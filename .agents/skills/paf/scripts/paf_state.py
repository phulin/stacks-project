#!/usr/bin/env python3
"""Inspect and safely override task rows in an offline PAF v2 SQLite state store."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sqlite3
import sys
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

STATUSES = {"pending", "running", "succeeded", "failed", "blocked", "interrupted"}
STAGES = {"discover", "formalize", "review", "prove"}


def now() -> str:
    return datetime.now(UTC).isoformat()


def decode(value: bytes | str) -> dict[str, Any]:
    result = json.loads(value)
    if not isinstance(result, dict):
        raise TypeError("expected a JSON object payload")
    return result


def encode(value: dict[str, Any]) -> bytes:
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode()


def database_path(state_dir: Path) -> Path:
    path = state_dir.resolve() / "state.sqlite3"
    if not path.is_file():
        raise FileNotFoundError(f"PAF database not found: {path}")
    return path


def alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def live_owner(state_dir: Path) -> tuple[int, Path] | None:
    # A parent .paf directory can itself be a different state store. Only the
    # PID file beside this database establishes ownership of this store.
    path = state_dir / "daemon.pid"
    if not path.is_file():
        return None
    try:
        pid = int(path.read_text(encoding="utf-8").strip())
    except (OSError, ValueError):
        return None
    if alive(pid):
        return pid, path
    return None


def connect(path: Path, *, readonly: bool = True) -> sqlite3.Connection:
    if readonly:
        connection = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    else:
        connection = sqlite3.connect(path)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys=ON")
    return connection


def require_v2(connection: sqlite3.Connection) -> None:
    version = int(connection.execute("PRAGMA user_version").fetchone()[0])
    if version != 2:
        raise ValueError(f"unsupported PAF schema {version}; expected 2")


def task(connection: sqlite3.Connection, key: str) -> dict[str, Any]:
    row = connection.execute("SELECT payload FROM tasks WHERE task_key=?", (key,)).fetchone()
    if row is None:
        raise KeyError(f"unknown task key: {key}")
    return decode(row[0])


def global_state(connection: sqlite3.Connection) -> dict[str, Any]:
    row = connection.execute("SELECT payload FROM globals WHERE key='state'").fetchone()
    return decode(row[0]) if row is not None else {}


def related_requests(connection: sqlite3.Connection, unit: str) -> dict[str, list[dict[str, Any]]]:
    state = global_state(connection)
    result: dict[str, list[dict[str, Any]]] = {}
    identity_fields = {
        "chapter_id",
        "consumer_chapter_id",
        "owner_chapter_id",
        "requester_chapter_id",
        "review_chapter_id",
        "target_chapter_id",
    }
    for ledger_name in ("upstream_requests", "proof_review_requests", "fixup_requests"):
        ledger = state.get(ledger_name, {})
        if not isinstance(ledger, dict):
            continue
        matches = [
            value
            for value in ledger.values()
            if isinstance(value, dict)
            and any(value.get(field) == unit for field in identity_fields)
        ]
        if matches:
            result[ledger_name] = matches
    return result


def command_discover(args: argparse.Namespace) -> int:
    project = args.project.resolve()
    paths = sorted(project.glob(".paf/**/state.sqlite3"))
    if not paths:
        print("No PAF SQLite state stores found.")
        return 1
    for path in paths:
        try:
            with connect(path) as connection:
                revision = connection.execute(
                    "SELECT revision FROM meta WHERE singleton=1"
                ).fetchone()
                counts = dict(
                    connection.execute("SELECT status, count(*) FROM tasks GROUP BY status")
                )
            print(
                json.dumps(
                    {
                        "state_dir": str(path.parent),
                        "revision": int(revision[0]) if revision else 0,
                        "tasks": counts,
                    },
                    sort_keys=True,
                )
            )
        except (sqlite3.Error, ValueError) as error:
            print(json.dumps({"state_dir": str(path.parent), "error": str(error)}))
    return 0


def command_summary(args: argparse.Namespace) -> int:
    path = database_path(args.state_dir)
    with connect(path) as connection:
        require_v2(connection)
        meta = connection.execute(
            "SELECT schema_version, revision, created_at, updated_at, config_fingerprint "
            "FROM meta WHERE singleton=1"
        ).fetchone()
        counts = dict(connection.execute("SELECT status, count(*) FROM tasks GROUP BY status"))
        stages = {
            stage: dict(
                connection.execute(
                    "SELECT status, count(*) FROM tasks WHERE stage=? GROUP BY status", (stage,)
                )
            )
            for stage in sorted(STAGES)
        }
        documents = int(connection.execute("SELECT count(*) FROM documents").fetchone()[0])
        work_units = int(connection.execute("SELECT count(*) FROM work_units").fetchone()[0])
        runs = int(connection.execute("SELECT count(*) FROM runs").fetchone()[0])
    result = {
        "database": str(path),
        "schema_version": int(meta["schema_version"]),
        "revision": int(meta["revision"]),
        "created_at": meta["created_at"],
        "updated_at": meta["updated_at"],
        "config_fingerprint": meta["config_fingerprint"],
        "documents": documents,
        "work_units": work_units,
        "runs": runs,
        "tasks": counts,
        "by_stage": stages,
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


def command_tasks(args: argparse.Namespace) -> int:
    path = database_path(args.state_dir)
    clauses: list[str] = []
    values: list[Any] = []
    for column, value in (("stage", args.stage), ("status", args.status)):
        if value:
            clauses.append(f"{column}=?")
            values.append(value)
    if args.book:
        clauses.append("work_unit_id LIKE ?")
        values.append(f"{args.book}/%")
    query = (
        "SELECT task_key, status, queued, rounds, detail, source_digest, updated_at, "
        "latest_run_id, run_count FROM tasks"
    )
    if clauses:
        query += " WHERE " + " AND ".join(clauses)
    query += " ORDER BY task_key"
    if args.limit:
        query += " LIMIT ?"
        values.append(args.limit)
    with connect(path) as connection:
        require_v2(connection)
        rows = [dict(row) for row in connection.execute(query, values)]
    print(json.dumps(rows, indent=2, sort_keys=True))
    return 0


def command_show(args: argparse.Namespace) -> int:
    path = database_path(args.state_dir)
    with connect(path) as connection:
        require_v2(connection)
        value = task(connection, args.task_key)
        unit = str(value.get("work_unit_id", value.get("chapter_id", "")))
        requests = related_requests(connection, unit)
        runs = [
            decode(row[0])
            for row in connection.execute(
                "SELECT summary FROM runs WHERE task_key=? ORDER BY started_at, id", (args.task_key,)
            )
        ]
    value["runs"] = runs
    value["related_requests"] = requests
    print(json.dumps(value, indent=2, sort_keys=True))
    return 0


def apply_task_change(
    connection: sqlite3.Connection, key: str, args: argparse.Namespace, changed_at: str
) -> tuple[dict[str, Any], dict[str, Any]]:
    before = task(connection, key)
    after = dict(before)
    stage = str(after.get("stage", key.rsplit(":", 1)[-1]))
    if stage not in STAGES:
        raise ValueError(f"task has unknown stage: {stage}")
    if args.status == "running":
        raise ValueError("refusing to synthesize a running task without an active run")
    if args.status:
        after["status"] = args.status
        after["phase"] = "idle"
        after["queued"] = False
    if args.detail is not None:
        after["detail"] = args.detail
    if args.rounds is not None:
        if args.rounds < 0:
            raise ValueError("rounds must be nonnegative")
        after["rounds"] = args.rounds
    if args.queued is not None:
        after["queued"] = args.queued
    if after.get("queued") and after.get("status") != "pending":
        raise ValueError("queued=true is valid only for pending tasks")
    if args.source_digest is not None and stage != "prove":
        raise ValueError("source_digest is valid only for prove tasks")
    if stage == "prove":
        if args.source_digest is not None:
            after["source_digest"] = args.source_digest
        if after.get("status") != "succeeded":
            after["source_digest"] = None
        if after.get("status") == "succeeded" and not after.get("source_digest"):
            raise ValueError("a succeeded prove task requires --source-digest or an existing digest")
        if before.get("status") != "pending" and after.get("status") == "pending":
            unit = str(after.get("work_unit_id", after.get("chapter_id", "")))
            upstream = related_requests(connection, unit).get("upstream_requests", [])
            escalated = [
                value
                for value in upstream
                if value.get("consumer_chapter_id") == unit
                and value.get("status") == "escalated"
            ]
            if escalated:
                ids = ", ".join(str(value.get("id", "?")) for value in escalated)
                raise ValueError(
                    "proof retry has escalated upstream request(s) "
                    f"{ids}; reopen them through StateStore with the task"
                )
    if stage == "formalize" and after.get("status") != "succeeded":
        unit = str(after.get("work_unit_id", after.get("chapter_id", "")))
        for later_stage in ("review", "prove"):
            later = task(connection, f"{unit}:{later_stage}")
            if int(later.get("rounds", 0)) > 0 or later.get("status") in {
                "running",
                "succeeded",
            }:
                raise ValueError(
                    f"cannot regress formalize after {later_stage} started; PAF will repair it"
                )
    after["updated_at"] = changed_at
    return before, after


def write_task(connection: sqlite3.Connection, key: str, value: dict[str, Any]) -> None:
    connection.execute(
        "UPDATE tasks SET status=?, queued=?, detail=?, rounds=?, source_digest=?, "
        "updated_at=?, latest_run_id=?, run_count=?, payload=? WHERE task_key=?",
        (
            str(value.get("status", "pending")),
            int(bool(value.get("queued", False))),
            str(value.get("detail", "")),
            int(value.get("rounds", 0)),
            value.get("source_digest"),
            str(value.get("updated_at", "")),
            value.get("latest_run_id"),
            int(value.get("run_count", 0)),
            encode(value),
            key,
        ),
    )


def promote_formalize_if_needed(
    connection: sqlite3.Connection, value: dict[str, Any], changed_at: str
) -> tuple[str, dict[str, Any], dict[str, Any]] | None:
    if value.get("stage") not in {"review", "prove"} or value.get("status") != "succeeded":
        return None
    unit = str(value.get("work_unit_id", value.get("chapter_id", "")))
    key = f"{unit}:formalize"
    before = task(connection, key)
    if before.get("status") == "succeeded":
        return None
    after = dict(before)
    after.update(
        status="succeeded",
        phase="idle",
        queued=False,
        detail="formalization completed before review",
        updated_at=changed_at,
    )
    return key, before, after


def backup_database(path: Path) -> Path:
    stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    candidate = path.with_name(f"{path.name}.bak-{stamp}")
    suffix = 1
    while candidate.exists():
        candidate = path.with_name(f"{path.name}.bak-{stamp}-{suffix}")
        suffix += 1
    with sqlite3.connect(path) as source, sqlite3.connect(candidate) as target:
        source.backup(target)
    shutil.copymode(path, candidate)
    return candidate


def command_set_task(args: argparse.Namespace) -> int:
    if all(
        item is None
        for item in (args.status, args.detail, args.rounds, args.queued, args.source_digest)
    ):
        raise ValueError("no changes requested")
    state_dir = args.state_dir.resolve()
    path = database_path(state_dir)
    owner = live_owner(state_dir)
    if owner is not None:
        pid, pid_path = owner
        raise RuntimeError(
            f"refusing to edit state owned by live PID {pid} ({pid_path}); stop the daemon first"
        )
    changed_at = now()
    with connect(path) as connection:
        require_v2(connection)
        before, after = apply_task_change(connection, args.task_key, args, changed_at)
        promotion = promote_formalize_if_needed(connection, after, changed_at)
    preview: dict[str, Any] = {args.task_key: {"before": before, "after": after}}
    if promotion:
        key, old, new = promotion
        preview[key] = {"before": old, "after": new}
    if args.dry_run:
        print(json.dumps({"dry_run": True, "changes": preview}, indent=2, sort_keys=True))
        return 0
    backup = backup_database(path)
    with connect(path, readonly=False) as connection:
        require_v2(connection)
        connection.execute("BEGIN IMMEDIATE")
        owner = live_owner(state_dir)
        if owner is not None:
            connection.rollback()
            pid, pid_path = owner
            raise RuntimeError(
                f"state became owned by live PID {pid} ({pid_path}); no changes written"
            )
        # Recompute every invariant after acquiring the write lock. This catches
        # both task changes and newly escalated request-ledger entries.
        locked_before, locked_after = apply_task_change(
            connection, args.task_key, args, changed_at
        )
        locked_promotion = promote_formalize_if_needed(connection, locked_after, changed_at)
        if locked_before != before or locked_after != after or locked_promotion != promotion:
            connection.rollback()
            raise RuntimeError("task or related state changed after preview; retry the command")
        write_task(connection, args.task_key, locked_after)
        changed = [(args.task_key, locked_after)]
        if locked_promotion:
            key, _, new = locked_promotion
            write_task(connection, key, new)
            changed.append((key, new))
        row = connection.execute("SELECT revision FROM meta WHERE singleton=1").fetchone()
        revision = int(row[0]) + 1
        connection.execute(
            "UPDATE meta SET revision=?, updated_at=? WHERE singleton=1", (revision, changed_at)
        )
        global_row = connection.execute(
            "SELECT payload FROM globals WHERE key='state'"
        ).fetchone()
        if global_row is not None:
            global_value = decode(global_row[0])
            global_value["updated_at"] = changed_at
            connection.execute(
                "UPDATE globals SET revision=?, payload=? WHERE key='state'",
                (revision, encode(global_value)),
            )
            connection.execute(
                "INSERT OR IGNORE INTO changes VALUES(?, 'global', 'state')", (revision,)
            )
        for key, value in changed:
            unit = str(value.get("work_unit_id", value.get("chapter_id", "")))
            connection.execute(
                "INSERT OR IGNORE INTO changes VALUES(?, 'task', ?)", (revision, key)
            )
            connection.execute(
                "INSERT OR IGNORE INTO changes VALUES(?, 'work_unit', ?)", (revision, unit)
            )
        connection.commit()
    print(
        json.dumps(
            {"backup": str(backup), "revision": revision, "changes": preview},
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(description=__doc__)
    commands = root.add_subparsers(dest="command", required=True)
    discover = commands.add_parser("discover", help="list project-local PAF state stores")
    discover.add_argument("--project", type=Path, default=Path.cwd())
    discover.set_defaults(func=command_discover)
    for name, help_text, func in (
        ("summary", "show database metadata and task counts", command_summary),
        ("tasks", "list filtered task projections", command_tasks),
        ("show", "show one task and compact run summaries", command_show),
        ("set-task", "transactionally override one offline task", command_set_task),
    ):
        command = commands.add_parser(name, help=help_text)
        command.add_argument("--state-dir", type=Path, required=True)
        command.set_defaults(func=func)
    tasks = commands.choices["tasks"]
    tasks.add_argument("--book")
    tasks.add_argument("--stage", choices=sorted(STAGES))
    tasks.add_argument("--status", choices=sorted(STATUSES))
    tasks.add_argument("--limit", type=int, default=0)
    show = commands.choices["show"]
    show.add_argument("task_key")
    edit = commands.choices["set-task"]
    edit.add_argument("task_key")
    edit.add_argument("--status", choices=sorted(STATUSES))
    edit.add_argument("--detail")
    edit.add_argument("--rounds", type=int)
    queue = edit.add_mutually_exclusive_group()
    queue.add_argument("--queued", dest="queued", action="store_true")
    queue.add_argument("--not-queued", dest="queued", action="store_false")
    edit.set_defaults(queued=None)
    edit.add_argument("--source-digest")
    edit.add_argument("--dry-run", action="store_true")
    return root


def main() -> int:
    try:
        args = parser().parse_args()
        return int(args.func(args))
    except (FileNotFoundError, KeyError, RuntimeError, TypeError, ValueError, sqlite3.Error) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
