# PAF state and scheduler internals

## Contents

- Architecture and source map
- Durable state layout
- SQLite schema and write path
- Task lifecycle invariants
- Scheduling and freshness
- Durable request ledgers
- Safe customization patterns
- Source-change checklist

## Architecture and source map

The current checkout is PAF 0.7.x. Verify the installed version before relying on these details.

- `src/paf/cli.py`: argparse surface, project/config resolution, selectors, foreground and managed commands.
- `src/paf/project.py`: project-root, config, source, target, and state path binding.
- `src/paf/config.py`: TOML parsing, source adapters, inferred corpus IDs, work-unit and target construction.
- `src/paf/models.py`: `Stage`, immutable config, document/work-unit, source span, and backend models.
- `src/paf/state.py`: in-memory records, lifecycle invariants, request ledgers, snapshots, change bus, and high-level mutations.
- `src/paf/state_db.py`: SQLite schema/migrations, normalized projections, revision log, writer thread, snapshots, and legacy import.
- `src/paf/scheduler.py`: readiness, dependency/freshness checks, worker attempts, coordinator builds, retries, review/proof convergence.
- `src/paf/control.py`: managed daemon ownership and Unix-socket control protocol.
- `src/paf/corpus.py`: corpus schedules and weighted critical-path ordering.
- `src/paf/codex.py`, `adapters.py`, `backends.py`, `isolation.py`, `lean_mcp.py`: worker process, source/target abstraction, isolation, and Lean tooling.
- `src/paf/activity.py`: bounded live activity derived from JSONL logs.
- `src/paf/web.py`, `tui.py`, Rust `src/`: read models and user interfaces.

Read the corresponding tests before changing behavior: `tests/test_workflow.py`, `test_scheduler.py`, `test_control.py`, `test_cli.py`, `test_config.py`, `test_corpus.py`, and `test_web.py`.

## Durable state layout

Within the resolved state directory:

```text
state.sqlite3                 authoritative normalized state
state.sqlite3-wal/-shm        SQLite WAL sidecars; never copy only the main file live
state.json                    legacy import or explicitly exported snapshot
source-issues.json            legacy ledger only
logs/<run>.jsonl              raw worker events
logs/<run>.prompt.md          composed prompt
logs/<run>.activity.json      bounded activity projection
agent-report-<role>.schema.json
control.sock                  live managed control endpoint
daemon.pid                    managed owner PID
daemon.log                    detached process output
daemon-result.json            terminal managed result
```

`StateStore.load_or_create()` initializes/migrates SQLite, loads global/task/run/issue rows, reconciles configured work units, creates missing stage tasks, recovers `running` runs/tasks as `interrupted`, clears transient queues and active coordinator builds, normalizes request ledgers, then persists the reconciliation. Merely loading a `StateStore` is therefore a mutation. Use `StateDatabase` or the bundled script for read-only/offline inspection.

## SQLite schema and write path

Schema v2 retains the old `checkpoint` table only for migration. Authoritative tables are:

- `meta`: singleton schema version, monotonic revision, timestamps, config fingerprint.
- `documents`, `work_units`: static normalized rows plus JSON `payload` blobs.
- `tasks`: indexed task columns plus a JSON `payload`; unique `(work_unit_id, stage)`.
- `runs`: indexed run summary columns, a compact `summary`, and full `payload`.
- `globals`: the non-task state snapshot under key `state`.
- `source_issues`: normalized issue payloads.
- `changes`: retained `(revision, entity_type, entity_id)` notifications for incremental views.

Every task update must keep its indexed columns and JSON payload identical. At minimum synchronize `status`, `queued`, `detail`, `rounds`, `source_digest`, `updated_at`, `latest_run_id`, and `run_count`. Advance `meta.revision` and `meta.updated_at`, and add appropriate `changes` rows. A state writer normally does all of this transactionally.

`StateStore` marks dirty entities and sends immutable `DatabaseWrite` deltas to a single `StateWriter` thread. Writes update normalized rows, increment the revision, and publish a `ChangeSet` in memory. Direct database edits while a daemon is running are unsafe: its in-memory store can overwrite them, its UI change bus will miss them, and lifecycle invariants will not execute.

Run payloads hold reports, validation, isolation, usage, logs, PIDs, Codex thread IDs, request IDs, and provenance. Task rows only cache run count/latest ID. Do not invent, delete, or reassign runs to make a status look consistent unless provenance rewriting is explicitly required.

## Task lifecycle invariants

Statuses are `pending`, `running`, `succeeded`, `failed`, `blocked`, and `interrupted`. Phases are `idle`, `agent`, and `postprocess`.

- Only a pending task may have `queued=true`; queued means runnable but awaiting capacity.
- A non-running task should have `phase=idle`. `running` is coordinator-owned and must correspond to a real active run.
- `rounds` counts started main attempts. Resetting status normally retains rounds and all history.
- A proof task has `source_digest` only when succeeded. It binds proof success to exact validated chapter sources.
- Setting review/prove to running or succeeded implicitly promotes formalize to succeeded if needed.
- PAF refuses to regress formalize once review/proof has rounds or is running/succeeded; loading also repairs this condition.
- `unblock()` changes blocked tasks to pending, clears queue/phase, clears proof digests, and reopens affected escalated upstream requests.
- Restart reconciliation converts orphaned running tasks/runs to interrupted. `--resume` later changes interrupted tasks to pending while retaining session history.
- A forced run bypasses the successful-task skip but does not first erase success or history.

Supported `StateStore` mutation methods include `set_task(s)`, `set_task_phase`, `unblock`, `requeue_interrupted`, `start_run`, `update_run`, `finish_run`, coordinator-build methods, and enqueue/finish/reopen methods for request ledgers. Use these inside PAF when changing behavior; they encode more invariants than raw SQL.

## Scheduling and freshness

There are four stage tasks per work unit:

1. `discover` persists direct source dependencies and source-input digests.
2. `formalize` becomes ready after its own discovery and successful formalization of discovered prerequisites.
3. `review` first becomes ready after clean own formalization and dependency reviews; targeted later reviews can bypass the initial dependency barrier.
4. `prove` requires successful review and a clean formalize/build record. Its success digest must match the clean record.

Three related facts must not be conflated:

- Task status records workflow completion.
- `source_dependency_tree` records discovery nodes, dependency edges, and source digests.
- `formalize_graph` records clean/dirty build freshness, build generation, and source digests.

Changing only a task from failed to succeeded does not create a clean build record. Changing only `formalize_graph` does not establish review/proof completion. Scheduler readiness reads all of them.

The coordinator coalesces pending build requests, prioritizes statement-critical work over proof certification, routes failed diagnostics to owners/import descendants, and stores clean freshness only after successful builds. Review edits invalidate affected import closures; proof-body edits validate the own chapter without proactively invalidating downstream chapters.

## Durable request ledgers

Global state contains three cross-attempt ledgers:

- `upstream_requests`: a proof consumer asks an earlier owner for a missing interface. Statuses are `requested`, `answered`, `closed`, and `escalated`. Repair/retry run IDs and exact answers connect the lifecycle.
- `proof_review_requests`: proof findings reopen review/statement work and remain until review resolves them.
- `fixup_requests`: compatibility/post-review repair requests; current startup migration moves legacy uses toward review.

These structures have relationships to task status and run `request_ids`. Avoid generic JSON patching. Use `enqueue_upstream_request`, `record_upstream_answers`, `finish_upstream_requests`, `reopen_escalated_upstream_requests`, and corresponding proof-review/fixup methods, or add a purpose-built StateStore method with tests.

## Safe customization patterns

### Retry one offline task

Use the bundled editor to set it to pending with an explanatory detail. Keep history/rounds. For proof, the editor clears the success digest. If the proof is linked to an escalated upstream request, the editor refuses: call the matching `StateStore.reopen_escalated_upstream_requests()` behavior through a purpose-built targeted operation. Then run the narrow stage selection.

### Mark externally verified work successful

Prefer adding a supported PAF command or StateStore method. A proof success requires the actual source digest and clean build freshness; a naked status override will be reconsidered by scheduling. Record why provenance is absent.

### Reopen review after an API/statement finding

Use the proof-review request machinery so the finding, requester, affected chapter, and lifecycle survive restarts. Resetting the review status alone loses the reason and downstream coordination.

### Change dependencies

Fix the source discovery adapter, manifest, dependency document, or discovery output logic, then rerun discovery. Direct edits to `source_dependency_tree` are temporary and must update digests/graph structure consistently.

### Change build freshness

Patch scheduler/build policy and let a real coordinator build populate `formalize_graph`. Never declare an arbitrary source digest clean solely to unblock proof.

### Add a custom administrative operation

Implement one high-level `StateStore` method, expose it through `ControlServer` for live use and CLI for offline/managed routing, update protocol/version handling if the wire shape changes, and cover in-memory state, SQLite persistence, restart behavior, and CLI output in tests.

## Source-change checklist

1. Read repository `AGENTS.md` and the narrow source/tests.
2. Identify whether the change belongs in config resolution, state transition, scheduling policy, control, or display projection.
3. Preserve the distinction among task status, run provenance, dependency discovery, and build freshness.
4. Use `StateStore` mutation methods and dirty tracking; do not update dataclass fields without `_mark_dirty()` plus persistence.
5. Keep SQLite indexed columns, payloads, revisions, and change rows synchronized.
6. Test restart recovery and both live and offline control paths when relevant.
7. Run targeted pytest files, then the PAF suite and lint/type checks required by that checkout.
