---
name: paf
description: Operate, inspect, diagnose, and customize PAF mathematical-formalization swarms and their durable state. Use for PAF CLI commands, paf.toml configuration, corpus planning, stage or agent control, task retries or overrides, SQLite state inspection, scheduler debugging, source-dependency/build-freshness changes, and edits to a PAF checkout's state machinery.
---

# PAF

Use PAF's supported interfaces first, then descend into internals only as far as the request requires. Preserve run history and provenance unless the user explicitly asks to rewrite them.

## Start safely

1. Locate the project, config, executable, source checkout, and state directory. Do not assume `.paf/` itself is the active state directory; inferred corpora use `.paf/corpus-<hash>/`, while explicit config normally uses `swarm.state_dir`.
2. Read [references/commands.md](references/commands.md) for routine planning, running, status, agent control, selection, and configuration work.
3. Read [references/internals.md](references/internals.md) before changing persisted state, scheduler behavior, state schemas, task transitions, dependency graphs, request ledgers, or PAF source.
4. Inspect before mutating. Capture status/snapshot output and check whether a managed daemon owns the state.

Find likely installations and state without writing:

```bash
command -v paf || true
find .. -maxdepth 3 -type f -path '*/.venv/bin/paf' -print
find .paf -name state.sqlite3 -o -name state.json 2>/dev/null
python .agents/skills/paf/scripts/paf_state.py discover --project .
```

When PAF is in a sibling checkout, prefer its environment directly:

```bash
../paf/.venv/bin/paf plan --config paf.toml
../paf/.venv/bin/paf status --config paf.toml --json
```

Avoid `uv run --project ...` when the existing environment already has the executable and `uv` cannot write its cache.

## Choose the interface

- Use `paf plan`, `status`, `source-issues`, and `agent snapshot` for read-only inspection.
- Use `stage`, `pipeline`, or `corpus` with `--book`, `--chapter`, `--force`, and `--resume` for supported reruns.
- Use `agent pause|resume|unblock|stop|wait` for a live managed swarm. These commands go through the Unix control socket and update in-memory state correctly. `unblock` is global, not targeted.
- Use `scripts/paf_state.py` only for an offline, targeted task override that the CLI cannot express. It refuses live-state writes, validates core task invariants, uses a transaction, increments the database revision, records change rows, and creates a SQLite backup.
- Modify PAF source when the requested behavior is reusable policy rather than a one-off state correction. Add or update tests in the PAF checkout.

## Inspect and override offline task state

Pass the exact directory containing `state.sqlite3`:

```bash
python .agents/skills/paf/scripts/paf_state.py summary --state-dir .paf/corpus-0123456789
python .agents/skills/paf/scripts/paf_state.py tasks --state-dir .paf/corpus-0123456789 \
  --book algebra --stage prove --status blocked
python .agents/skills/paf/scripts/paf_state.py show --state-dir .paf/corpus-0123456789 \
  algebra/chapter-03:prove
python .agents/skills/paf/scripts/paf_state.py set-task --state-dir .paf/corpus-0123456789 \
  algebra/chapter-03:prove --status pending --detail 'manual retry after API repair' --dry-run
```

Remove `--dry-run` only after reviewing the diff. Stop and wait for a managed daemon before an exact-one override; pausing alone leaves an in-memory owner. The editor deliberately does not create fake run records, set tasks to `running`, rewrite request ledgers, or infer a proof digest. It refuses to reopen a blocked proof tied to an escalated upstream request because that transition also requires a ledger update. For those changes, use `StateStore` APIs or patch PAF itself after reading the internals reference.

## Verify every change

After configuration or source edits, run `paf plan` and the narrowest relevant PAF tests. After state edits:

1. Re-run `paf_state.py show` and `summary`.
2. Run `paf status ... --json` or `paf agent snapshot ...` against the same resolved project.
3. Start only the narrow requested selection, preferably with `--no-tui` while diagnosing.
4. Confirm that the selected task becomes runnable and that prerequisites were not falsely marked green.

Do not edit exported `state.json` and expect the live v2 store to change. In current PAF, normalized SQLite rows are authoritative; JSON is a legacy import or explicit export format.
