# PAF commands and configuration

## Contents

- Resolve the project and state
- Inspect without launching workers
- Run work
- Control a managed run
- Select work units
- Configure PAF
- Diagnose common failures

## Resolve the project and state

PAF discovers `paf.toml` from a source target or project path. An explicit config uses `[swarm].state_dir` (default `.paf`). A zero-config inferred corpus hashes the sorted repository-relative source paths, plus an explicit target when present, into `.paf/corpus-<10 hex>`.

Do not choose the newest-looking database blindly. Ask PAF to resolve the same inputs the run uses:

```bash
paf plan --config paf.toml
paf plan books/
paf status --config paf.toml --json
paf agent status --config paf.toml
```

The `plan` display includes the resolved repository, state path, concurrency, model, reasoning effort, isolation, documents, work units, target scopes, and stage settings. Use the same invocation shape for subsequent commands.

## Inspect without launching workers

```bash
paf plan TARGET_OR_DIRECTORY
paf status TARGET_OR_DIRECTORY
paf status --config paf.toml --json
paf source-issues --config paf.toml --json
paf agent snapshot --config paf.toml
paf agent snapshot --config paf.toml --output /tmp/paf-snapshot.json
paf agent inspect --config paf.toml --chapter BOOK/CHAPTER-NN --json
paf agent inspect --config paf.toml --run RUN_ID --follow
```

`status --json` reads the complete durable snapshot. On large corpora it can be expensive because run payloads are materialized. `agent status` is compact; `agent snapshot` talks to a live control server when available and otherwise reads durable state.

The source-issue ledger is evidence reported by workers. It is independent of whether a task is pending or green.

## Run work

```bash
paf scaffold --config paf.toml
paf stage discover --config paf.toml --book algebra --chapter 3
paf stage formalize --config paf.toml --book algebra --chapter algebra/chapter-03
paf stage review --config paf.toml --book algebra --chapter 3 --force
paf stage prove --config paf.toml --book algebra --chapter 3 --resume
paf pipeline --config paf.toml --no-tui
paf corpus books/ --max-agents 24 --no-tui
```

- `--force` bypasses the normal skip of a persisted successful task. It does not erase history.
- `--resume` requeues interrupted work and tries saved Codex thread IDs before falling back to fresh workers.
- `--no-tui` keeps execution in the foreground with logs suitable for automation.
- `--isolation auto|fuse-overlay|shared`, `--model`, `--reasoning-effort`, `--max-agents`, and `--discover-max-agents` override configured values.
- `scaffold` creates deterministic target directories only; it launches no agents.

## Control a managed run

```bash
paf agent start --config paf.toml --stage pipeline
paf agent status --config paf.toml
paf agent pause --config paf.toml
paf agent resume --config paf.toml
paf agent unblock --config paf.toml
paf agent stop --config paf.toml
paf agent wait --config paf.toml
```

`pause` is cooperative: running attempts continue, but scheduling stops before new attempts. `unblock` resets every blocked task to pending, clears proof digests for affected proof tasks, and reopens relevant escalated upstream requests. `stop` cancels the pipeline and asks PAF to integrate interrupted workspace changes.

There is no supported targeted live `unblock` in PAF 0.7.x. To retry exactly one blocked task, stop and wait for the daemon, inspect the exact task plus its request ledgers, then use the offline editor. If a blocked proof has an escalated upstream request, add a purpose-built `StateStore` operation or use the global unblock command when resetting all blocked work is acceptable; a task-row-only edit is incomplete.

The control protocol is newline-delimited JSON over `<state_dir>/control.sock`. Current commands are `status`, `snapshot`, `pause`, `resume`, `unblock`, `stop`, `wait`, and dashboard `subscribe`. Prefer the CLI wrapper over hand-written socket traffic.

## Select work units

`--book` selects a document ID and may repeat. `--chapter` may be a full work-unit ID such as `algebra/chapter-03` or a decimal ordinal such as `3`, and may repeat. A numeric selector applies within every selected book and can therefore match more than one work unit.

Task keys are `<work-unit-id>:<stage>`, for example `algebra/chapter-03:prove`. Stages are `discover`, `formalize`, `review`, and `prove`.

## Configure PAF

The repository's minimal LaTeX corpus configuration is representative:

```toml
[swarm]
repo = "."
sandbox = "workspace-write"
bypass_approvals_and_sandbox = false

[sources]
roots = ["books"]

[sources.manifest]
path = "chapters.tex"
pattern = '\\hyperref\[(?P<name>.+?)-section-phantom\]'
template = "books/{name}.tex"
allow_missing = true
```

Important `[swarm]` fields include `state_dir`, `max_agents`, `model`, `reasoning_effort`, `sandbox`, `approve_for_me`, `bypass_approvals_and_sandbox`, `isolation`, `agent_timeout_seconds`, validation/capacity retry settings, `lean_project`, and Lean MCP timeout settings. Stage tables select prompt, model, effort, rounds, and optional per-stage agent limits. Backend/target configuration maps source units to Lean paths, modules, build commands, and exclusive scopes.

Before adding a field, inspect `paf.example.toml`, `src/paf/config.py`, and `src/paf/models.py` in the installed PAF version. Config is evolving and unknown assumptions can redirect state or output paths.

## Diagnose common failures

- **Wrong or empty status:** compare the exact target/config invocation with the original run; several databases may coexist.
- **`uv` cache is read-only:** invoke the environment's installed `paf` binary directly.
- **Managed command times out:** inspect `daemon.pid`, `control.sock`, `daemon.log`, and `daemon-result.json`; verify the PID is alive before treating files as current.
- **A successful task reruns:** check `--force`, task key selection, config fingerprint/static work-unit changes, discovery source digests, and proof/build freshness digests.
- **A task remains blocked:** inspect its detail, latest run report, upstream requests, proof-review requests, and prerequisite task states. Use global `agent unblock` only when resetting all blocked work is intended.
- **A formalization is unexpectedly green:** PAF enforces formalization success once review or proof has started; inspect history before attempting to regress it.
- **Unknown Lean module/build failure:** compare the resolved backend mapping, generated module/path, actual files, and `build_command`; task-state changes cannot repair a bad target mapping.
