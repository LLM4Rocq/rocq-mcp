# rocq-mcp response reference — optional fields, caps, size controls

Field-level reference for the optional/verbose parts of tool responses.
The always-present contract is in each tool's description; this guide
covers what shows up conditionally and how output size is bounded.

## Envelope fields common to many tools

- `clamped_timeout: <cap>` — the per-call `timeout=` exceeded
  `ROCQ_QUERY_TIMEOUT_CAP` (default 300) and ran with the cap instead.
- `workspace_warning: str` — the resolved workspace has no
  `_RocqProject` / `_CoqProject` / `dune-project` marker AND the call
  passed explicit `workspace=` or `file=`; load paths may be wrong.
  Source-string tools without those hints stay quiet.
- `stale_warning: str` — the session's `.v` file changed on disk after
  `rocq_start`; the proof state no longer matches the file.
- `pet_restarted: true` — pet was killed during this call (timeout /
  crash / memory breach); held state_ids are gone. See the failures
  guide playbook.
- `degraded: ["<field>:<code>", ...]` — best-effort enrichment steps
  that failed this call; treat the named fields as missing.
  `degraded_detail` appears only when the server runs with
  `ROCQ_DEBUG_ENRICHMENT=1`.

## rocq_check response

- `state_id` / `from_state_id` — the new state and its parent. Pass
  `state_id` as the next call's `from_state`.
- `goals` — representation controlled by `goals_format`:
  - `"pretty"` (default): the classic string, capped at 8,000 chars and
    10 goals shown.
  - `"structured"`: `[{hyps: [{names, type, body?}], conclusion}]` —
    pytanque's structured hypotheses; per-string cap 2,000 chars, 10
    goals + `{omitted_goals: N}` marker.
  - `"names_only"`: `[{hyp_names, conclusion}]` — the token-lean variant.
  - `"diff"`: the `goals` key is replaced by `goals_diff` — either
    `{unchanged: true, count}` or `{before_count, after_count,
    added: [goal texts new since the from_state parent],
    removed_count}`. Costs one extra pet round-trip; degrades to
    pretty `goals` (with a `degraded` note) if the parent lookup fails.
  - `"none"`: goals omitted entirely (commit-only calls).
- `feedback: [[command, output], ...]` — only when commands produce
  visible output (`Print`, `Check`, `vm_compute`...). Truncated at 50K
  chars per step, 200K total per call, with a
  `"... (truncated, N total chars)"` marker.
- `focus_depth` — open `{...}`/bullet focus frames above the goal (0 at
  top level). Omitted when goal state is unavailable.
- `shelved_goals` / `given_up_goals` — counts, present when non-zero.
- On `proof_finished: true` — `proof_tactics` (root-to-leaf tactic
  list), and when the statement is recoverable also `proof_script` (a
  ready-to-paste declaration + Proof. + tactics + Qed.; preamble-mode
  sessions prepend their imports), `statement`, and `statement_source`
  (`"file"` | `"session_commands"` | `"unrecoverable"`). The
  `proof_tactics_status` family now fires only if the finished state
  itself was evicted (failures guide).
- On failure — `last_valid_state_id`, `failed_command` (failures guide).

## rocq_step_multi response

- `results: [entry, ...]` in input order. First tactic reaching a proof
  state: `{tactic, success: true, goals, goals_count, proof_finished,
  time_ms, focus_depth?, shelved_goals?, given_up_goals?, feedback?}`.
  Later tactics reaching the SAME state are deduplicated: `{tactic,
  success: true, proof_finished, goals_count, same_outcome_as: <index
  into results>, time_ms, feedback?}` — look up the referenced entry
  for the goals. Failed entry: `{tactic, success: false, reason:
  "tactic_failed", error, time_ms}`.
- `summary: {tried, succeeded, finished: [tactics], distinct_outcomes,
  best?: {tactic, goals_count}}` — `best` = fewest goals remaining,
  proof-finishing tactics first.
- `timeouts=[...]` gives each tactic its own budget (batch wall clock =
  the sum); `preset="auto"` appends the automation battery (deduped,
  capped at 20; `preset_truncated: true` when cut).
- `distinct_outcomes` — count of unique successful proof states reached.
- Per-entry `goals` respects `goals_format` (pretty/structured/
  names_only); pretty capped at 8,000 chars. Per-entry `feedback` capped
  at 50K chars with a 200K total cap across the batch.
- Max 20 tactics per call; the per-tactic time budget is
  `timeout / len(tactics)` for Timeout-eligible tactics.
- `from_state_id` echoes the base state.

## rocq_query / rocq_toc / rocq_notations output

- Single `output: str`, capped at 8,000 chars with a truncation marker.
- `rocq_query(max_results=N)` truncates the result list BEFORE the char
  cap and appends a "N more results" line — use it for broad `Search`
  patterns.
- `include_warnings=False` drops LSP Warning-severity feedback entries
  (7 tools accept this; keeps output compact on warning-heavy files).
- `rocq_toc` returns the outline as a single `output` string under
  the same 8,000-char cap — no per-name cap or overflow fields.

## rocq_search response

- `hits: [{name, type?} | {raw}]` — one entry per Search hit, parsed as
  `name: type`; unparseable messages kept as `{raw}`. `include_types=false`
  drops the types. With multiple `patterns`, each hit carries
  `matched_patterns` (multi-pattern hits are the strongest premise
  candidates).
- `total` / `offset` / `truncated` — pagination over the merged,
  deduplicated hit list (re-run with a higher `offset` for the next page).
- `query` — the exact Search command(s) executed (string, or list in
  fan-out mode).
- A pattern Coq rejects fails with `reason: "query_rejected"` and the
  offending command in the message.

## rocq_goal response

- `goals` (per `goals_format`) or `goals_diff` (when `diff_from` given),
  plus `goals_count`, `proof_finished`, `focus_depth?`,
  `shelved_goals?`, `given_up_goals?`.
- `stateless: true` — no state was registered; the LRU table is untouched.

## rocq_assumptions response

- `assumptions: list[str]` of `"name : type"` pairs. Empty list = the
  theorem is closed under the global context. `Print Assumptions` does
  NOT distinguish `Admitted` from `Axiom`/`Parameter`/`Conjecture` — they
  all appear here.
- `raw_output: str` — opt-in via `include_raw=true` (redundant with the
  parsed list on success; opaque-proof loader notices are stripped).
  On a parse failure it is always present — there it IS the payload.

## rocq_compile / rocq_compile_file failure fields

- `error` — coqc's diagnostic, tail-truncated at 4,000 chars (the tail
  carries the actual error). Success `output` is capped at 2,000 chars.
- `error_positions: [{line, character}, ...]` — coqc's parsed positions
  (1-based lines from coqc are normalized; see hint text for usage).
- `hint` — the suggested next call, rewritten to
  `rocq_check(from_state=...)` when state capture succeeded.
- `state_capture_status` + captured-state fields — failures guide.
- `errors: list` — multi-error walk (rocq_compile_file only; failures
  guide). Tunables: `ROCQ_COMPILE_MULTI_ERROR_CAP` (default 20; 0
  disables), `ROCQ_COMPILE_MULTI_ERROR_TIMEOUT` (default 5.0s per chunk).

## rocq_compile_file options

- `keep_vo=True` — keep `.vo`/`.vok`/`.vos` after the compile (diagnostic
  artifacts are still cleaned). Use when a sibling file will
  `Require Import` the result. **Footgun:** `keep_vo=True` +
  `mode="vos"` produces only a `.vos`; a downstream `mode="full"` import
  then fails with "Unable to locate library ... (.vos file)" — use
  `mode="full"` when the consumer expects a `.vo`.
- `mode="vos"` — statements-only pre-pass (`coqc -vos`): skips proof
  bodies ENTIRELY (does not execute them). Catches missing imports,
  statement type errors, and notation conflicts in seconds; accepts any
  proof body, so always finish with `mode="full"`.
- `timing=True` — run coqc with `-time`; adds
  `timing: {total_sentences, top_slowest (≤5, by duration),
  last_completed}`. On timeout, `last_completed` is woven into the error
  ("Last completed sentence: line 221 [Theorem.foo] (15.3s)"); on
  success it is simply the file's final sentence.
- `vo_rebuild_warning: str` — this compile rewrote `.vo` artifacts in a
  workspace that has active interactive sessions; those sessions should
  `rocq_start` again to refresh held dependency state. Quiet when no
  `.vo` changed or no session lives in the workspace. `keep_vo=True`
  makes it more likely to fire on subsequent compiles (the persisted
  `.vo` shows a fresh mtime delta).

## Workspace auto-detection

File-accepting tools called without `workspace=` walk up from the file's
directory looking for `_RocqProject` / `_CoqProject` / `dune-project` and
use the innermost match; fallback is the `ROCQ_WORKSPACE` env var
(default cwd). Pass `workspace=` explicitly for monorepos with nested
project files. For dune projects the server derives load paths via
`dune coq top` per theory and writes an auto-generated `_RocqProject`
(gitignore it).

## rocq_diag / rocq_health shapes

`rocq_diag`: `server_version`, `pet {pid, uptime_seconds, restarts,
generation}`, `memory {pet_rss_mb, peak_pet_rss_mb, max_rss_mb_threshold,
sample_status}`, `load_average {1m,5m,15m}|null`, `lock {wait_ms_last,
wait_ms_max, contended_total}`, `enrichment_failures {code: count}`,
`live_states` (≤50 newest; `live_states_total` for the uncapped count),
`recent_errors` (last 20: `{tool, message, reason, ago_seconds}`).

`rocq_health`: `ok` (coqc resolves), `server_version`, `switch`,
`switch_prefix`, `switch_is_local`, `switch_source`
(`opam_env`|`binary_path`|`unknown`), `toolchain {coqc {path, version},
pet {path, version, pytanque_importable}}`, `pet {running, pid}`,
`warnings`. rocq_health = toolchain health; rocq_diag = runtime health.

## Size-control parameters at a glance

| Control | Tools | Effect |
|---|---|---|
| `goals_format` | check (5 modes), start, step_multi, goal (3 modes) | Goals representation: `pretty` / `structured` / `names_only`, plus check-only `diff` / `none` |
| `include_raw` | rocq_assumptions | Opt back into the verbatim `raw_output` |
| `max_results` | rocq_query | Cap Search hits before char truncation |
| `include_warnings=False` | compile, compile_file, verify, query, search, check, step_multi | Drop warning-severity feedback |
| `timeout=<s>` | pet-routed tools | Per-call budget, clamped to `ROCQ_QUERY_TIMEOUT_CAP` (response carries `clamped_timeout`) |
| `timeout=<s>` | compile, compile_file, verify | Per-call budget, used as-is (0 = `ROCQ_COQC_TIMEOUT` / `ROCQ_VERIFY_TIMEOUT`) |
| Input cap | source/body/proof params | `ROCQ_MAX_SOURCE_SIZE` (default 1 MB) rejects oversize input |
