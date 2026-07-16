# rocq-mcp failure recovery — reasons, statuses, playbooks

Every failure response is `{success: false, error: str, reason: str}`.
Dispatch on `reason`, never on message text. The same `reason` is
recorded into the `recent_errors` ring buffer that `rocq_diag` returns.

## The reason taxonomy

| reason | Emitted by | Meaning / recovery |
|---|---|---|
| `validation` | any tool, pre-pet | Input shape was wrong (mode conflict, oversize source, empty name...). Fix the arguments; do not retry verbatim. |
| `not_found` | rocq_start, rocq_assumptions, rocq_switch | Name resolution failed (typo). The response carries recovery data — see `available_in_file` below / `available_switches` on rocq_switch. |
| `timeout` | pet-routed + coqc tools | The call exceeded its budget. On pet-routed tools pet was killed and restarted (`pet_restarted: true`; held state_ids are gone); on coqc tools (`rocq_compile*`, `rocq_verify`) nothing was killed. Retry with a larger per-call `timeout=` — see the timeout trap below. |
| `crashed` | pet-routed tools | Pet died or raised unexpectedly. If `pet_restarted: true`, pet was respawned; retry once, then check `rocq_diag`. |
| `memory_exhausted` | pet-routed tools | Pet RSS breached `ROCQ_MAX_PET_RSS_MB`; pet was killed. Check `rocq_diag` memory section; avoid the offending `vm_compute` or raise the cap. |
| `lock_contended` | pet-routed tools | Another call holds the pet lock (pet is NOT killed). Retry after in-flight calls settle; under multi-agent sharing see the concurrency guide. |
| `unavailable` | pet-routed tools | pytanque / the `pet` binary is not installed. Only coqc-based tools work; see README prerequisites. |
| `tactic_failed` | rocq_check (mid-batch) | Coq rejected a tactic — a *proof* problem, not a transport problem. Use `last_valid_state_id` (below). |
| `query_rejected` | rocq_search | Coq rejected the Search pattern/filter syntax. Fix the pattern (see rocq_query for raw vernacular escape hatch). |
| `compile_error` | rocq_compile, rocq_compile_file, rocq_verify | coqc returned non-zero. Use `error_positions` / `state_capture_status` / `errors` (below). |
| `axiom_dependency` | rocq_verify | The proof relies on `Admitted`/`admit` or a non-whitelisted axiom. |
| `type_mismatch` | rocq_verify | Phase-3 check: the proof proves a different type than the problem statement. |

## rocq_check failure recovery

On `tactic_failed`, the response carries `last_valid_state_id` — the
state after the last sentence that DID succeed — plus `failed_command`.
Continue immediately via `rocq_check(from_state=last_valid_state_id, ...)`
or `rocq_step_multi(from_state=last_valid_state_id, ...)`; no session
restart needed.

## state_capture_status (rocq_compile / rocq_compile_file failures)

When coq-lsp is available and a compile fails, the server tries to
capture the interactive proof state at the error position:

- `"ok"` — captured. The response also carries `state_id`, `goals`,
  `file`, `theorem`, `proof_finished`. Recover directly via
  `rocq_check(from_state=state_id)` or `rocq_step_multi(from_state=state_id)`.
- `"outside_proof"` — the error is outside any open proof (bad import,
  bad statement). No `state_id`; follow the response `hint`.
- `"no_position"` — coqc reported no parseable position.
- `"timeout"` / `"crashed"` / `"lock_contended"` / `"unavailable"` /
  `"memory_exhausted"` — enrichment itself failed; follow the original
  `hint` (typically `rocq_start(file=..., line=..., character=...)` at
  the reported error position).

## Multi-error entries (rocq_compile_file only)

On `compile_error` with pet available, the response may carry
`errors: list` — pet's structured walk of the whole file, one entry per
failing declaration: `{proof_name, kind, start_line, end_line, code,
message, start_args}` — `start_args` is a ready-made `{file, line,
character}` for `rocq_start`/`rocq_goal` at the failing declaration
(lines 0-based). This surfaces errors *beyond* the first one coqc
reports;
cascade failures inside one proof body are deduplicated. The field can be
**present and empty** (`errors: []`) when the walker ran but pet did not
reproduce the coqc failure — read that as "no additional errors found",
not "no errors at all". Absent on success, without pet, and when
`ROCQ_COMPILE_MULTI_ERROR_CAP=0`.

## available_in_file (typo recovery)

On `not_found` from `rocq_start` / `rocq_assumptions`, the response
includes `available_in_file: list[str]` — the file's defined names,
sorted and capped. When capped: `available_in_file_truncated: true`,
`available_in_file_total` (uncapped count) and `available_in_file_limit`
(the active cap) are also present; call `rocq_toc` for the outline
(itself char-capped).
Fuzzy-match the requested name against this list to recover from typos.

## proof_tactics_status (broken chain on a finished proof)

When `rocq_check` reports `proof_finished: true` it normally returns
`proof_tactics` (the root-to-leaf tactic list). The chain is
materialized at each state's creation, so ancestor eviction can no
longer break it; the only remaining break is the finished state itself
being evicted before the response was assembled (LRU churn or a pet
restart mid-call). Then `proof_tactics` and `proof_hint` are omitted
and the response carries `proof_tactics_status: "ancestor_evicted"`
(`"cycle"` is reserved but no longer produced), `proof_tactics_broken_at`
(the finished state's id) and `proof_tactics_hint`. You never see a
half-chain. Recovery: re-run the assembled tactic sequence you already
know from your own transcript, or restart with `rocq_start` and replay.

## pet_restarted: the diag playbook

Any response with `pet_restarted: true` means the pet subprocess was
killed and will be respawned lazily. Call `rocq_diag` and read:

- `memory.pet_rss_mb` vs `memory.max_rss_mb_threshold` — was it a memory
  breach? (`peak_pet_rss_mb` shows the high-water mark.)
- `recent_errors` — what failed recently, with `reason` per entry.
- `load_average` — CPU saturation vs a genuinely diverging tactic.
- `lock` — `contended_total` / `wait_ms_max` reveal multi-caller
  contention on the single pet lock.
- `enrichment_failures` — counters of degraded best-effort enrichment.

Note: a pet restart wipes Fleche's cache — held `state_id`s from before
the restart are gone (`rocq_start` again), and the first call after a
restart re-pays import loading.

## The rocq_assumptions timeout trap

`Print Assumptions` triggers `.vo` opaque-proof fetching on first call
(often 40+ modules on heavy imports). A pet restart from a timeout wipes
that progress, so retrying with the *same* timeout pays the full cost
again and times out again. Set `timeout=` high on the FIRST call (e.g.
180–300) rather than relying on a retry.

## degraded (best-effort enrichment failed)

Some response fields are best-effort (goals at a state,
`available_in_file`, focus depth). When such an enrichment step fails,
the response still succeeds but carries `degraded: ["<field>:<code>", ...]`
(e.g. `"goals:pet_call_failed"`). Treat the named fields as missing, not
as authoritative empties. Set `ROCQ_DEBUG_ENRICHMENT=1` server-side to
also get `degraded_detail` with exception text; `rocq_diag` aggregates
per-code counters under `enrichment_failures`.
