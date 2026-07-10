# Remediation plan — audit dialogue outcome (2026-07-10)

Working record of the plan agreed with the external reviewer of
[`PROOF_AUDIT_2026-07-10.md`](PROOF_AUDIT_2026-07-10.md). The reviewer is a stronger
model without Lean tooling; this repo's agent supplies the tooling evidence (axiom
reports, `lean_references`, `lean_minimal_hypotheses`, scratch elaboration). This file
preserves the high-level goal and the concrete overlay sequence so the work survives
context resets. It is a planning doc, not a status slogan — every claim below is scoped
to a command + commit.

## High-level goal (unchanged)

1. **Primary:** the two card inequalities `Drsb.wdrsb_cost_bound` and
   `Drsb.sdrsb_cost_bound` are proved under their stated assumptions. Verified
   axiom-clean:

   ```
   #print axioms Drsb.wdrsb_cost_bound  -- [propext, Classical.choice, Quot.sound]
   #print axioms Drsb.sdrsb_cost_bound  -- [propext, Classical.choice, Quot.sound]
   ```

   The Chen–Georgiou–Pavon continuum development is **not** a proof-term dependency of
   either card theorem (`V` is abstract at the `Drsb` layer; the CGP import contributes
   only a docstring reference). `MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual`
   and the Gao–Kleywegt worst-case-structure corollaries are **parallel source-faithful
   developments, not gates** for the card inequalities.

2. **Secondary:** keep the reusable `ForMathlib` mathematics upstreamable and honest.
   Most of the audit's remediation concerns this secondary program, not the card.

## Reviewer-agreed overlay sequence

Priority is by upstream mathematical value, not card-path urgency (the card is closed).

- **A0 — documentation truthfulness.** Record the card axiom reports with commit +
  toolchain; correct the card dependency graph; document the two Birkhoff proofs as a
  deliberate feature (below); drop completion slogans in favour of scoped command/result
  prose; relabel MEK/GK structure results as parallel developments; date/supersede stale
  plan sections. No theorem changes.
- **A1 — decompose `matrix_scaling_exists`** (highest immediate upstream value). See
  extraction map below. Public statement unchanged; no module split.
- **A2 — hypothesis minimization** via `_core` + source-facing wrappers. Confirmed
  body-unused hypotheses (via `lean_minimal_hypotheses`, filtered for call-site vs.
  body breakage): `_hD` (`0 ≤ D`) and `_hdiam` in `BirkhoffHopf.lean`, `_hbox` and
  `_hγ_lt_one` in `FranklinLorenz.lean`. `_hγ_lt_one` belongs on the first theorem using
  decay of `γ^k`. Keep `0 ≤ D` on the paper-facing wrapper — describe removal as
  hypothesis minimization, **not** a new negative-diameter theorem (the `D < 0` branch
  may be vacuous under the pairwise assumptions).
- **A3 — ProjectiveLag dependency clarification.** One-wrapper rewire, no deletions:
  point `..._drift_envelopes_atTop_from_gauge_iterates` at
  `..._tendsto_zero_from_franklin_lorenz` directly. Retain the no-subsequence machinery
  (`ProjectiveLag.lean:1078,1353,1391,1428`) as a labeled alternate compactness seam;
  reference sweep confirmed every use is internal, no external clients. Update docstrings
  to stop calling the derived no-subsequence result the hard Sinkhorn theorem.
- **A4 — minimal continuum honesty.** Delete the two `: True := by trivial` scaffolds
  (`KLExhaustion.lean:24`, `QuasiInvariance.lean:66`) and the ignored `_hui : True`
  client; add roadmap prose for the intended target on the canonical anchored-interval
  carrier. No elaborate `Prop` interface (the `RealPath := ℝ → ℝ` carrier is known wrong).
- **A5 — verification-data interfaces** deferred until a real client consumes them.

## Birkhoff two-route independence certificate (2A — established)

Preserve as a deliberate feature in the documentation:

- direct AI-discovered Doeblin / weighted-average proof
  (`ForMathlib.Matrix.positive_kernel_birkhoff_hopf_contraction`, `BirkhoffHopf.lean`);
- source-faithful Eveson–Nussbaum proof
  (`...PaperRoute.positive_kernel_birkhoff_hopf_contraction_paper_route`);
- **shared definitions, independent contraction cores** — `BirkhoffHopf.lean` imports
  only `Mathlib`; the paper route imports the direct module (via `PositiveConeHilbert`)
  **only** for the shared defs `positiveKernelApply`, `finiteHilbertProjectiveLogSpread`,
  `positiveKernelCrossRatioBound`. Proof-term reference sweep confirms neither route's
  capstone or hard lemma invokes the other's; the one cross-mention is a docstring;
- the paper route obtains the **sharper** two-dimensional coefficient.

## `matrix_scaling_exists` extraction map (A1)

Single theorem, `ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean:49–354`. Tail-first.

| Piece | Content | Source lines | Status |
|---|---|---|---|
| **M1** `common_column_residual_eq_zero` | mass conservation ⟹ common residual `μ = 0` | ~312–337 | **LANDED** (commit 3791d88) |
| **M2** `column_scaling_of_zero_residual` | zero residual ⟹ column scaling equation | ~345–353 | **LANDED** (commit 3791d88) |
| **M3a** `stationarity_pairwise_residual_eq` | ψ-specific `HasDerivAt` core | ~210–311 | **LANDED** (this overlay) |
| **M3b** pairwise-equal family ⟹ constant | choose `j0`, `μ := r j0` | inline | **LANDED inline** (in `key`/`hresid`) |
| **M4** compact interior minimizer exists | boundary-coercivity confinement + EVT | ~62–201 | **not this overlay** |
| **M5** assembly | short public-theorem body | 49–56, 338–353 | done for the tail; M4 pending |

M1 passes the row relation as the construction-independent
`hrow : ∀ i, a i * ∑ j, G i j * b j = p i` (never sees `ψ`/`D2`/`aa`). M3a takes
`IsMinOn ψ K bs` restricted to the line `bs + t • (e j − e j₀)`; a narrow private
structure is permitted only if the explicit-argument signature is unreadable — try
explicit first. Do **not** start M4 in the M3 overlay.

## Execution log

- 2026-07-10: plan locked with reviewer. Landed M1+M2 (commit 3791d88);
  `lake build ...SinkhornScaling` OK, axioms clean.
- 2026-07-10: landed M3a (`stationarity_pairwise_residual_eq`) + inline M3b.
  M3a signature: primary data `(p q G hG δ hδ_pos bs hbs_gt hbs_sum)` + `IsMinOn ψ K bs`
  (ψ, K reconstructed inline); **no `hp`/`hq` positivity** (p, q are coefficients only);
  `classical` at top (was file-level in `matrix_scaling_exists`); derivative body copied
  verbatim (j0→j₀); **no per-lemma `maxHeartbeats` needed** (elaborates under default
  200000 in isolation). No private structure required — explicit args stayed readable.
  CLI validation: `lake env lean SinkhornScaling.lean` exit 0; full `lake build` 8761 jobs
  exit 0 (incl. `Drsb.Basic`); CLI `#print axioms`:
  `matrix_scaling_exists`, `wdrsb_cost_bound`, `sdrsb_cost_bound` all
  `[propext, Classical.choice, Quot.sound]`. MCP and CLI agreed throughout.
- Next: report M3 to reviewer; then decide M4 first target (convex-combination lower
  bound `hGb_ge` vs. logarithmic sublevel confinement `hsublevel`).
