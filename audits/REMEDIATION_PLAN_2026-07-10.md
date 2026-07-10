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

**Status: A0–A4 and A6 are complete** (see the execution log at the end of this file for
commit hashes and validation); **A5 remains explicitly deferred**. The bullets below record
the originally agreed scope of each overlay.

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
| **M4a.1** `lower_bound_le_weighted_sum` | constant ≤ normalized nonneg weighting | `hGb_ge` | **LANDED** |
| **M4a.2** `simplex_coord_le_one` | coord ≤ 1 on the simplex | `hle1` | **LANDED** |
| **M4b** `exp_neg_div_le_coord_of_weighted_log_sum_ge` | pure log barrier (no ψ/G) | `hsublevel` | **LANDED** (ψ-wrapper retained) |
| **M4c** `exists_isMinOn_truncated_simplex` | generic finite-simplex EVT (no ψ/G) | inline | **LANDED** |
| **M4d** `exists_sinkhorn_interior_minimizer` | Sinkhorn strict interior minimizer | inline | **LANDED** |
| **M5** assembly | short public-theorem body | tail | **DONE** — `matrix_scaling_exists` now 47 lines |

**Heartbeat finding:** after M1–M4b the module compiles under **default** heartbeats;
`set_option maxHeartbeats 1000000` **removed**. Mathlib helper search: no clean
specialization for M4a.1 (Jensen needs `ConvexOn`/`Module`); `stdSimplex.le_one` exists
but only for the bundled type, so M4a.2 stays a private raw-function lemma.

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
- 2026-07-10: reported M3. Landed M4a (`lower_bound_le_weighted_sum`,
  `simplex_coord_le_one`) + M4b (`exp_neg_div_le_coord_of_weighted_log_sum_ge`), with the
  ψ-specific `hsublevel` reduced to a thin wrapper that only proves the `hlogsum` premise.
  `hle1` local deleted (M4b calls `simplex_coord_le_one` directly). Removed the module's
  `maxHeartbeats 1000000` — default heartbeats now suffice. `lake env lean` exit 0.
- 2026-07-10: reviewer chose the two-lemma split. Landed M4c
  (`exists_isMinOn_truncated_simplex`, generic; added `0 ≤ δ` for the unit-ball bound;
  witness `u` gives nonemptiness so no `[Nonempty ι]`) and M4d
  (`exists_sinkhorn_interior_minimizer`, `[Nonempty ι]`, returns the strict bound
  `δ < bs l` and drops `δ0` from the interface). `matrix_scaling_exists` is now **47 lines**
  (empty case → M4d → D2/aa → M3a → M1 → M2 → assemble). `lake env lean` exit 0.
- **The `matrix_scaling_exists` decomposition (A1) is complete.** Public statement
  unchanged across M1–M4d. Commit sequence: M1/M2 `3791d88`, M3a `1c9054b`,
  M4a/M4b `3ba1d17`, M4c/M4d `36265ff`; `matrix_scaling_exists` is a 47-line assembly
  over eight private lemmas.
- 2026-07-10: reviewer directed **A2 before A0** (README/STATUS/EXTERNAL_AUDIT/formalization.yaml
  already carry the essential corrections; a final docs sweep comes after the proof changes
  settle). One theorem family per commit; `_core` with minimal hypotheses + retained public
  wrapper (never delete/rename a public decl in this batch); update clients to the decl whose
  assumptions they actually use.
  - **A2.1** (commit 9161fa1, `BirkhoffHopf.lean`, +33/−7):
    `finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound_core` drops `0 ≤ D`
    (was already `_hD`). Wrapper re-adds `_hD` (compat). Both clients (`two_point_...`,
    `finite_..._crossratio_bound`) call core directly. `lake env lean` exit 0, no warnings.
  - **A2.2** (commit 1e4c003, `BirkhoffHopf.lean`, +34/−5):
    `positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_crossratio_bound` drops
    `_hdiam`. Wrapper `..._of_apply_hilbert_log_diameter_bound` re-adds it (compat). Higher theorem
    keeps threading `hdiam` through the wrapper (source-shaped API); docstring notes the cross-ratio
    machinery does the real work. PaperRoute untouched. `lake env lean` exit 0.
    **Route-independence re-sweep:** PaperRoute (`BirkhoffHopf/PaperRoute/Assemble.lean`) references
    the direct capstone only in a docstring (line 287) and uses only the shared defs
    (`positiveKernelCrossRatioBound`/`positiveKernelApply`/`finiteHilbertProjectiveLogSpread`); it
    does **not** reference the new core or any direct contraction/pointwise lemma. No cross-route
    proof-term dependency introduced.
  - **A2.3** (commit 893192a, `FranklinLorenz.lean`, +38/−6):
    `hard_core_franklinLorenz_right_column_pairwise_log_correction_geometric_bound_core` drops
    `_hbox` and `_hγ_lt_one`. Wrapper re-adds both (compat). Client `..._of_birkhoff_coefficient`
    calls core directly, still using `hbox` for the box-ratio lemma and `hγ_lt_one` for the
    log-to-error conversion — the correct dependency split. `lake env lean` exit 0.
  - No proof-body change beyond binder removal in any of the three; heartbeat overrides untouched
    (none added, none removed). Full `lake build` 8761 jobs exit 0; the five named axiom reports
    (`matrix_scaling_exists`, both Birkhoff capstones, both card inequalities) all
    `[propext, Classical.choice, Quot.sound]`. Route-independence re-sweep clean.

### A3–A6 execution log (2026-07-10)

Reviewer accepted A2 and directed the remaining batch A3 → A4 → A6 → A0, separate
bisectable commits, no mid-batch review.

- **A3** (commit `8356468`, `ProjectiveLag.lean`): body-only rewire of the production
  wrapper `..._drift_envelopes_atTop_from_gauge_iterates` to obtain its two convergence
  facts directly from `..._spreads_tendsto_zero_from_franklin_lorenz` (skipping the
  no-subsequence round trip). Theorem statement unchanged. Alternate compactness seam
  retained (`eventually_lt_of_tendsto_zero`, `no_positive_subsequence_of_pair_tendsto_zero`,
  `tendsto_pair_nonnegative_atTop_zero_of_no_positive_subsequence`, and the two
  `..._from_gauge_iterates` theorems). Docstrings corrected: the no-subsequence theorem is
  a derived alternate characterization (not the single hard theorem; the described
  contradiction proof is not what the body does); the reconstructed convergence theorem is
  neither the production route nor an independent proof. Obsolete Carroll/Birkhoff--Hopf
  implemented-route reference removed (implemented direct route is Doeblin/weighted-average;
  published comparison route is Eveson--Nussbaum). Reference sweep: production wrapper now
  calls the direct Franklin--Lorenz theorem; reconstructed convergence theorem has no
  production client; all seam decls retained; no external file depended on the old round trip.
  `lake env lean` exit 0; full build 8761 jobs exit 0.
- **A4** (commit `d7866bb`, `KLExhaustion.lean`, `QuasiInvariance.lean`, `PROOF_PIPELINE.md`):
  deleted the two `: True := by trivial` tautologies
  (`dyadicNormalizedIncrementMap_generates_standardWienerRealPathMeasure` — no clients;
  `cameronMartinDyadicDensity_uniformIntegrability_of_isCameronMartinPath` — fed an ignored
  `True` arg) and removed the `(_hui : True)` binder from
  `absCont_of_finiteDyadic_absCont_and_density_closure`, updating its caller. Retained the
  proved one-sided measurability bound, the finite-dyadic AC theorem, the explicit
  density-closure theorem, and the assembly wrappers; docstrings now state the closure is
  supplied by `hac` and the finite-dyadic family is source-facing context. No premature
  `Prop` interface. Module header + PROOF_PIPELINE A4 section describe the future work in
  prose (canonical anchored-interval carrier). Both files `lake env lean` exit 0; full build
  8761 jobs exit 0.
- **A6** (commit `c0c0495`, `scripts/`, `README.md`): added
  `scripts/check_nonvacuous_scaffolds.py` (textual ratchet against `True`-shaped theorem
  scaffolds and ignored `(_h.. : True)`/`(h.. : True)` binders; excludes `.git/`, `.lake/`,
  `reference/`, `.reference-clones/`, `Challenge/`; explicit empty allowlist). Extended
  `check_documentation_consistency.py` (remediation plan added to live set; require correct
  `ForMathlib.matrix_scaling_exists` + flag wrong `.Matrix.` form; STATUS two-route
  pluralism markers; flag deleted continuum names in live status docs, audit exempt; align
  slogan-scan exclusions with the rest of the tooling). Fixed README namespace error.
  Hardened `check_comparator_signatures.py` (missing `lake` → concise message, exit 3).
  Validation: py_compile clean ×4; nonvacuous check passes (fixture confirms it catches both
  patterns); doc consistency passes; audit_proof_shape exit 0; comparator lake-missing guard
  exits 3.
- **A0** (this commit): remediation plan reconciled to final code state with commit hashes;
  `PROOF_AUDIT_2026-07-10.md` findings marked resolved; live status docs reviewed for the
  final-tree invariants. **A5 remains explicitly deferred** until a real client consumes a
  verification-data interface.
