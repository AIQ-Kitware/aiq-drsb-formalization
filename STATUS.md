# STATUS.md — where this repo actually stands

> **Dated snapshot. This is the file that goes stale — update it, don't trust it blindly.**
> Evergreen orientation, conventions, and the traps live in [`AGENTS.md`](AGENTS.md);
> the running narrative of how we got here lives in [`JOURNAL.md`](JOURNAL.md);
> the work plan lives in [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).
>
> **Verify before you trust.** Two commands re-derive this whole file's factual core:
> ```bash
> cat lean-toolchain && grep -A2 '"name": "mathlib"' lake-manifest.json   # the real pin
> grep -rn --include=*.lean --exclude-dir=.lake --exclude-dir=.reference-clones --exclude-dir=reference -w sorry .
> ```

**Last updated: 2026-07-10**

## Snapshot

| | |
|---|---|
| Toolchain | `leanprover/lean4:v4.32.0-rc1` |
| Mathlib | `e3b73828…` (2026-07-09), `inputRev = master` — **policy: track latest master** |
| Open goals | **16**, all in the projective-metric frontier below |
| DRSB card claims | ✅ **proved** (`wdrsb_cost_bound`, `sdrsb_cost_bound`) — untouched by the frontier |
| Strong duality (all four) | ✅ **proved**, each `le_antisymm(weak, one explicit attainment edge)` |
| `energy_identity` | ✅ **closed** — Girsanov content isolated to the explicit `hCM` edge |

The six paper libraries + `Drsb` + most of `ForMathlib` are proved and dependency-clean. **Every one
of the 16 open goals is upstream `ForMathlib`/Sinkhorn-convergence infrastructure — no card claim
depends on any of them.**

---

## CURRENT FRONTIER (2026-07-10) — read this first

> **The live work is Sinkhorn *convergence* via the Birkhoff–Hopf contraction.** The DRSB card
> claims and all six paper libraries are proved; this frontier is upstream `ForMathlib`
> infrastructure, not a card claim.

**16 open goals**, all in one connected effort. Get the exact inventory with the grep at the top of
this file — never trust a count in a doc, including this one.

| File | Open | What |
|---|---|---|
| `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean` | 3 | Carroll-route weighted-average contraction core |
| `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/*` | 10 | Eveson–Nussbaum-route cone/2×2 reduction |
| `ForMathlib/Analysis/ExpLogBounds.lean` | 1 | `|exp t − 1| ≤ exp C · |t|` conversion |
| `ChenGeorgiouPavon2021/…/Compactness/FranklinLorenz.lean` | 2 | geometric decay of the two scaling corrections |

### The decision (made 2026-07-10) — finish the PAPER ROUTE

Two parallel, unfinished routes to the same theorem coexist. **The Eveson–Nussbaum
`PaperRoute/*` is the one to finish** — it is the more correct and (per the sources) the easier
route, and it is what `PaperRoute`'s own header already declares itself to be: "the intended
replacement spine for the currently parked weighted-average route."

**The Carroll weighted-average route in `BirkhoffHopf.lean` is to be *sequestered, not deleted*.**
Getting it too would be nice; it is simply not the priority. Sequester it into its own module rather
than removing it — nothing is lost, and it stops competing for attention.

### The architecture is already right — this is the key fact

`ForMathlib.Matrix.positive_kernel_strict_birkhoff_contraction_coefficient` is **the public seam**.
It is the *only* Birkhoff–Hopf theorem `FranklinLorenz.lean` consumes (lines 507, 529), and both
routes exist solely to discharge its single open goal. **Every weighted-average theorem has zero
external consumers** (verified by grep), so the split below is mechanical and safe.

```
BirkhoffHopf.lean  = SHARED CORE (keep)                              PaperRoute/*  (finish this)
  defs: positiveKernelApply, finiteHilbertProjectiveLogSpread,          PositiveConeHilbert
        positiveKernelCrossRatio(Bound), positiveKernelBirkhoffCoefficient,   ConvexHullDiameter
        IsBirkhoffHopfContractionCoefficient, IsStrict…                       PositiveMatrixDiameter
  proved: positivity + sSup bridges + positive_kernel_apply_crossRatioBounded  TwoByTwo
          + positive_kernel_apply_hilbert_log_diameter_bound_of_apply_crossratio_bound   Assemble
  seam:   positive_kernel_strict_birkhoff_contraction_coefficient  ◄──── discharged by
                    ▲                                                    PaperRoute's
                    └── consumed by FranklinLorenz.lean                  …_paper_route
```

### Your first moves (cheapest → hardest)

1. **Sequester the Carroll route.** Move these eight declarations out of `BirkhoffHopf.lean` into a
   new `BirkhoffHopf/WeightedAverageRoute.lean` (0 external consumers, so nothing else changes):
   `two_point_weighted_average_…`, `finite_weighted_average_…_of_pairwise_log_bound`,
   `finite_weighted_average_…_of_crossratio_bound`,
   `positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_…`,
   `positive_kernel_birkhoff_hopf_contraction_of_apply_hilbert_log_diameter_bound`,
   `positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound`,
   `positive_kernel_birkhoff_hopf_contraction`, `positive_kernel_birkhoff_contraction_coefficient`.
   Keep the defs and the proved core lemmas where they are. Document it as an alternate route.
2. **Free win — `positive_kernel_apply_hilbert_log_diameter_bound_paper_route`** (`PositiveMatrixDiameter.lean`)
   is *the same statement* as the already-proved, **not** placeholder-backed
   `positive_kernel_apply_hilbert_log_diameter_bound_of_apply_crossratio_bound` in the core. Discharge
   by `exact … G hG (positive_kernel_apply_crossRatioBounded G hG)`.
3. **Near-trivial — `quadrant_hilbert_coordScale_eq` / `_equivPerm_eq`** (`PositiveConeHilbert.lean`).
   The `d i` scale factors cancel *inside* the log, and reindexing a `Set.range` along an `Equiv`
   leaves it literally equal. No positivity of `x`/`y` is needed (both sides degenerate to
   `Real.log 0 = 0` consistently).
4. **Easy — `positiveKernel_column_diameter_le_crossratio_bound`**: the spread of columns `j, j'` is a
   `sSup` of `log (positiveKernelCrossRatio G i i' j j')`; bound each by `positiveKernelCrossRatio_le_bound`
   and apply `Real.log_le_log`.
5. **Moderate — `ConvexHullDiameter.lean`** (Eveson–Nussbaum Prop 2.9(b)). Then
   `positiveKernelApply_image_diameter_le_column_diameter` follows: `G x = Σⱼ xⱼ · (column j)` is a
   nonnegative combination of the columns, so it is exactly the nonnegative-hull lemma.
6. **Moderate — `positive_twoByTwo_reduces_to_symmetric_normal_form`** (`TwoByTwo.lean`).
   ⚠️ **Do not follow the paper here.** Eveson–Nussbaum Lemma 5.1 goes through a doubly-stochastic
   normalization + intermediate value theorem; the Lean statement as written needs none of that.
   Explicit closed-form witnesses exist: with `ρ = A₀₀A₁₁/(A₀₁A₁₀)` (and `hdet` is *exactly* `ρ ≠ 1`),
   take `α = √ρ`, `c₁ = 1`, `c₀ = √(A₀₁A₁₁ / (A₀₀A₁₀))`, `r₀ = 1/(A₀₁c₁)`, `r₁ = 1/(A₁₀c₀)`;
   if `ρ < 1`, swap the rows first (which sends `ρ ↦ 1/ρ > 1`).
7. **Hard — `symmetricTwoByTwo_birkhoff_contraction`** (`TwoByTwo.lean`). The analytic core is
   **already proved** in the same file as `symmetricTwoByTwoPhi_le` (the `α(α−1)(t−1)²` factorization).
   What remains is connecting `φ` to the Hilbert spread. Carroll's Step 4 is the cross-check:
   AM-GM `1 + rsy² ≥ 2y√(rs)`, then two mean-value comparisons.
8. **Hardest — `positiveKernel_birkhoff_contraction_from_twoByTwo`** (`Assemble.lean`), Eveson–Nussbaum
   Lemma 3.11: reduction to two-dimensional subspaces. ⚠️ Note the "public" theorem in that file is
   currently just `exact` of this open goal, so `Assemble.lean` carries **no content** today.
9. Finally, discharge the seam `positive_kernel_strict_birkhoff_contraction_coefficient` from
   `…_paper_route`. Mind the instances: the seam has **no** `[Nonempty ι]`/`[Nonempty κ]`, so it needs
   an empty-type case split (both sides degenerate to `0 ≤ γ·0`); the paper-route theorem assumes them.

**Two facts to keep in mind while doing the above:**

- **The target is TRUE, and deliberately coarse.** `IsBirkhoffHopfContractionCoefficient G γ` is a
  real, non-vacuous statement (`∀ x y > 0, logSpread(Gx,Gy) ≤ γ · logSpread(x,y)`; the diagonal
  `i=i'` term forces `spread ≥ 0`). The chosen `γ = (B−1)/B` with `B = 1 + Σ cross-ratios` is
  **weaker** than the sharp Birkhoff constant `tanh(Δ/4) = (√B−1)/(√B+1)`, since `B ≥ 1+M ≥ √B+1`.
  ⚠️ But the coarse constant does **not** appear to make the proof easier — the analytic core is the
  same. Proving the sharp `tanh` and weakening may well be the shorter path.
- **`FranklinLorenz.lean` is already decoupled.** Its hard cores take
  `IsBirkhoffHopfContractionCoefficient G γ` as an explicit *hypothesis* (the house edge pattern),
  so its 2 goals and the contraction theorem can be attacked independently, in either order.

**Nothing here can be vendored.** The 2026-07-10 sweep (`SURVEY_LEADS.md` § Projective-metric
frontier) found that the **Hilbert projective metric and the Birkhoff–Hopf contraction do not exist
in Lean anywhere** — not in Mathlib, not in any external repo. Perron–Frobenius *does* exist
externally (sorry-free, MIT/Apache-2.0) but is **not on the critical path**: our Sinkhorn existence
proof never used it. ⚠️ Every Mathlib `Birkhoff`/`Hilbert` grep hit is a different theorem.

**The papers are already distilled** — `prose/distilled_literature/` maps one-to-one onto these goals:

| Open goal | Distilled source |
|---|---|
| `two_point_weighted_average_log_crossratio_contraction_…` | `Carroll2004_birkhoff_contraction.tex` **Step 4** (elementary: AM-GM `1+rsy² ≥ 2y√(rs)`, then two mean-value comparisons) |
| `finite_weighted_average_log_crossratio_contraction_…` | `Carroll2004…` **Step 3** (reduce *n* coords → 2 by linear programming — the genuinely hard step) |
| `PaperRoute/ConvexHullDiameter.lean` | `EvesonNussbaum1995_birkhoff_hopf.tex` **Prop 2.9(b)** |
| `PaperRoute/PositiveConeHilbert.lean` | ibid. **Lemma 3.12** (cone-iso invariance) — both goals are near-trivial (the scale factors cancel inside the log) |
| `PaperRoute/TwoByTwo.lean` normal form | ibid. **Lemma 5.1**. NB the paper's doubly-stochastic + IVT route is *unnecessary* for the Lean statement: `α = √(cross-ratio)` and the scalings are explicit closed forms |
| `PaperRoute/Assemble.lean` | ibid. **Lemma 3.11** (2-dim subspace reduction) — the hard one; and note the "public" theorem there is just `exact` of that open goal, so it carries no content |
| `PaperRoute/PositiveMatrixDiameter.lean` | ibid. **Theorem 6.2** (cross-ratio diameter formula) |
| `FranklinLorenz.lean` ×2 | `FranklinLorenz1989_matrix_scaling.tex` **Lemma 2 / Theorem 4** |
| `ExpLogBounds.lean` | none needed — one-variable calculus |

Original PDFs for all of these are in `prose/papers/` (`nusseveson1995.pdf`, `carroll-birkoff.pdf`,
`FranklinLorenz1989-…pdf`, Lemmens–Nussbaum, Birkhoff 1957). The `.tex` notes are far easier to work
from, but each has a *Distillation gaps* section — **verify a theorem/page anchor against the PDF
before citing it as a numbered result.**

---

## Landed work (history)

*Kept for provenance. The per-session narrative — including the soundness audits and what each
proof actually cost — is in [`JOURNAL.md`](JOURNAL.md).*

- **Next steps + the full triage live in [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).**
  Per the user (2026-07): **no Fable** — decompose each remaining target into its natural
  subproblems and prove step-by-step with the thinking budget turned up. The SDE/PDE and
  OT-measurable-selection blocks may still need a documented `dependency` or a Mathlib-infra lift
  (decide with the coordinator). ForMathlib upstreaming queue:
  DV ✓, Normalization ✓, WeakDuality ✓ (three kernels, incl. the Ξ-restricted one),
  SinkhornScaling ✓ (`matrix_scaling_exists`), **KLDataProcessing ✓ (`toReal_klDiv_map_le` — the
  KL data-processing inequality; a clean standalone Mathlib PR candidate)**,
  **PathEmbedding ✓ (`exists_measurableEmbedding_nat_of_separating` — standard-Borel + countable
  separating family ⇒ measurable embedding into `ℕ→ℝ` with measurable left inverse; also a Mathlib
  PR candidate)**.
- **Source-pass note (2026-07-07):** `ForMathlib/MeasureTheory/GaussianCameronMartin.lean`
  stages the next sequence-model Cameron–Martin brick from `PLAN_CONTINUUM_CLOSURE.md` as a
  candidate no-placeholder overlay: iid `stdSeqGaussian`, `prefixFiltration`, finite-prefix marginals,
  shift/restriction commutation, and `cmDensityProcess`. The producing sandbox had no Lean compiler;
  run `lake env lean ForMathlib/MeasureTheory/GaussianCameronMartin.lean` before marking M2.4 done.

- **Plan A(i) DONE (2026-07-04) — the continuum embedding edge is now a THEOREM**
  (`ForMathlib/MeasureTheory/PathEmbedding.lean`, all dependency-clean; JOURNAL Session 4 addendum 8).
  `energy_eq_klReal_via_embedding`'s abstract measurable-embedding hypothesis is *constructed* for the
  continuous-path model (`C(T,ℝ)`, dense-time evaluation), via Mathlib's existing `ContinuousMap`
  Polish instances + Lusin–Souslin — **no brownian-motion vendor needed**. `eq_toReal_klDiv_continuousMap_of_tendsto`
  is the continuum identity for `C(T,ℝ)` laws with the embedding edge discharged; only `hconv`
  (gap #2 Girsanov) + the `SBData.Path := C([0,1],X)` re-typing (roadmap step 3) remain.
- When a `reference/` result is validated and promoted, update `reference/README.md`.

> **2026-07-08 module-layout note (GPT-5.5 Thinking).** Public aggregate imports remain stable,
> but the theorem libraries are split further. `ForMathlib.MeasureTheory.GaussianCameronMartin`
> is now an aggregate over `Basic`, `Energy`, `FiniteKL`, `InfiniteKL`, `Density`, and
> `AbsoluteContinuity`. `ChenGeorgiouPavon2021.Continuum.WienerDyadic` is an aggregate over
> `Continuum.Wiener.*`; `Continuum.Closure` is split into Sobolev, KL-exhaustion,
> quasi-invariance, and assembly modules; `SocOt` is split into dynamic, static, entropic-OT,
> and Sinkhorn wrappers. Downstream code may keep importing the aggregate modules.
>
> **Progress-bar policy.** Future placeholders should live only on the mathematical theorem targets
> needed to discharge final DRSB assumptions. Do not add placeholders to downstream integration/assembly
> lemmas that merely consume those targets; those should be wired only after the target theorems are
> proved or stated as explicit hypotheses/interfaces.

- **Done:** repo scaffolded; `ForMathlib` + 5 paper libraries + `Drsb` capstone all
  `lake build` green; prose transcriptions + PDFs in place; `formalization.yaml` maps
  every declaration to its source.
- **Proofs landed (proof pass, foundational-first):**
  - `ForMathlib.MeasureTheory.DonskerVaradhan` — the full DV family (dependency-clean).
  - `ForMathlib.MeasureTheory.Normalization.isProbabilityMeasure_inv_univ_smul` —
    normalize a finite nonzero measure to a probability measure (new; the first
    pipeline extraction — a genuine Mathlib gap, consumed by `exists_worstCase_gibbs`).
  - `WangGaoXie2023.logPartition_eq_gibbs_sSup` (DV applied to the tilted reward),
    `worstCase_conditional_tilted` (density rewrite), and
    `exists_worstCase_gibbs` (Remark 4: normalize the unnormalized Gibbs measure → a
    probability measure ∝ the tilt; now via the ForMathlib lemma).
  - `ChenGeorgiouPavon2021.staticSB_eq_entropicOT` (T0: the `hgibbs` rewrite — when the
    endpoint law IS the entropic-OT reference, the two `sInf`s coincide).
  - `BlanchetMurthy2019.wdro_strong_duality_dualFn` — the `Lc`-form of
    `wdro_strong_duality`, derived from it by defeq. Not an independent strong-duality
    proof; the debt stays in one place.
  - `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost` — the OT-DRO
    per-coupling **weak-duality kernel** (ported from `reference/V4.lean`, generalized to
    arbitrary cost `c`); dependency-clean.
  - ⭐ **BOTH DRSB evaluation-card claims PROVED, dependency-clean** — the project's headline
    result `𝔼_perturbed[V] ≤ 𝔼_worst-case[V]` for both balls:
    - `Drsb.wdrsb_cost_bound` (Wasserstein): weak-duality kernel + `sqCost` symmetry, under
      regularity + the OT-attainment edge `hOT`.
    - `Drsb.sdrsb_cost_bound` (Sinkhorn): composes the proved
      `WangGaoXie2023.sinkhorn_weak_duality_kernel` (per-point Gibbs/DV bound integrated
      over `p₀`) with `budget ≤ ε`, under `hκ>0` + the Sinkhorn attainment+disintegration
      edge `hSink`; dual restricted to `0<lam` (the `lam=0` `logPartition` is junk — a
      third statement issue found this pass; ess-sup convention unencoded).
    The cards need only the `≤` direction; the strong-duality `≥` seams are now discharged
    too (below), each modulo one explicit attainment hypothesis rather than a placeholder.
  - **General duality + the "strong = weak + attainment" pattern** (dependency-clean):
    `GaoKleywegt2023.weak_duality_prop1` (general Wasserstein `v_P ≤ v_D`, via the kernel +
    coupling ε-approx + the unconditional `Real.sSup_neg` for `Φ`↔sup-form) and
    `GaoKleywegt2023.strong_duality_thm1` = `le_antisymm(weak, attainment)` — the `≥` is a
    single explicit **attainment edge**, isolating the whole strong-duality gap to that one
    OT measurable-selection fact. `Drsb.wdrsb_strong_duality` delegates to it (`sqCost`
    symmetric ⇒ `Lc = −Φ`), completing the **WDRSB capstone** (cost bound + strong duality).
  - **Both weak-duality kernels are staged in `ForMathlib.OT`** (paper-agnostic,
    upstreamable): `expect_le_dualIntegrand_add_lam_couplingCost` (Wasserstein) and
    `expect_kernel_le_lam_sinkhornBudget_add_logPartition` (entropic/Sinkhorn) — the two
    "from-scratch" Mathlib gaps the cards descend from.
  - **Atop-a-placeholder reductions** (concentrate debt, not dependency-clean):
    `ChenGeorgiouPavon2021.schrodingerBridge_KL_eq_SOC` (sInf-translation atop
    `energy_identity`) and `optimal_control_eq_neg_grad_value` (atop
    `optimal_control_eq_grad_log` + a `grad`-negation edge).
  - **ALL strong-duality *equalities* proved** (2026-07), each `le_antisymm(weak,
    attainment)` with the `≥` isolated to one explicit OT-attainment hypothesis:
    `BlanchetMurthy2019.wdro_strong_duality` (primary Wasserstein), `WangGaoXie2023.strong_duality`
    (Sinkhorn Theorem 1(II)), and the two **`Drsb` capstones** `wdrsb_strong_duality` /
    `sdrsb_strong_duality` — **`Drsb` is now proved** (all four card+duality results land).
  - `WangGaoXie2023.primal_feasible_radius_nonneg` (was the mis-stated `primal_feasible_iff`)
    — the honest necessity half of Theorem 1(I), `0 ≤ κ ⇒ (Nonempty → 0 ≤ ε)`, dependency-clean
    (see §6). Sufficiency is the deferred ρ̄-ball attainment edge.
- **Finite Sinkhorn scaling — ✅ PROVED, dependency-clean (2026-07):**
  `ForMathlib.matrix_scaling_exists` + `ForMathlib.sinkhorn_potentials_exist`
  (`ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean`). Mathlib has **neither** Brouwer
  nor the Birkhoff/Hilbert-metric contraction (grep-verified), so the proof is a **log-domain
  convex minimization** of `ψ(b)=∑ᵢ pᵢ log(∑ⱼ Gᵢⱼ bⱼ) − ∑ⱼ qⱼ log bⱼ` over the open simplex:
  boundary blow-up `−qⱼ log bⱼ→+∞` confines the sublevel set to an explicit compact set
  (extreme value theorem — no coercivity lemma), and the marginal equations fall out of the
  1-D directional derivatives along `eⱼ−eₖ` (`IsLocalMin.hasDerivAt_eq_zero`), with **mass
  conservation `∑p=∑q` exactly killing the Lagrange multiplier**. `ChenGeorgiouPavon2021.
  sinkhorn_potentials_exist` now delegates to a proved proof. `matrix_scaling_exists`
  is a clean general lemma staged for Mathlib upstreaming (Sinkhorn scaling is a genuine gap).
- **Vendored external proof + discrete energy identity — ✅ landed (2026-07):** vendored
  `mrdouglasny/gibbs-variational`'s `GaussianEntropy.lean` (Apache-2.0, commit `75e08d8`) →
  `ForMathlib/MeasureTheory/GaussianEntropy.lean` (Cameron–Martin `KL(N(·+h)‖N)=½‖h‖²`;
  attribution in file header + README + `formalization.yaml` + `SURVEY_LEADS.md`). Built on
  it, the **proved, dependency-clean** Euler–Maruyama discrete energy identity
  `ForMathlib…klDiv_emShift_eq_emEnergy` → `ChenGeorgiouPavon2021.energy_identity_euler_maruyama`:
  `(KL(P^u‖P^0)).toReal = ∑ₖ Δt·½‖u_k‖²`, the discrete/Gaussian layer of `energy_identity`
  (4.19) — the quantity the card measures (§3). The continuous `energy_identity` stays a bare
  placeholder (count unchanged at 12); the single remaining edge is the Δt→0 SDE limit
  (PROOF_PIPELINE §2).
- **Worst-case structure — ✅ BOTH GaoKleywegt corollaries PROVED, dependency-clean (2026-07);
  `GaoKleywegt2023` is now proved:**
  - `dataDriven_worstCase_cor2ii` (Cor 2(ii), eq. 29 — the `≤ N+1`-atom empirical worst case):
    `μ*` built as the explicit `K = 2` weighted-Dirac double-sum; probability measure,
    `∈ ambiguitySet` (explicit transport plan + `ForMathlib.OT.otCost_le_couplingCost`),
    closed-form `Ψ`-expectation and the eq. (29) split-form identity all **proved**. Local
    copies of `isProbabilityMeasure_wsum`/`integral_wsum`/`map_wsum` (→ ForMathlib dedup TODO).
  - `worstCase_structure_cor1` (Cor 1(ii), eq. 27 — the general-`ν` 2-map transport
    `μ* = pstar·T̄#ν + (1−pstar)·T*#ν`): same house pattern via `Measure.map` pushforwards +
    `integral_map` (with **regularity edges** since `c`/`Ψ` carry no standing measurability);
    2nd marginal `= ν` because `snd∘(T,id)=id`; eq. (27) measure form is `rfl`.

  Both are §5-safe: the structured optimizer is **not** hypothesized — only genuinely-weaker
  ingredient edges are (mixture weight, measurable a.e.-argmin maps/atoms, feasibility budget,
  and one `≥` attainment edge — the `le_antisymm(constructive, one edge)` posture shared with
  `MohajerinEsfahaniKuhn2018.worstCase_exists`).
- **Data-driven duality equality — ✅ PROVED, dependency-clean (2026-07); `MohajerinEsfahaniKuhn2018`
  is now proved:** `worstCaseExpectation_eq_dual` (Thm 4.2). `le_antisymm(weak, attainment)`:
  the weak `≤` is **proved** — `csSup_le → le_csInf → per-(Q,λ)` (η/(λ+1) trick) reducing to the
  **new** `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost_restrict` (the `Ξ`-restricted
  Lagrangian kernel — `integral_mono_ae` since the source marginal is `Ξ`-supported) + the
  empirical collapse + the OT ε-approx edge; the `≥`/attainment isolated to one edge.
  **⚠ STATEMENT CORRECTION:** the ball is now `wass1BallΞ` (`P(Ξ)`-restricted). The `ℝ`-valued
  (total) `ℓk` encoding drops the paper's `+∞`-off-`Ξ` / `P(Ξ)` restriction, so the raw
  `wass1Ball` equality is *unsound* for `Ξ ≠ univ` (an escaping `Q` beats the `Ξ`-dual);
  restricting the ball to `P(Ξ)` restores it — same fidelity-correction class as the Sinkhorn
  external-`ν` fix / `primal_feasible_radius_nonneg` (§6). `[BorelSpace X]` added for
  `IsClosed Ξ ⇒ MeasurableSet Ξ`.
- **First crack in the SDE frontier — ✅ `dynamic_eq_static_SB` PROVED (one direction),
  dependency-clean (2026-07); via a NEW KL data-processing inequality.** The Léonard dynamic⇄static
  SB equivalence: `le_antisymm(gluing-edge, DPI-direction)`. `staticSBValue ≤ schrodingerBridgeValueKL`
  is **genuinely proved** — the endpoint projection `e = (ω↦(ω₀,ω₁))` sends a feasible path law to
  a coupling in `Π(ρ₀,ρ₁)`, and coarse-graining can't increase KL, so `klReal(e#P‖endpointLaw) ≤
  klReal(P‖R)`. That inequality is the **new `ForMathlib.MeasureTheory.toReal_klDiv_map_le`** — the
  KL **data-processing inequality**, a *genuine Mathlib gap* (Mathlib has the KL chain rule but no
  DPI / f-divergence file), proved by conditional Jensen on the convex `klFun` (`ConvexOn.map_condExp_le`)
  + `toReal_rnDeriv_map` (pushforward RN-derivative = conditional expectation). Honest edges `hac`
  (`P ≪ R`), `hfin` (finite KL), `hne`; the gluing (path-reconstruction) `≤` isolated to `hglue`.
- **Soundness audit + fix (2026-07 — see [`JOURNAL.md`](JOURNAL.md)):** the four **under-specified**
  statements — `optimal_control_eq_grad_log` / `_sigma_grad_log` / `_grad_value` (HJB) and
  `optimal_coupling_factorization` — were **false as stated** (they equate `u*`/`dens*` to a *free*
  operator/function argument with no linking hypothesis; `grad := 0` refutes them). Worse,
  `optimal_control_eq_neg_grad_value` was **green but false** — it compiled only by `rw`ing through
  the false `grad_log` (Lean dependency audit carried `unsound dependency marker`): a genuine hidden `if False then True`.
  All four are now **reformulated to TRUE statements** and are **dependency-clean**: the real SDE/OT
  content (Hopf–Cole / product-form **verification** — the candidate is optimal — + optimizer
  **uniqueness**) is isolated to explicit non-vacuous edges (`hHC`/`hprodopt`, `huniq`), and the
  identity is *derived* (the `isolate-content-to-an-edge` posture used everywhere here). Blast
  radius was contained: `Drsb` uses `V` abstractly, so no card claim was ever affected.
- **`ChenGeorgiouPavon2021.energy_identity` is CLOSED** (Session 3): reshaped via the roadmap
  disintegration + KL chain rule, with the Girsanov content isolated to the explicit `hCM` edge
  (whose discrete Euler–Maruyama instance `energy_identity_euler_maruyama` is proved). The
  Session-9 theorem-target scaffold has likewise been converted from executable placeholders into
  hypothesis/structure **interfaces** (`EnergyIdentityTargets.lean` &c. carry **zero** open goals).

---