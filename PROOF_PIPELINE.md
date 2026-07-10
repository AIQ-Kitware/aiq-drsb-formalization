# PROOF_PIPELINE.md — ranking the remaining proofs & the ForMathlib upstreaming queue

Companion to [`AGENTS.md`](AGENTS.md) (orientation) and
[`formalization.yaml`](formalization.yaml) (per-declaration source map). This file is
the **proof-pass work plan**: it ranks every remaining placeholder by difficulty, says
**who should do it** (us vs. a Fable 5 agent), and defines the **ForMathlib pipeline**
of Mathlib-contributable lemmas that the paper libraries consume.

Update it as placeholders close. Keep the counts honest — because Lean comments never contain the
literal token (AGENTS.md §5 grep hygiene), a bare word-match is an exact inventory:

```bash
grep -rn --include=*.lean --exclude-dir=.lake --exclude-dir=.reference-clones --exclude-dir=reference -w sorry .
```

---

## −1. Projective-metric frontier (2026-07-10) — THE CURRENT WORK

> Sections 0–5 below describe the **DRSB card + duality** pass, which is **done**. They are
> retained as history. The live frontier is **Sinkhorn convergence via Birkhoff–Hopf**, upstream
> `ForMathlib` infrastructure that no card claim depends on. Full orientation: **[`STATUS.md`](STATUS.md)**.

**16 open goals.** Two parallel routes to the same theorem exist. **Decision (2026-07-10): finish the
Eveson–Nussbaum `PaperRoute`; *sequester* — do not delete — the Carroll weighted-average route.**
Step-by-step first moves are in [`STATUS.md`](STATUS.md).

| Route | Location | Open | Source paper | Priority |
|---|---|---|---|---|
| **Eveson–Nussbaum (1995)** cone route | `ForMathlib/…/BirkhoffHopf/PaperRoute/*` | 10 | `…/EvesonNussbaum1995_birkhoff_hopf.tex` | ⭐ **finish this** |
| Carroll (2004) weighted-average | `ForMathlib/…/BirkhoffHopf.lean` | 3 | `prose/distilled_literature/Carroll2004_birkhoff_contraction.tex` | sequester (keep as an alternate route; useful as a cross-check on the 2×2 core) |
| Franklin–Lorenz consumers | `ChenGeorgiouPavon2021/…/Compactness/FranklinLorenz.lean` | 2 | `…/FranklinLorenz1989_matrix_scaling.tex` | independent — attack any time |
| analysis tail | `ForMathlib/Analysis/ExpLogBounds.lean` | 1 | — | independent |

**The public seam is `positive_kernel_strict_birkhoff_contraction_coefficient`** — the only
Birkhoff–Hopf theorem `FranklinLorenz.lean` consumes, and the single goal both routes exist to
discharge. Every weighted-average theorem has **zero external consumers** (grep-verified), so
sequestering them into `BirkhoffHopf/WeightedAverageRoute.lean` is mechanical. Keep the shared
definitions and the proved core lemmas in `BirkhoffHopf.lean`.

**Dependency facts (Lean-verified, not eyeballed):**
- `positive_kernel_birkhoff_hopf_contraction` *looks* proved but its dependency audit reports the
  placeholder marker — the whole chain rests on the single open goal
  `finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound`, which in turn should
  reduce to `two_point_weighted_average_log_crossratio_contraction_of_crossratio_bound`.
- `PaperRoute/Assemble.lean`'s "public" theorem is `exact` of an open goal → **zero content**.
- Some `PaperRoute` goals are *already proved elsewhere* or near-trivial. Before proving anything
  there, check whether `BirkhoffHopf.lean` already has it: e.g.
  `positive_kernel_apply_hilbert_log_diameter_bound_of_apply_crossratio_bound` (proved, and
  **not** itself placeholder-backed) has the same statement as PaperRoute's
  `positive_kernel_apply_hilbert_log_diameter_bound_paper_route` (open). Likewise
  `quadrant_hilbert_coordScale_eq` / `_equivPerm_eq` are near-trivial (the scale factors cancel
  inside the log; the two `Set.range`s are literally equal).

**Difficulty (honest):** the two genuinely hard goals are Carroll **Step 3** (reduce *n* coordinates
to 2, by linear programming) and Eveson–Nussbaum **Lemma 3.11** (2-dimensional subspace reduction).
Everything else is elementary algebra/calculus. Carroll **Step 4** (the two-coordinate inequality) is
AM-GM plus two mean-value comparisons, and its analogue is **already proved** as
`PaperRoute/TwoByTwo.lean`'s `symmetricTwoByTwoPhi_le`.

**Vendoring: impossible.** The Hilbert projective metric and the Birkhoff–Hopf contraction exist
**nowhere in Lean** (swept 2026-07-10 — `SURVEY_LEADS.md` § Projective-metric frontier). PF exists
externally and sorry-free, but is **off the critical path** (our Sinkhorn existence proof avoided it).

---

## 0. The one insight that reorders everything

**The evaluation-card claims — the actual deliverables — need only the EASY half of
duality.** Each card asserts `𝔼_μ[V] ≤ (worst-case value)` for a *single* source `μ`
inside the ambiguity ball (`Drsb.wdrsb_cost_bound`, `Drsb.sdrsb_cost_bound`). That is:

```
𝔼_μ[V]  ≤  sup_{μ' ∈ ball} 𝔼_{μ'}[V]   (μ is in the sup set: le_csSup, needs BddAbove)
        ≤  inf_{λ≥0} dual(λ)             (WEAK duality, the always-true ≤ direction)
```

Neither step needs the research-grade **strong-duality `≥` (attainment)** direction —
the worst-case-measure / measurable-selection construction that is *not in Mathlib*
(AGENTS.md §6). So the tractable critical path to the cards is:

> **weak duality (≤)  ⇒  `BddAbove` of the ball's value set  ⇒  the two cost bounds.**

Everything labelled T4 below (strong duality `≥`, SDE/PDE, worst-case structure) is
NOT on that path. It is mathematically interesting and needed for the *strong-duality*
capstones, but the cards do not depend on it.

---

## 1. Difficulty tiers

| Tier | Meaning | Owner |
|---|---|---|
| **T0** | defeq / one rewrite; the content lives elsewhere | us (done inline) |
| **T1** | self-contained, ≲ few dozen lines of standard Mathlib; no missing theory | us |
| **T2** | real argument (sInf/sSup shifts, integrability, couplings) or needs a hypothesis added first; laborious but no missing theory | us, carefully |
| **T3** | genuine research-level Lean but self-contained enough to be a single target; from-scratch (Mathlib lacks the area) | **Fable 5** (or us with a big time budget) |
| **T4** | needs mathematics not in Mathlib (SDE/Girsanov/path measures, OT measurable selection, strong-duality attainment) | defer / make explicit as a named dependency / long-horizon |
| **TX** | blocked: the *statement* is wrong/under-specified — fix the statement before proving | us (statement work) |

---

## 2. Ranked placeholders of the card + duality pass (all closed)

*Historical. This pass is finished — the count here is 0. For the live inventory see §−1 and
[`STATUS.md`](STATUS.md).*

> **Soundness fix (2026-07 audit — see `JOURNAL.md`).** Four of the five former placeholders were
> **false as stated** (they equated `u*`/`dens*` to *free* operator/function arguments with no
> linking hypothesis; `optimal_control_eq_neg_grad_value` was **green but false**, surviving only
> by `rw`ing through the false `optimal_control_eq_grad_log` — a hidden `if False then True`).
> All four are now reformulated to TRUE statements: the genuine SDE/OT content (Hopf–Cole /
> product-form **verification** + optimizer **uniqueness**) is isolated to explicit non-vacuous
> edges, and the identity is *derived* — the same `isolate-content-to-an-edge` posture as the
> strong-duality equalities. Lean dependency audit on all four (+ `neg_grad_value`) is now clean
> (`propext/Classical.choice/Quot.sound`, no `unsound dependency marker`).

> **`energy_identity` closed (2026-07)** — this pass's last placeholder, and with it every card and
> duality result is proved and dependency-clean. `energy_identity` (CGP 4.19) was reshaped from a
> monolithic placeholder into a *proved* disintegration (`ROADMAP_ENERGY_IDENTITY.md`): KL invariance
> under a start-plus-centered-path measurable iso (`klDiv_map_measurableEquiv`) + the KL chain rule
> on the compProd factorizations (new `ForMathlib.toReal_klDiv_compProd_eq_add`) + the conditional
> term = control energy (`hCM`). The disintegration + finiteness + `hCM` hypotheses are honest
> structural/finite-energy edges (house pattern). `hCM` is the sole Girsanov content; its discrete
> Euler–Maruyama instance is the proved `energy_identity_euler_maruyama`. The **continuum** discharge
> of `hCM` (ROADMAP Phase 2) is blocked on Mathlib's missing Itô integral / Girsanov (grep-confirmed
> absent; both the density and discrete-limit routes need it) — the honest residual, an explicit
> edge, not a placeholder. Every library is proved.

> **Sequence-model Cameron–Martin/Kakutani milestone (2026-07-08, GPT-5.5 Thinking).**
> The iid Gaussian sequence-coordinate staging theorem is now proved and `lake build` green:
> `stdSeqGaussian` prefix marginals, shifted Gaussian density representations, prefix
> local-density and L² density-process bounds, `ℓ²` absolute continuity,
> `klDiv_stdSeqGaussian_map_add_of_summable`, and the nonsummable/infinite-KL converse.
> `ChenGeorgiouPavon2021.energy_identity_sequenceModel` is a thin, honest wrapper for the
> sequence model. The remaining frontier is path-level Wiener/SDE transport (M4b), not more
> sequence-model KL plumbing.
>
> **Finite M4b/Wiener-dyadic checkpoint (2026-07-08, GPT-5.5 Thinking).** The finite-dimensional
> Wiener bridge is now green: dyadic increment laws, normalization/scaling, independence/product
> assembly, finite shifted-grid densities, and finite dyadic absolute continuity. The continuum
> closure is intentionally represented by explicit interfaces (`HasDyadicKLExhaustion` and
> path-space AC for the CM shift), because the current ambient `RealPath := ℝ → ℝ` is too broad
> for the discarded dyadic-generator equality.
>
> **Interval-path frontier seam (2026-07-08, GPT-5.5 Thinking).** The next carrier has been staged
> in `ChenGeorgiouPavon2021.Continuum.IntervalPath` as `IntervalPath := [0,1] → ℝ`, with proved low-risk finite
> projection lemmas: measurability of normalized interval dyadic increments, one-sided generated
> sigma-algebra bound, additivity under deterministic shifts, shifted finite-dimensional Wiener law,
> and the finite dyadic KL identity. The hard continuum facts are still interfaces:
> `HasIntervalDyadicGeneration 𝓜`, `HasIntervalDyadicKLExhaustion`, and full path-space CM
> quasi-invariance/AC for the eventual continuous anchored carrier.
>
> **Module split checkpoint (2026-07-08, GPT-5.5 Thinking).** Before adding the project-wide
> theorem-skeleton progress bar, the former CGP monolith was split and the larger proved theorem
> libraries were split as well. `ForMathlib.MeasureTheory.GaussianCameronMartin` is an aggregate
> over sequence-product, energy, finite-KL, infinite-KL, density, and absolute-continuity modules.
> `ChenGeorgiouPavon2021.Continuum.WienerDyadic` is an aggregate over concrete Wiener grid,
> measure, projective reduction, finite-increment algebra, RealPath transport, and finite-shift
> assembly modules. `Continuum.Closure` and `SocOt` are likewise topic-split. Aggregate imports
> remain stable; direct-file checks require prebuilt imports, so use `dev/check_cgp_module_split.sh`.
>
> **Progress-bar policy.** The future global placeholder count should measure only missing mathematics
> needed to discharge final DRSB assumptions. Do not put placeholders on final integration lemmas that
> merely chain proved theorem targets; those lemmas should stay as assembly from explicit inputs
> until the mathematical targets are proved.

> **Status refresh (2026-07).** All four DRSB capstones (`Drsb.{wdrsb,sdrsb}_cost_bound`
> and `Drsb.{wdrsb,sdrsb}_strong_duality`) are **proved** — `Drsb` is proved. The
> paper-level strong-duality *equalities* (`BlanchetMurthy2019.wdro_strong_duality`,
> `GaoKleywegt2023.strong_duality_thm1`, `WangGaoXie2023.strong_duality`) are likewise
> proved, each `le_antisymm(weak, attainment)` with the research-grade `≥` isolated to one
> explicit **OT-attainment hypothesis** (not a placeholder). `WangGaoXie2023.primal_feasible_iff`
> is resolved (see below). The **finite-Sinkhorn-scaling existence** (`SinkhornScaling`, T3)
> is now **PROVED** (dependency-clean; see below). `dataDriven_strongDuality_cor2i` is also now
> PROVED (house pattern; see §T4 note). `MohajerinEsfahaniKuhn2018.worstCase_program`
> (Thm 4.4) and `worstCase_exists` (Cor 4.6) are also PROVED (constructive worst-case law +
> one edge each). `GaoKleywegt2023.{dataDriven_worstCase_cor2ii, worstCase_structure_cor1}`
> (Cor 2(ii)/1(ii), eqs. 29/27) are also now PROVED (same house pattern; see §T4 note) —
> **`GaoKleywegt2023` is now proved**. `MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual`
> (Thm 4.2) is likewise PROVED (see §T4 note) — **`MohajerinEsfahaniKuhn2018` is now proved
> too**. `ChenGeorgiouPavon2021.dynamic_eq_static_SB` (Léonard dynamic⇄static SB) is now PROVED in
> one direction via the **new KL data-processing inequality** (see §T4 note + §3). The **5** remaining
> placeholders are all in `ChenGeorgiouPavon2021`: `energy_identity` (continuous Girsanov) and four
> **under-specified** HJB/factorization statements (`optimal_control_eq_grad_log` / `_sigma_grad_log`
> / `_grad_value`, `optimal_coupling_factorization` — each equates `u*`/`dens*` to an *arbitrary
> passed-in operator* with no linking hypothesis, so they need statement work, not a proof).

### On the card critical path (do these first)

| Decl | Tier | What it needs | Notes |
|---|---|---|---|
| `ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range` | ✅ **PROVED** (dependency-clean) | — | **`hbddP` was never an edge.** A function bounded above has bounded-above expectations over any set of probability measures integrating it; and a dual over `lam ≥ 0` already asserts `BddAbove (range f)` as its `lam = 0` conjugate. Deleted `hbddP` from `Drsb.wdrsb_strong_duality`, `GaoKleywegt2023.{strong_duality_thm1, dataDriven_strongDuality_cor2i}`, `BlanchetMurthy2019.{wdro_strong_duality, _dualFn}`; replaced by the weaker checkable `BddAbove (range V)` in the two `0 < lam` duals (`Drsb.sdrsb_strong_duality`, `WangGaoXie2023.strong_duality`). Four remain, all on worst-case-*structure* theorems (GK cor1/cor2ii, MEK worstCase_program/_exists), which carry no boundedness hypothesis to derive from. |
| `Drsb.wdrsb_cost_bound` | ✅ **PROVED** (dependency-clean, **edge-free**) | — | **The WDRSB evaluation-card claim, discharged with NO optimal-transport edge.** Composes the weak-duality kernel + `sqCost` symmetry + a *near-optimal* plan (`ForMathlib.OT.exists_coupling_couplingCost_lt`) + `η ↓ 0`. The old `hOT` attainment edge is **deleted**: `W₂²` is an `sInf`, so it never yields a plan of cost `≤ ε`, only `< ε + η` — and the limit suffices. Cost-integrability is likewise a theorem, from finite second moments (`integrable_normSq_sub_of_mem_couplings`). Remaining hypotheses are regularity + `HasSecondMoment μ/p₀`. `wdrsb_cost_bound_of_ot_edge` is the machine-checked receipt that `{hOT, hp2} ⊢ {hμ2, hp2}`, so nothing was strengthened. Lean dependency audit = propext/Classical.choice/Quot.sound only. |
| `GaoKleywegt2023.weak_duality_prop1` | ✅ **PROVED** (dependency-clean) | — | The general Wasserstein `v_P ≤ v_D`. `csSup_le → le_csInf → per-(μ,λ)` bound from the kernel + coupling ε-approx; the Moreau–Yosida `Φ`↔sup-form negation is the unconditional `Real.sSup_neg`. Under honest edges (`hfeas`/`hbdd`/`hφint`/`hΨμ`/`hOT`). |
| `GaoKleywegt2023.strong_duality_thm1` | ✅ **PROVED** (dependency-clean) | — | `v_P = v_D` via `le_antisymm (weak_duality_prop1) (attainment)`. The `≥` is a single explicit **attainment edge** `hattain` — this ISOLATES the whole strong-duality gap to the one OT measurable-selection fact (§6). |
| `Drsb.sdrsb_cost_bound` | ✅ **PROVED** (dependency-clean, **edge-free**) | — | **The SDRSB evaluation-card claim, discharged with NO transport, attainment or disintegration edge.** Ball membership → `ForMathlib.OT.exists_isSinkhornPlan_of_mem_sinkhornBall` (a theorem now that `Wkappa` infimises the `ℝ≥0∞` `sinkhornObjectiveENN`, so singular couplings score `⊤` not `0`) → `Drsb.hasSinkhornDisintegration_of_isSinkhornPlan` (`condKernel` + KL chain rule) → `sdrsb_cost_bound_of_disintegrations` (Donsker–Varadhan + `η ↓ 0`). Surviving hypotheses: `hV`, `HasSecondMoment p₀/μ`, and `h_exp`/`hI_lp` which constrain the **dual**, not the transport. `sdrsb_cost_bound_of_attained_disintegration` is the receipt that the old attained edge implies the new one. Dual over `0<lam` (the `lam=0` `logPartition` is junk — ess-sup convention unencoded). Ball uses the audit-fixed external `ν`. |
| `Drsb.hasSinkhornDisintegration_of_isSinkhornPlan` | ✅ **PROVED** (dependency-clean) | — | **The SDRSB disintegration edge, discharged.** On `[StandardBorelSpace X] [Nonempty X]`, a `ForMathlib.OT.IsSinkhornPlan` (coupling + `≪ p₀⊗ν` + finite `klDiv` + budget) *builds* the conditional family: `Measure.condKernel` + `Measure.integral_compProd` + `toReal_klDiv_compProd_eq_integral` at `η := Kernel.const X ν`. The a.e. slice facts (`P x ≪ ν`, integrable `llr`) come from `klDiv_ne_top_iff` on the a.e.-finite slices (`ae_klDiv_kernel_ne_top`). **Prerequisite:** `sinkhorn_weak_duality_kernel`/`IsSinkhornDisintegration` weakened from `∀ x` to `∀ᵐ x ∂p₀` — a `condKernel` is only determined a.e. |
| `ForMathlib.OT.exists_isSinkhornPlan_of_mem_sinkhornBall` | ✅ **PROVED** (dependency-clean) | — | **Ball membership yields a near-optimal finite-entropy plan.** Was the `hplan` hypothesis; became a theorem once `Wkappa` was redefined over the `ℝ≥0∞` objective. `0 < κ` converts finiteness of `κ·KL` into finiteness of `KL`; `klDiv_ne_top_iff` then gives `≪`. `ForMathlib.OT.mem_sinkhornBall_reference` certifies the ball is nonempty, so nothing downstream is vacuous. |
| `WangGaoXie2023.strong_duality` | ✅ **PROVED** (dependency-clean) | — | `V = V_D` via `le_antisymm`: the `≤` half composes `sinkhorn_weak_duality_kernel` (per-point DV integrated over `p₀`) + `le_csInf`; the `≥` half is the single **attainment+disintegration edge** `hSinkAll`/`hattain` (§6). The Sinkhorn analogue of the WDRO linchpin. |

**Sinkhorn weak-duality kernel — ✅ DONE** (`WangGaoXie2023.sinkhorn_weak_duality_kernel`,
dependency-clean; the second card `sdrsb_cost_bound` composes it). The roadmap below is how it
was built (kept for reference). The audit fixed the ball to use the external reference `ν`
(`sinkhornBall μ̂ ν κ ε`; ball & dual now share `ν`). The kernel to prove — the entropic
analogue of `expect_le_dualIntegrand_add_lam_couplingCost` — is: for `γ ∈ couplings p₀ μ`
and `λ ≥ 0`,
`expect μ V ≤ λ·sinkhornObjective(γ) + expect p₀ (logPartition ν sqCost V κ λ ·)`.
Proof plan, all pieces confirmed to exist:
1. Disintegrate `γ = p₀ ⊗ₘ γ_x` (Mathlib `Measure.condKernel`, standard-Borel `X`).
2. Per nominal `x`, the proved Gibbs/DV bound
   (`ForMathlib…integral_le_klDiv_add_log_integral_exp` / `logPartition_eq_gibbs_sSup`)
   gives `𝔼_{γ_x}[V] ≤ λ·𝔼_{γ_x}[c] + λκ·KL(γ_x‖ν) + logPartition(x)`.
3. Average over `p₀` via the KL chain rule (`Mathlib…klDiv_compProd_eq_add`); the
   *integral form* `KL(p₀⊗ₘγ_x ‖ p₀⊗ₘ ν) = ∫ KL(γ_x‖ν) dp₀` is a Mathlib TODO — supply it
   as a ForMathlib lemma (a genuine contribution).
4. Then compose exactly as `wdrsb_cost_bound` (`le_csInf` + `sinkhornObjective ≤ ε`).
NB the global single-DV shortcut only yields a *weaker* bound (Jensen: `log 𝔼 ≥ 𝔼 log`),
so the disintegration is unavoidable. A substantial but well-specified proof — a strong
Fable ticket or a focused session.

### Contributable-to-Mathlib, standalone (ForMathlib queue — see §3)

| Decl | Tier | What it needs |
|---|---|---|
| `ForMathlib.sinkhorn_potentials_exist` / `matrix_scaling_exists` | ✅ **PROVED** (dependency-clean) | Done. Mathlib has **neither** Brouwer nor Birkhoff/Hilbert-metric contraction (grep-verified), so proved via **log-domain convex minimization** of `ψ(b)=∑ pᵢlog(∑ Gᵢⱼbⱼ)−∑ qⱼlog bⱼ` over the open simplex: boundary blow-up `−qⱼlog bⱼ→+∞` gives compactness (EVT, no coercivity lemma), the marginal equations come from 1-D directional derivatives along `eⱼ−eₖ` (`IsLocalMin.hasDerivAt_eq_zero`), and **mass conservation `∑p=∑q` kills the Lagrange multiplier**. `matrix_scaling_exists` staged for Mathlib upstreaming. `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` delegates. |

### Cheap once a dependency or a hypothesis lands (us)

| Decl | Tier | What it needs |
|---|---|---|
| `ChenGeorgiouPavon2021.schrodingerBridge_KL_eq_SOC` | **T2** | `sInf`-shift `inf{a+g(u)} = a + inf g` using `energy_identity` + `Feasible ⇒ initialMarginal = ρ₀`. Compiles atop the (T4) `energy_identity` sibling — concentrates debt like `wdro_strong_duality_dualFn` did. |
| `ChenGeorgiouPavon2021.optimal_control_eq_neg_grad_value` | **T2/TX** | blocked by *abstract* `grad`: `grad(−V) ≠ −grad V` without linearity. Add a `grad` additivity/negation hypothesis (or derive from `optimal_control_eq_grad_log` + that hyp), then T1. |
| `Drsb.wdrsb_strong_duality` | ✅ **PROVED** | — | Delegates to `GaoKleywegt2023.strong_duality_thm1` (`sqCost` symmetric ⇒ `Lc = −Φ`); the WDRSB capstone. |
| `Drsb.sdrsb_strong_duality` | ✅ **PROVED** | — | Re-export of `WangGaoXie2023.strong_duality`; `Drsb` is now proved. |

### Statement bug — ✅ RESOLVED

| Decl | Tier | Resolution |
|---|---|---|
| `WangGaoXie2023.primal_feasible_iff` → **`primal_feasible_radius_nonneg`** | ~~TX~~ ✅ | The naive `Nonempty ↔ 0 ≤ ε` is **false** for the raw `Wkappa` ball (`Wkappa κ ν μ̂ μ̂ > 0` for non-degenerate `μ̂`; the true nonemptiness threshold is the free energy `−κ·𝔼[log ∫e^{−c/κ}dν] ≥ 0`, generically `> 0`). Restated & **proved** as the honest **necessity** half — `0 ≤ κ ⇒ (Nonempty → 0 ≤ ε)` — from `Wkappa ≥ 0`. The paper's full `↔ ρ ≥ 0` holds only for the ρ̄-reformulated KL-ball; its sufficiency direction is the worst-case-measure **attainment** edge (T4, deferred). Docstring records the derivation. |

### T4 — research-grade / not-in-Mathlib (defer or make explicit as a named dependency)

**Worst-case *structure*** — ✅ **ALL PROVED** (0 remaining). The last one,
`MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` (Thm 4.2), landed 2026-07 (see note below).

> **`GaoKleywegt2023.dataDriven_worstCase_cor2ii` (Cor 2(ii), eq. 29) — PROVED (2026-07,
> house pattern, dependency-clean).** The data-driven worst case is a `≤ N+1`-atom transport of the
> empirical nominal. Because this corollary pins the *exact* atom structure (unlike a bare
> existence), the §5 trap is acute: the structured optimizer `μ*` may **not** be a hypothesis.
> The honest decomposition takes as inputs only the genuinely-weaker **extremal ingredients** a
> full OT measurable-selection would extract from `hexists` — the split index `i₀`, weight
> `p0 ∈ [0,1]`, the per-point argmin atoms `ξstar`/`ξbarstar` (conditions (v)/(vi); argmin
> *existence* is an extreme-value fact strictly weaker than the conclusion) — plus two
> ingredient-level scalar edges: a **feasibility budget** `hbudget` (argmin-transport cost `≤ δ`,
> the analogue of Esfahani–Kuhn's `(1/N)Σ‖q‖ ≤ ε`) and the **attainment `≥` edge** `hattain`
> (the atom-value formula dominates `droValue`, the analogue of `worstCase_exists`'s `hval`).
> Everything else is **proved**: `μ*` is built as the explicit `K = 2` weighted-Dirac
> double-sum, shown a probability measure, shown `∈ ambiguitySet` via the explicit transport
> plan (cost `≤ δ` through `ForMathlib.OT.otCost_le_couplingCost`), its `Ψ`-expectation computed
> in closed form, and the `≤` half of attainment is `le_csSup` — so `hattain` supplies only the
> `≥`. The measure is finally rewritten into the printed eq. (29) split form. Exactly the
> `le_antisymm(constructive, one attainment edge)` posture of `worstCase_exists`/`strong_duality_thm1`.
> Reuses local copies of `isProbabilityMeasure_wsum`/`integral_wsum`/`map_wsum` (verbatim from
> the sibling) — both consumers now exist, so promoting these three to `ForMathlib.OT` is the
> natural small dedup follow-up. `MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` (Thm 4.2,
> the duality *equality*) remains the last open worst-case-structure target.

> **`GaoKleywegt2023.worstCase_structure_cor1` (Cor 1(ii), eq. 27) — PROVED (2026-07,
> house pattern, dependency-clean).** The general-`ν` sibling of `cor2ii`: the worst case is a
> **2-map transport** `μ* = pstar·T̄#ν + (1−pstar)·T*#ν`. Same §5-safe decomposition — the
> structured optimizer is not hypothesized; the inputs are only the mixture weight `pstar ∈ [0,1]`
> and the two **measurable** transport maps `Tbar`/`Tstar` that are `ν`-a.e. argmins (`hargmin`),
> plus honest **regularity edges** (`Ψ` and the cost integrable along each transport — required
> because `c`/`Ψ` carry no standing measurability, unlike the finite-Dirac `cor2ii` where
> `integral_dirac` needs none) and the two content edges (feasibility budget + attainment `≥`).
> Proved: `μ*` built as the mixture (probability measure via `Measure.map_apply` +
> `measure_univ`), `∈ ambiguitySet` via the explicit plan `pstar·(T̄,id)#ν + (1−pstar)·(T*,id)#ν`
> (2nd marginal `= ν` because `snd∘(T,id)=id` and `Measure.map_id`; cost `≤ δ` via
> `otCost_le_couplingCost`), `Ψ`-expectation `integral_map`'d to the mixture value, `≤` half of
> attainment by `le_csSup`. The eq. (27) measure form is `rfl`. **`GaoKleywegt2023` is now
> proved.** (The four `Measure.map`/`smul`/`add` pushforward manipulations here are the
> reusable pattern if `worstCaseExpectation_eq_dual`'s attainment measure is built the same way.)

> **`MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` (Thm 4.2, eq. 12b) — PROVED
> (2026-07, house pattern, dependency-clean) + STATEMENT CORRECTION.** The data-driven worst-case
> duality *equality* `sup_{Q} 𝔼_Q[ℓ] = inf_{λ≥0}{λε + (1/N)Σᵢ sup_{ξ∈Ξ}(ℓ(ξ)−λ‖ξ−ξ̂ᵢ‖)}`.
> **Fidelity fix:** the paper's ambiguity set is over `P(Ξ)` and its `−ℓk` are *proper* convex
> (`= +∞` off `Ξ`); the `ℝ`-valued (total) `ℓk` encoding drops that, so the raw `wass1Ball` (no
> `Ξ`-support) is too large — for `Ξ ≠ univ` an escaping `Q` makes `𝔼_Q[ℓ]` exceed the `Ξ`-dual
> and the equality *fails*. Corrected to the `P(Ξ)`-restricted ball `wass1BallΞ` (same class of
> statement correction as the Sinkhorn external-`ν` fix / `primal_feasible_radius_nonneg`; the
> proved `worstCase_program`/`worstCase_exists` use `wass1Ball` and are unaffected — their laws
> are `Ξ`-supported anyway). **Proof:** `le_antisymm(weak, attainment)`. Weak `≤` is PROVED —
> `csSup_le → le_csInf → per-(Q,λ)` (via `le_of_forall_pos_le_add`, the `η/(λ+1)` trick of
> `weak_duality_prop1`) reduces to the **new** `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost_restrict`
> (the `Ξ`-restricted Lagrangian kernel — needs `Q ∈ P(Ξ)`, supplied by the ball, so its conjugate
> `sup` lands on `Ξ`) composed with the empirical collapse `𝔼_{P̂}[g] = (1/N)Σᵢ g(ξ̂ᵢ)` and the OT
> coupling ε-approx edge `hOT`; integrability against `P̂` is automatic (finite Dirac sum). The
> `≥`/attainment is isolated to one explicit edge `hattain`, as everywhere. `[BorelSpace X]` added
> for `IsClosed Ξ ⇒ MeasurableSet Ξ`. **`MohajerinEsfahaniKuhn2018` is now proved.**

> **`MohajerinEsfahaniKuhn2018.worstCase_program` (Thm 4.4, eq. 13) — PROVED (2026-07,
> house pattern, dependency-clean).** The `≥` direction (`sup(program) ≤ droValue`) is proved
> **constructively, proved**: every feasible `(α,q)` gives the explicit discrete law
> `Q = (1/N) Σᵢₖ αᵢₖ δ_{ξ̂ᵢ − qᵢₖ/αᵢₖ}`, shown to lie in the ε-Wasserstein ball via an
> explicit transport plan (cost `(1/N)Σ‖qᵢₖ‖ ≤ ε`, using the new reusable
> `ForMathlib.OT.otCost_le_couplingCost`) and to satisfy `𝔼_Q[ℓ] ≥ extremalObjective`
> (`ℓ = maxₖ ℓₖ ≥ ℓₖ`) — **no measurable selection**, just finite data-point perturbations.
> The `≤` direction (every ball measure ≤ some extremal config — Thm 4.4's OT content) is
> isolated to one explicit edge `hdom`, same posture as the strong-duality attainment edges.
> Reusable finite-measure helpers (`isProbabilityMeasure_wsum`, `integral_wsum`, `map_wsum`
> for weighted Dirac double-sums) + the shared construction lemma `worstCaseLaw_ball_ge`
> landed in the file — promotable to `ForMathlib` if `GaoKleywegt2023.dataDriven_worstCase_cor2ii`
> (same construction) is taken up next. **`worstCase_exists` (Cor 4.6) is likewise PROVED**
> via `worstCaseLaw_ball_ge` + an explicit attainment edge `hattain` (the extreme-value
> argument `hExist` would supply): the constructed `Q` is in the ball and, with `hattain`,
> attains `droValue`.

> **`dataDriven_strongDuality_cor2i` — PROVED (2026-07, house pattern).** The data-driven
> strong-duality *equality* `v_P = empiricalDual` (eq. 28) is now discharged, dependency-clean:
> it is the general `strong_duality_thm1` (`v_P = v_D`, weak-`≤` from the ForMathlib kernel +
> the isolated attainment edge `hattain`) composed with the **new proved reduction**
> `GaoKleywegt2023.dualValue_eq_empiricalDual` (`v_D = empiricalDual` for the empirical `ν`,
> a direct integral-against-empirical-measure computation under `[MeasurableSingletonClass X]`).
> So this is the same `le_antisymm(weak, attainment)` posture as every other strong-duality
> equality here — the `≥` isolated to one explicit hypothesis, not a placeholder. A 2026-07-03
> survey pass (flow-sinkhorn / lean-stat-learning-theory / Mathlib) confirmed **no external
> Lean library** supplies a finite Kantorovich/LP strong duality to discharge `hattain`
> outright; the finite worst-case is the explicit ≤(N+1)-atom construction of `cor2ii` (below,
> still open) — that, not an import, is what would make it fully proved.

**SDE / PDE / path-measure** (no Mathlib SDE theory):
`ChenGeorgiouPavon2021.{energy_identity (Girsanov), optimal_control_eq_grad_log,
optimal_control_eq_sigma_grad_log, optimal_control_eq_grad_value (HJB),
optimal_coupling_factorization}`. (`dynamic_eq_static_SB` was in this block — now PROVED in
one direction, see below.)

> **`dynamic_eq_static_SB` (Léonard dynamic⇄static SB) — PROVED one direction (2026-07,
> house pattern, dependency-clean) via a NEW KL data-processing inequality.** `le_antisymm(hglue, DPI)`.
> The `staticSBValue ≤ schrodingerBridgeValueKL` direction is **genuinely proved**: the endpoint
> projection `e = (ω↦(ω₀,ω₁))` sends every feasible path law `P` to a coupling `e#P ∈ Π(ρ₀,ρ₁)`
> (marginals from feasibility via `Measure.map_map`), and *coarse-graining cannot increase
> relative entropy* — `klReal(e#P ‖ endpointLaw) ≤ klReal(P ‖ R)` — by the **new**
> `ForMathlib.MeasureTheory.toReal_klDiv_map_le` (§3). Honest edges `hac` (`P ≪ R`), `hfin`
> (finite KL), `hne` (nonempty). The reverse (**gluing** reference bridges onto a coupling to
> reconstruct a path law of equal KL — Léonard Prop 2.3, path reconstruction absent from Mathlib)
> is isolated to the single edge `hglue`. This is the first genuine crack in the SDE frontier:
> a unproved T4 theorem turned into `le_antisymm(edge, proved)`, and it forced a real Mathlib
> contribution (KL DPI). **NB the four `optimal_control_*` / `optimal_coupling_factorization`
> placeholders are structurally different — UNDER-SPECIFIED** (each concludes `u* = <expr in an
> arbitrary passed-in `grad`/`lam`/`φ`/`p`>` with no hypothesis linking them; false for e.g.
> `grad := 0`). Honestly closing them needs the SDE *verification theorem* as an added hypothesis
> (statement work / TX), not a proof against the current statements. `energy_identity`'s discrete
> layer is proved (below); the continuous form needs Girsanov.

> **`energy_identity` — CLOSED (2026-07, chain-rule split; complete).** The continuous
> `energy_identity` (CGP (4.19)) is no longer a placeholder: it is proved by disintegrating both path
> laws over the initial coordinate and applying the KL chain rule, with the Girsanov content
> isolated to the explicit `hCM` (Cameron–Martin) edge (ROADMAP Phases 0–1). Its continuum edge is
> blocked on Mathlib's missing Itô integral (ROADMAP Phase 2). Separately, its
> **Euler–Maruyama / Gaussian discretization — the quantity the DRSB card actually
> measures (AGENTS §3) — is proved, dependency-clean**:
> `ChenGeorgiouPavon2021.energy_identity_euler_maruyama` delegates to
> `ForMathlib.MeasureTheory.klDiv_emShift_eq_emEnergy`, which shows
> `(KL(P^u ‖ P^0)).toReal = ∑ₖ Δt·½‖u_k‖²` (the discrete control energy) built on the
> **vendored** Cameron–Martin identity `klDiv_stdGaussian_map_add` (`KL(N(·+h) ‖ N) = ½‖h‖²`)
> from `mrdouglasny/gibbs-variational` (Apache-2.0, commit `75e08d8`; see
> `ForMathlib/MeasureTheory/GaussianEntropy.lean` header + README "Vendored / adapted external
> proofs"). **The single remaining edge** between this proved discrete identity and the
> continuous `energy_identity` is the **`Δt → 0` Euler–Maruyama → SDE limit** (a documented
> OT/SDE edge; needs limits of path-measure KL as the mesh refines). That is the honest
> next target here — the algebraic/Girsanov content per mesh is done.

These are correct as *statements* (that was the first pass). Proving them means either
building the missing Mathlib theory (a multi-month effort, its own upstream program) or
recording them as `dependency`s with provenance. **Do not spend Fable cycles here yet.**

---

## 3. The ForMathlib pipeline (Mathlib-contributable proofs)

`ForMathlib/` is the staging library for **paper-agnostic** results — genuine Mathlib
gaps, proved here first, then proposed upstream. The paper libraries import them; only
these are candidates for a Mathlib PR. Proven template: the Donsker–Varadhan port.

The **classical-theorem chains** under DRSB — the DKPS-style dependency DAGs (Chain 1
convex/Kantorovich duality, Chain 2 entropic/Gibbs, Chain 3 Perron–Frobenius/Sinkhorn,
Chain 4 SDE), each link's grep-verified Mathlib gap status, and **search terms for
surveying existing AI/human Lean proofs** — are in **[`FOUNDATIONS.md`](FOUNDATIONS.md)**.

| ForMathlib item | Status | Mathlib gap? | Tier | Owner |
|---|---|---|---|---|
| `MeasureTheory.DonskerVaradhan` (DV inequality + Gibbs variational identity) | ✅ proved | yes — only `Measure.tilted` exists | (done) | — |
| `MeasureTheory.Normalization.isProbabilityMeasure_inv_univ_smul` | ✅ proved | yes — only `tilted_const'` indirectly | T0 | — |
| `OptimalTransport.WeakDuality.expect_le_dualIntegrand_add_lam_couplingCost` — the OT-DRO **per-coupling Lagrangian bound** (Wasserstein `≤` kernel) | ✅ **proved** (ported from `reference/V4.lean`, generalized to arbitrary cost `c`) | yes — no Kantorovich/Wasserstein duality in Mathlib at all | (done) | — |
| `OptimalTransport.WeakDuality.expect_le_dualIntegrand_add_lam_couplingCost_restrict` — the **Ξ-restricted** Lagrangian bound (`P(Ξ)`-supported source ⇒ conjugate `sup` over `Ξ`) | ✅ **proved** (dependency-clean; same proof, `integral_mono_ae` since the pointwise bound holds `π`-a.e. on the `Ξ`-supported marginal) | yes — the entropic/Ξ-restricted Kantorovich variant | (done) | — |
| `OptimalTransport.WeakDuality.expect_kernel_le_lam_sinkhornBudget_add_logPartition` — the **entropic (Sinkhorn) weak-duality kernel** (per-point DV integrated over `p₀`) | ✅ **proved** (dependency-clean; the entropic analogue, paper-agnostic) | yes — no entropic-DRO duality in Mathlib | (done) | — |
| `LinearAlgebra/Matrix.SinkhornScaling` — finite **Sinkhorn / matrix scaling** existence (`matrix_scaling_exists` + `sinkhorn_potentials_exist`, with mass-conservation hyp) | ✅ **proved** (dependency-clean; log-domain min, no Brouwer/Birkhoff needed) | yes — Sinkhorn scaling absent from Mathlib | T3 | (done) |
| `MeasureTheory.KLDataProcessing.toReal_klDiv_map_le` — **data-processing inequality for KL** (`KL(g#μ‖g#ν) ≤ KL(μ‖ν)`) | ✅ **proved** (dependency-clean; conditional Jensen on `klFun` + `toReal_rnDeriv_map` = condExp of the RN-derivative + `integral_condExp`) | **yes — Mathlib has the KL chain rule but no DPI / f-divergence monotonicity** | T3 | (done) |
| Chain 1 roots (Sion minimax, Fenchel conjugate/duality, Kantorovich) · Chain 3 (Perron–Frobenius) | 🔜 queued (see FOUNDATIONS.md) | ❌ absent | L–XL | survey → Fable |

**Extraction rule.** When a placeholder is a *general* fact (no DRSB/paper-specific
objects), give it a clean Mathlib-idiom statement, prove it in `ForMathlib/`, and have
the paper library `import` + consume it (as `WangGaoXie2023.exists_worstCase_gibbs` now
consumes `isProbabilityMeasure_inv_univ_smul`). That is the pipeline: paper placeholder →
recognized general lemma → ForMathlib proof → upstream PR.

**Proposed next extractions (statements to stage):**

- `OptimalTransport.WeakDuality`: for feasible `μ` (`otCost c μ ν ≤ δ`), a coupling
  `π ∈ Π(μ,ν)`, and `λ ≥ 0`, `𝔼_μ[f] ≤ 𝔼_ν[φ_λ] + λ·𝔼_π[c]` where
  `φ_λ(y) = sup_x (f x − λ c x y)`; then the `inf`/`sup` assembly. The per-coupling
  bound is *already proved* in `reference/V4.lean` against the reference vocabulary —
  port it to `ForMathlib.OT` vocabulary (`expect`, `couplings`, `couplingCost`).
- `SinkhornScaling`: `∃` positive scalings solving the discrete Schrödinger system
  (`sinkhorn_potentials_exist`'s conclusion), stated for a positive kernel on a
  `Fintype`. Build on `Mathlib.Analysis.Convex.Birkhoff` / `DoublyStochasticMatrix`.

---

## 4. Fable 5 hand-off protocol

> **Policy update (2026-07, user directive): do NOT hand off to Fable.** The remaining
> work is to be done in-context by decomposing each target into its natural subproblems and
> proving step-by-step (with the thinking budget turned up). This section is retained only
> as a description of what a *self-contained T3 target* looks like — the same decomposition
> discipline applies whether or not a separate agent does it.

Historically we would reach for a **Fable 5 agent** (`Agent` tool with `model: fable`, or a
`Workflow` with a Fable stage) on **T3** targets — self-contained, hard, from-scratch. Not
on T4 (missing theory: it will thrash) and not on T0–T2 (we do those cheaper).

A good Fable task spec is a **single theorem** with:
1. the exact Lean statement already in the file (Fable fills the body only);
2. all dependencies proved & imported (list them);
3. a proof sketch / the reference proof if one exists (e.g. `reference/V4.lean`);
4. the acceptance check: `lake env lean <File>.lean` exits 0 with only complete
   `warning`s for *other* decls; the target emits none;
5. isolation: run in a `git` worktree (`isolation: "worktree"`) if it will edit files
   that another agent also touches.

**Ticket status:**
- **F1 — `ForMathlib.OptimalTransport.WeakDuality`** (unblocked the cards): ✅ **DONE by us**
  — `expect_le_dualIntegrand_add_lam_couplingCost` ported/generalized and
  `GaoKleywegt2023.weak_duality_prop1` assembled, both dependency-clean.
- **F2 — `ForMathlib.…SinkhornScaling`** (`matrix_scaling_exists` + `sinkhorn_potentials_exist`):
  ✅ **DONE by us, no Fable** (dependency-clean). The intended fixed-point/Birkhoff route was
  infeasible (Mathlib has **neither** Brouwer nor the Birkhoff/Hilbert-metric contraction),
  so proved instead by **log-domain convex minimization** over the open simplex — existence
  by boundary blow-up + EVT (no coercivity lemma), scaling equations by 1-D directional
  derivatives, Lagrange multiplier killed by mass conservation. `matrix_scaling_exists` is a
  clean general lemma staged for Mathlib upstreaming.

---

## 5. Recommended execution order

**✅ Steps 1–4 below are DONE** (weak duality → both cost bounds → all strong-duality
equalities → `primal_feasible` resolved). Remaining live work is step 5.

1. ~~**us, now:**~~ ✅ landed the T0/T1/T2 wins — `schrodingerBridge_KL_eq_SOC`,
   `optimal_control_eq_neg_grad_value` (hyp fix), the two ForMathlib skeletons.
2. ~~**us, statement work:**~~ ✅ `weak_duality_prop1` side-hypotheses added and proved;
   `primal_feasible_iff` re-derived from prose → `primal_feasible_radius_nonneg` (necessity,
   proved; sufficiency deferred to the ρ̄-ball attainment edge).
3. ~~**Fable:**~~ ✅ F1 (weak-duality → cards) and F2 (`SinkhornScaling`) **both done by us,
   no Fable** — F2 dependency-clean via log-domain minimization (Brouwer/Birkhoff absent).
4. ~~**us:**~~ ✅ `Drsb.{wdrsb,sdrsb}_cost_bound` and both `*_strong_duality` re-exports
   closed; `Drsb` is proved.
5. **remaining (the 9 placeholders):** the T4 SDE/PDE controls + worst-case-*structure*
   corollaries. Per the user (2026-07): **no Fable** — break each into natural subproblems
   and prove step-by-step. The SDE/PDE and OT-measurable-selection blocks may still need a
   documented `dependency` or a Mathlib-infrastructure lift; decide with the coordinator.

---

### Change log
- **2026-07 (first crack in the SDE frontier; KL data-processing proved):** count **6 → 5**.
  Proved `ChenGeorgiouPavon2021.dynamic_eq_static_SB` (Léonard dynamic⇄static SB) in one direction
  via a **new dependency-clean ForMathlib contribution** `MeasureTheory.toReal_klDiv_map_le` — the KL
  **data-processing inequality** (a genuine Mathlib gap: no DPI / f-divergence file), proved by
  conditional Jensen on the convex `klFun` (`toReal_rnDeriv_map` gives the pushforward RN-derivative
  as a conditional expectation). The gluing (path-reconstruction) direction is isolated to an edge.
  The remaining 5 CGP placeholders are `energy_identity` (continuous Girsanov) + 4 under-specified
  HJB/factorization statements (need statement work, not proofs).
- **2026-07 (Thm 4.2 landed + statement correction; MohajerinEsfahaniKuhn2018 proved):**
  count **7 → 6**. Proved `MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` (Thm 4.2)
  dependency-clean via `le_antisymm(weak, attainment)`, weak `≤` from the **new**
  `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost_restrict` (Ξ-restricted kernel) +
  empirical collapse + η-trick; **corrected the statement** to the `P(Ξ)`-restricted ball
  `wass1BallΞ` (the `ℝ`-valued `ℓk` encoding had dropped the paper's `P(Ξ)` restriction, making
  the raw-`wass1Ball` equality unsound for `Ξ ≠ univ`). **All 6 remaining placeholders are now in
  `ChenGeorgiouPavon2021`** (SDE/PDE — no Mathlib theory).
- **2026-07 (general worst-case structure landed; GaoKleywegt2023 proved):** count
  **8 → 7**. Proved `GaoKleywegt2023.worstCase_structure_cor1` (Cor 1(ii), eq. 27) dependency-clean —
  the general-`ν` 2-map transport `μ* = pstar·T̄#ν + (1−pstar)·T*#ν`, same house pattern as
  `cor2ii` but via `Measure.map` pushforwards + `integral_map` (with regularity edges since
  `c`/`Ψ` carry no standing measurability); attainment isolated to §5-safe ingredient edges.
  Only `MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` remains of the worst-case
  structure block.
- **2026-07 (data-driven worst-case structure landed):** count **9 → 8**. Proved
  `GaoKleywegt2023.dataDriven_worstCase_cor2ii` (Cor 2(ii), eq. 29) dependency-clean via the house
  pattern — explicit `K = 2` weighted-Dirac `μ*` construction (probability measure, `∈ ambiguitySet`
  via an explicit transport plan + `otCost_le_couplingCost`, closed-form `Ψ`-expectation, eq. (29)
  split-form identity), attainment isolated to §5-safe ingredient edges (split weight + per-point
  argmins + feasibility budget + one `≥` attainment edge), NOT the structured optimizer. Added
  local copies of `isProbabilityMeasure_wsum`/`integral_wsum`/`map_wsum` (→ ForMathlib dedup TODO).
- **2026-07 (Sinkhorn scaling landed):** count **13 → 12**. Proved
  `ForMathlib.matrix_scaling_exists` + `ForMathlib.sinkhorn_potentials_exist` (dependency-clean)
  by log-domain convex minimization — Mathlib has neither Brouwer nor Birkhoff contraction,
  so the intended fixed-point route was replaced. `matrix_scaling_exists` staged for
  upstreaming; `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` now delegates proved.
- **2026-07 refresh:** count 23 → **13**; recorded all strong-duality equalities +
  both cost bounds as PROVED (`Drsb` proved); resolved the `primal_feasible_iff` TX bug
  → `primal_feasible_radius_nonneg` (necessity, proved); recorded the no-Fable directive.
- Added [`FOUNDATIONS.md`](FOUNDATIONS.md): the classical-theorem chains, grep-verified
  Mathlib gaps, and survey search terms.
- Staged `ForMathlib/OptimalTransport/WeakDuality.lean` (Chain 1 weak node) and
  `ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean` (Chain 3 top);
  `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` now delegates to the latter (with a
  necessary `∑pᵢ = ∑qⱼ` hypothesis added — the statement was under-specified).
- Proved & staged `ForMathlib.MeasureTheory.Normalization` (first new pipeline artifact);
  `WangGaoXie2023.exists_worstCase_gibbs` now consumes it.
- Proved `ChenGeorgiouPavon2021.staticSB_eq_entropicOT` (T0, `hgibbs` rewrite).
- Prior: `WangGaoXie2023.exists_worstCase_gibbs`, `BlanchetMurthy2019.wdro_strong_duality_dualFn`.

## Project-wide theorem-target scaffold (2026-07-08)

The remaining DRSB work is now intended to be tracked by executable theorem-target placeholders, not by
interfaces hidden inside downstream hypotheses.  The rule for future work is:

1. add placeholder only for missing mathematics;
2. place the target in the module where the theorem belongs mathematically;
3. keep final assembly wrappers proof-bearing from those theorem targets;
4. when a target is proved, replace downstream hypotheses by the proved theorem as a separate
   integration step.

The current target aggregate is:

```lean
import ChenGeorgiouPavon2021.ProjectTheoremTargets
```

The main groups are:

- path-space carrier/generation: `Continuum.PathSpace`;
- Sobolev/CM energy bridge: `Continuum.Sobolev`;
- interval Wiener finite law, KL exhaustion, and quasi-invariance: `Continuum.IntervalWiener`;
- general KL exhaustion from generation: `Continuum.KLExhaustion`;
- Girsanov/energy identity model edges: `EnergyIdentityTargets`;
- dynamic SOC/Hopf--Cole/HJB verification: `SocOt.DynamicTargets`;
- dynamic/static gluing and finite-energy feasibility facts: `SocOt.StaticTargets`;
- static product coupling and optimizer uniqueness/attainment: `SocOt.EntropicOTTargets`;
- Sinkhorn uniqueness/convergence: `SocOt.SinkhornTargets`.

A source-level count after the scaffold overlay gives 27 executable target placeholders.  This count is
now the intended coarse progress bar for the remaining mathematical theorem-building phase.
