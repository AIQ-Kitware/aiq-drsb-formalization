# PROOF_PIPELINE.md — ranking the remaining proofs & the ForMathlib upstreaming queue

Companion to [`AGENTS.md`](AGENTS.md) (orientation) and
[`formalization.yaml`](formalization.yaml) (per-declaration source map). This file is
the **proof-pass work plan**: it ranks every remaining `sorry` by difficulty, says
**who should do it** (us vs. a Fable 5 agent), and defines the **ForMathlib pipeline**
of Mathlib-contributable lemmas that the paper libraries consume.

Update it as `sorry`s close. Keep the counts honest (`grep -rn "sorry$" --include=*.lean
. | grep -vE '\.lake|reference/'`).

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
| **T4** | needs mathematics not in Mathlib (SDE/Girsanov/path measures, OT measurable selection, strong-duality attainment) | defer / axiomatize / long-horizon |
| **TX** | blocked: the *statement* is wrong/under-specified — fix the statement before proving | us (statement work) |

---

## 2. Ranked remaining `sorry`s (9)

> **Status refresh (2026-07).** All four DRSB capstones (`Drsb.{wdrsb,sdrsb}_cost_bound`
> and `Drsb.{wdrsb,sdrsb}_strong_duality`) are **proved** — `Drsb` is sorry-free. The
> paper-level strong-duality *equalities* (`BlanchetMurthy2019.wdro_strong_duality`,
> `GaoKleywegt2023.strong_duality_thm1`, `WangGaoXie2023.strong_duality`) are likewise
> proved, each `le_antisymm(weak, attainment)` with the research-grade `≥` isolated to one
> explicit **OT-attainment hypothesis** (not a `sorry`). `WangGaoXie2023.primal_feasible_iff`
> is resolved (see below). The **finite-Sinkhorn-scaling existence** (`SinkhornScaling`, T3)
> is now **PROVED** (axiom-clean; see below). `dataDriven_strongDuality_cor2i` is also now
> PROVED (house pattern; see §T4 note). `MohajerinEsfahaniKuhn2018.worstCase_program`
> (Thm 4.4) and `worstCase_exists` (Cor 4.6) are also PROVED (constructive worst-case law +
> one edge each). The **9** remaining `sorry`s are the genuine T4 frontier: the 6 SDE/PDE
> controls in `ChenGeorgiouPavon2021` and the 3 worst-case-*structure* corollaries in `GaoKleywegt2023`/`MohajerinEsfahaniKuhn2018`.

### On the card critical path (do these first)

| Decl | Tier | What it needs | Notes |
|---|---|---|---|
| `Drsb.wdrsb_cost_bound` | ✅ **PROVED** (axiom-clean) | — | **The WDRSB evaluation-card claim, discharged.** Composes the weak-duality kernel + `sqCost` symmetry + `couplingCost ≤ ε`, under explicit regularity + the OT-attainment edge `hOT` (the T4 seam stated as a hypothesis, not faked). `#print axioms` = propext/Classical.choice/Quot.sound only. |
| `GaoKleywegt2023.weak_duality_prop1` | ✅ **PROVED** (axiom-clean) | — | The general Wasserstein `v_P ≤ v_D`. `csSup_le → le_csInf → per-(μ,λ)` bound from the kernel + coupling ε-approx; the Moreau–Yosida `Φ`↔sup-form negation is the unconditional `Real.sSup_neg`. Under honest edges (`hfeas`/`hbdd`/`hφint`/`hΨμ`/`hOT`). |
| `GaoKleywegt2023.strong_duality_thm1` | ✅ **PROVED** (axiom-clean) | — | `v_P = v_D` via `le_antisymm (weak_duality_prop1) (attainment)`. The `≥` is a single explicit **attainment edge** `hattain` — this ISOLATES the whole strong-duality gap to the one OT measurable-selection fact (§6). |
| `Drsb.sdrsb_cost_bound` | ✅ **PROVED** (axiom-clean) | — | **The SDRSB evaluation-card claim, discharged.** Composes the proved `WangGaoXie2023.sinkhorn_weak_duality_kernel` (per-point DV bound integrated over `p₀`) with `budget ≤ ε`, under `hκ>0` + the Sinkhorn attainment+disintegration edge `hSink`; dual restricted to `0<lam` (the `lam=0` `logPartition` is junk — ess-sup convention unencoded). Ball uses the audit-fixed external `ν`. |
| `WangGaoXie2023.strong_duality` | ✅ **PROVED** (axiom-clean) | — | `V = V_D` via `le_antisymm`: the `≤` half composes `sinkhorn_weak_duality_kernel` (per-point DV integrated over `p₀`) + `le_csInf`; the `≥` half is the single **attainment+disintegration edge** `hSinkAll`/`hattain` (§6). The Sinkhorn analogue of the WDRO linchpin. |

**Sinkhorn weak-duality kernel — ✅ DONE** (`WangGaoXie2023.sinkhorn_weak_duality_kernel`,
axiom-clean; the second card `sdrsb_cost_bound` composes it). The roadmap below is how it
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
| `ForMathlib.sinkhorn_potentials_exist` / `matrix_scaling_exists` | ✅ **PROVED** (axiom-clean) | Done. Mathlib has **neither** Brouwer nor Birkhoff/Hilbert-metric contraction (grep-verified), so proved via **log-domain convex minimization** of `ψ(b)=∑ pᵢlog(∑ Gᵢⱼbⱼ)−∑ qⱼlog bⱼ` over the open simplex: boundary blow-up `−qⱼlog bⱼ→+∞` gives compactness (EVT, no coercivity lemma), the marginal equations come from 1-D directional derivatives along `eⱼ−eₖ` (`IsLocalMin.hasDerivAt_eq_zero`), and **mass conservation `∑p=∑q` kills the Lagrange multiplier**. `matrix_scaling_exists` staged for Mathlib upstreaming. `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` delegates. |

### Cheap once a dependency or a hypothesis lands (us)

| Decl | Tier | What it needs |
|---|---|---|
| `ChenGeorgiouPavon2021.schrodingerBridge_KL_eq_SOC` | **T2** | `sInf`-shift `inf{a+g(u)} = a + inf g` using `energy_identity` + `Feasible ⇒ initialMarginal = ρ₀`. Compiles atop the (T4) `energy_identity` sibling — concentrates debt like `wdro_strong_duality_dualFn` did. |
| `ChenGeorgiouPavon2021.optimal_control_eq_neg_grad_value` | **T2/TX** | blocked by *abstract* `grad`: `grad(−V) ≠ −grad V` without linearity. Add a `grad` additivity/negation hypothesis (or derive from `optimal_control_eq_grad_log` + that hyp), then T1. |
| `Drsb.wdrsb_strong_duality` | ✅ **PROVED** | — | Delegates to `GaoKleywegt2023.strong_duality_thm1` (`sqCost` symmetric ⇒ `Lc = −Φ`); the WDRSB capstone. |
| `Drsb.sdrsb_strong_duality` | ✅ **PROVED** | — | Re-export of `WangGaoXie2023.strong_duality`; `Drsb` is now sorry-free. |

### Statement bug — ✅ RESOLVED

| Decl | Tier | Resolution |
|---|---|---|
| `WangGaoXie2023.primal_feasible_iff` → **`primal_feasible_radius_nonneg`** | ~~TX~~ ✅ | The naive `Nonempty ↔ 0 ≤ ε` is **false** for the raw `Wkappa` ball (`Wkappa κ ν μ̂ μ̂ > 0` for non-degenerate `μ̂`; the true nonemptiness threshold is the free energy `−κ·𝔼[log ∫e^{−c/κ}dν] ≥ 0`, generically `> 0`). Restated & **proved** as the honest **necessity** half — `0 ≤ κ ⇒ (Nonempty → 0 ≤ ε)` — from `Wkappa ≥ 0`. The paper's full `↔ ρ ≥ 0` holds only for the ρ̄-reformulated KL-ball; its sufficiency direction is the worst-case-measure **attainment** edge (T4, deferred). Docstring records the derivation. |

### T4 — research-grade / not-in-Mathlib (defer or axiomatize)

**Worst-case *structure*** (the `≥`/attainment equalities are already discharged modulo an
explicit attainment hypothesis; what remains as `sorry` is the *shape* of the worst-case
measure): `GaoKleywegt2023.{worstCase_structure_cor1, dataDriven_worstCase_cor2ii}`,
`MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` (3).
*Need OT measurable-selection / worst-case-measure construction — absent from Mathlib.*

> **`MohajerinEsfahaniKuhn2018.worstCase_program` (Thm 4.4, eq. 13) — PROVED (2026-07,
> house pattern, axiom-clean).** The `≥` direction (`sup(program) ≤ droValue`) is proved
> **constructively, sorry-free**: every feasible `(α,q)` gives the explicit discrete law
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
> strong-duality *equality* `v_P = empiricalDual` (eq. 28) is now discharged, axiom-clean:
> it is the general `strong_duality_thm1` (`v_P = v_D`, weak-`≤` from the ForMathlib kernel +
> the isolated attainment edge `hattain`) composed with the **new sorry-free reduction**
> `GaoKleywegt2023.dualValue_eq_empiricalDual` (`v_D = empiricalDual` for the empirical `ν`,
> a direct integral-against-empirical-measure computation under `[MeasurableSingletonClass X]`).
> So this is the same `le_antisymm(weak, attainment)` posture as every other strong-duality
> equality here — the `≥` isolated to one explicit hypothesis, not a `sorry`. A 2026-07-03
> survey pass (flow-sinkhorn / lean-stat-learning-theory / Mathlib) confirmed **no external
> Lean library** supplies a finite Kantorovich/LP strong duality to discharge `hattain`
> outright; the finite worst-case is the explicit ≤(N+1)-atom construction of `cor2ii` (below,
> still open) — that, not an import, is what would make it fully sorry-free.

**SDE / PDE / path-measure** (no Mathlib SDE theory):
`ChenGeorgiouPavon2021.{energy_identity (Girsanov), optimal_control_eq_grad_log,
optimal_control_eq_sigma_grad_log, optimal_control_eq_grad_value (HJB),
dynamic_eq_static_SB (Léonard gluing), optimal_coupling_factorization}`.

> **`energy_identity` — discrete layer PROVED (2026-07, vendored external proof).** The
> continuous `energy_identity` (CGP (4.19)) is still a bare `sorry` (needs multi-D
> controlled-diffusion Girsanov + KL between path measures, neither in Mathlib). But its
> **Euler–Maruyama / Gaussian discretization — the quantity the DRSB card actually
> measures (AGENTS §3) — is now proved sorry-free, axiom-clean**:
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
recording them as `axiom`s with provenance. **Do not spend Fable cycles here yet.**

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
| `OptimalTransport.WeakDuality.expect_kernel_le_lam_sinkhornBudget_add_logPartition` — the **entropic (Sinkhorn) weak-duality kernel** (per-point DV integrated over `p₀`) | ✅ **proved** (axiom-clean; the entropic analogue, paper-agnostic) | yes — no entropic-DRO duality in Mathlib | (done) | — |
| `LinearAlgebra/Matrix.SinkhornScaling` — finite **Sinkhorn / matrix scaling** existence (`matrix_scaling_exists` + `sinkhorn_potentials_exist`, with mass-conservation hyp) | ✅ **proved** (axiom-clean; log-domain min, no Brouwer/Birkhoff needed) | yes — Sinkhorn scaling absent from Mathlib | T3 | (done) |
| Chain 1 roots (Sion minimax, Fenchel conjugate/duality, Kantorovich) · Chain 3 (Perron–Frobenius) | 🔜 queued (see FOUNDATIONS.md) | ❌ absent | L–XL | survey → Fable |

**Extraction rule.** When a `sorry` is a *general* fact (no DRSB/paper-specific
objects), give it a clean Mathlib-idiom statement, prove it in `ForMathlib/`, and have
the paper library `import` + consume it (as `WangGaoXie2023.exists_worstCase_gibbs` now
consumes `isProbabilityMeasure_inv_univ_smul`). That is the pipeline: paper `sorry` →
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
4. the acceptance check: `lake env lean <File>.lean` exits 0 with only `sorry`-free
   `warning`s for *other* decls; the target emits none;
5. isolation: run in a `git` worktree (`isolation: "worktree"`) if it will edit files
   that another agent also touches.

**Ticket status:**
- **F1 — `ForMathlib.OptimalTransport.WeakDuality`** (unblocked the cards): ✅ **DONE by us**
  — `expect_le_dualIntegrand_add_lam_couplingCost` ported/generalized and
  `GaoKleywegt2023.weak_duality_prop1` assembled, both axiom-clean.
- **F2 — `ForMathlib.…SinkhornScaling`** (`matrix_scaling_exists` + `sinkhorn_potentials_exist`):
  ✅ **DONE by us, no Fable** (axiom-clean). The intended fixed-point/Birkhoff route was
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
   no Fable** — F2 axiom-clean via log-domain minimization (Brouwer/Birkhoff absent).
4. ~~**us:**~~ ✅ `Drsb.{wdrsb,sdrsb}_cost_bound` and both `*_strong_duality` re-exports
   closed; `Drsb` is sorry-free.
5. **remaining (the 9 `sorry`s):** the T4 SDE/PDE controls + worst-case-*structure*
   corollaries. Per the user (2026-07): **no Fable** — break each into natural subproblems
   and prove step-by-step. The SDE/PDE and OT-measurable-selection blocks may still need a
   documented `axiom` or a Mathlib-infrastructure lift; decide with the coordinator.

---

### Change log
- **2026-07 (Sinkhorn scaling landed):** count **13 → 12**. Proved
  `ForMathlib.matrix_scaling_exists` + `ForMathlib.sinkhorn_potentials_exist` (axiom-clean)
  by log-domain convex minimization — Mathlib has neither Brouwer nor Birkhoff contraction,
  so the intended fixed-point route was replaced. `matrix_scaling_exists` staged for
  upstreaming; `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` now delegates sorry-free.
- **2026-07 refresh:** count 23 → **13**; recorded all strong-duality equalities +
  both cost bounds as PROVED (`Drsb` sorry-free); resolved the `primal_feasible_iff` TX bug
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
