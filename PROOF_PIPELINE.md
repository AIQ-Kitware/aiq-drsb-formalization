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

## 2. Ranked remaining `sorry`s (23)

### On the card critical path (do these first)

| Decl | Tier | What it needs | Notes |
|---|---|---|---|
| `Drsb.wdrsb_cost_bound` | ✅ **PROVED** (axiom-clean) | — | **The WDRSB evaluation-card claim, discharged.** Composes the weak-duality kernel + `sqCost` symmetry + `couplingCost ≤ ε`, under explicit regularity + the OT-attainment edge `hOT` (the T4 seam stated as a hypothesis, not faked). `#print axioms` = propext/Classical.choice/Quot.sound only. |
| `GaoKleywegt2023.weak_duality_prop1` | **T3** | add integrability/`BddAbove` hyps; then the coupling-ε + `sInf`/`sSup` assembly | linchpin — kernel DONE (`ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost`) and now demonstrated end-to-end by `wdrsb_cost_bound`. Only the general `droValue` assembly remains; **Sion** (`Mathlib.Topology.Sion`) available for the minimax step. |
| `Drsb.sdrsb_cost_bound` | ✅ **PROVED** (axiom-clean) | — | **The SDRSB evaluation-card claim, discharged.** Composes the proved `WangGaoXie2023.sinkhorn_weak_duality_kernel` (per-point DV bound integrated over `p₀`) with `budget ≤ ε`, under `hκ>0` + the Sinkhorn attainment+disintegration edge `hSink`; dual restricted to `0<lam` (the `lam=0` `logPartition` is junk — ess-sup convention unencoded). Ball uses the audit-fixed external `ν`. |
| `WangGaoXie2023.strong_duality` (≤ half only) | **T3** | outer `inf_{λ}` + ball Lagrangian on top of the proved `logPartition_eq_gibbs_sSup` | the DV engine (`ForMathlib`) is already done; this is the Sinkhorn analogue of the linchpin. |

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
| `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` | **T3** | finite Sinkhorn / matrix scaling existence. Mathlib has Birkhoff + doubly-stochastic infra but NOT this. Move statement → `ForMathlib`. |

### Cheap once a dependency or a hypothesis lands (us)

| Decl | Tier | What it needs |
|---|---|---|
| `ChenGeorgiouPavon2021.schrodingerBridge_KL_eq_SOC` | **T2** | `sInf`-shift `inf{a+g(u)} = a + inf g` using `energy_identity` + `Feasible ⇒ initialMarginal = ρ₀`. Compiles atop the (T4) `energy_identity` sibling — concentrates debt like `wdro_strong_duality_dualFn` did. |
| `ChenGeorgiouPavon2021.optimal_control_eq_neg_grad_value` | **T2/TX** | blocked by *abstract* `grad`: `grad(−V) ≠ −grad V` without linearity. Add a `grad` additivity/negation hypothesis (or derive from `optimal_control_eq_grad_log` + that hyp), then T1. |
| `Drsb.wdrsb_strong_duality` | **T1** | re-export of `BlanchetMurthy2019.wdro_strong_duality_dualFn` once proved; **also under-hypothesized** — needs BM's (A1)/(A2)/`δ>0` added to the Drsb statement. |
| `Drsb.sdrsb_strong_duality` | **T1** | re-export of `WangGaoXie2023.strong_duality` once proved; add its hyps. |

### Statement bug (fix first)

| Decl | Tier | What it needs |
|---|---|---|
| `WangGaoXie2023.primal_feasible_iff` | **TX** | `Nonempty ↔ 0 ≤ ε` is false for the coupling-based `Wkappa` (`Wkappa κ μ̂ μ̂ > 0` for non-degenerate `μ̂`). Re-derive the feasibility statement from prose. (AGENTS.md §6.) |

### T4 — research-grade / not-in-Mathlib (defer or axiomatize)

Strong-duality **`≥` / attainment & worst-case structure**:
`BlanchetMurthy2019.wdro_strong_duality`, `GaoKleywegt2023.{strong_duality_thm1,
worstCase_structure_cor1, dataDriven_strongDuality_cor2i, dataDriven_worstCase_cor2ii}`,
`MohajerinEsfahaniKuhn2018.{worstCaseExpectation_eq_dual, worstCase_program,
worstCase_exists}`, `WangGaoXie2023.strong_duality` (`≥` half).
*Need OT measurable-selection / worst-case-measure construction — absent from Mathlib.*

**SDE / PDE / path-measure** (no Mathlib SDE theory):
`ChenGeorgiouPavon2021.{energy_identity (Girsanov), optimal_control_eq_grad_log,
optimal_control_eq_sigma_grad_log, optimal_control_eq_grad_value (HJB),
dynamic_eq_static_SB (Léonard gluing), optimal_coupling_factorization}`.

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
| `OptimalTransport.WeakDuality.expect_le_dualIntegrand_add_lam_couplingCost` — the OT-DRO **per-coupling Lagrangian bound** (the `≤` kernel) | ✅ **proved** (ported from `reference/V4.lean`, generalized to arbitrary cost `c`) | yes — no Kantorovich/Wasserstein duality in Mathlib at all | (done) | — |
| `LinearAlgebra/Matrix.SinkhornScaling` — finite **Sinkhorn / matrix scaling** existence (`sinkhorn_potentials_exist`, now with mass-conservation hyp) | 🟡 **staged** (statement; `sorry`) | yes — has Birkhoff + doubly-stochastic, not scaling | T3 | Fable |
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

Reach for a **Fable 5 agent** (`Agent` tool with `model: fable`, or a `Workflow` with a
Fable stage) on **T3** targets — self-contained, hard, from-scratch. Not on T4 (missing
theory: it will thrash) and not on T0–T2 (we do those cheaper).

A good Fable task spec is a **single theorem** with:
1. the exact Lean statement already in the file (Fable fills the body only);
2. all dependencies proved & imported (list them);
3. a proof sketch / the reference proof if one exists (e.g. `reference/V4.lean`);
4. the acceptance check: `lake env lean <File>.lean` exits 0 with only `sorry`-free
   `warning`s for *other* decls; the target emits none;
5. isolation: run in a `git` worktree (`isolation: "worktree"`) if it will edit files
   that another agent also touches.

**First two Fable tickets (ready to cut):**
- **F1 — `ForMathlib.OptimalTransport.WeakDuality`** (unblocks the cards). Port +
  generalize `reference/V4.lean::wdro_lagrangian_bound`, then assemble
  `GaoKleywegt2023.weak_duality_prop1` (add the integrability/`BddAbove` hyps first —
  that statement edit is a T2 we do *before* handing off).
- **F2 — `ForMathlib.…SinkhornScaling`** (`sinkhorn_potentials_exist`). Independent;
  can run in parallel with F1 in its own worktree.

---

## 5. Recommended execution order

1. **us, now:** land the T0/T1/T2 wins that don't need new theory —
   `schrodingerBridge_KL_eq_SOC` (atop `energy_identity`), the `optimal_control_eq_neg_grad_value`
   hypothesis fix, and stage the two ForMathlib statements (F1/F2 skeletons).
2. **us, statement work:** add the weak-duality side-hypotheses to `weak_duality_prop1`;
   fix `primal_feasible_iff` from prose.
3. **Fable, parallel worktrees:** F1 (weak-duality → cards) and F2 (Sinkhorn scaling).
4. **us:** once F1 lands, close `Drsb.wdrsb_cost_bound` / `sdrsb_cost_bound` (T2) and the
   `*_strong_duality` re-exports (T1, after adding hyps).
5. **defer:** the T4 SDE/PDE and strong-duality-`≥` block — a separate upstream program
   or documented `axiom`s; decide with the coordinator (needs the DRSB manuscript, §2).

---

### Change log
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
