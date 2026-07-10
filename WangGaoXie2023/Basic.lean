/-
# Wang–Gao–Xie (2023), "Sinkhorn Distributionally Robust Optimization"

Core theorem library: the **Sinkhorn-DRO strong-duality** chain and its
**log-partition / log-sum-exp** dual, together with the **Gibbs (exponential-tilt)
worst-case distribution**. This is the published backing of the SDRSB card's entropic
log-partition cost-bound term (`sdrsb_cost_bound.yaml`).

Prose reference: `prose/sinkhorn-dro-duality.md` (transcribed against arXiv:2109.11926
v5, Operations Research 2023). All printed equation / theorem / remark numbers below
are as printed in the prose file.

## Critical symbol convention (see prose "Setup and notation" / the symbol swap note)
The **paper's** symbols and **our** (ForMathlib.OT / DRSB) symbols are swapped:

  * paper `ε` = **entropic regularizer** of the Sinkhorn distance  ↔  our `κ`;
  * paper `ρ` = **Sinkhorn ball radius** (ambiguity radius)        ↔  our `ε`;
  * paper `λ` = Lagrange multiplier for the ball constraint       ↔  `lam`;
  * paper `P̂` = nominal / empirical distribution                  ↔  `μhat`;
  * paper `ν` = reference measure the worst-case is a.c. wrt       ↔  `ν`;
  * paper `f` = loss function                                      ↔  `f`;
  * paper `c(x,z)` = transport cost                                ↔  `c`.

So throughout this file `κ` is the entropic regularizer and `ε` is the ball radius,
matching `sinkhornBall μhat κ ε`.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.Coupling
import ForMathlib.OptimalTransport.DroValue
import ForMathlib.MeasureTheory.KLChainRule
import ForMathlib.MeasureTheory.DonskerVaradhan
import ForMathlib.MeasureTheory.Normalization
set_option autoImplicit false
open MeasureTheory
open scoped ProbabilityTheory
open scoped ENNReal
open ForMathlib.OT

namespace WangGaoXie2023

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

/-! ## The log-partition (soft-max) inner term and the dual objective -/

/-- **Per-point log-partition / soft-max term** `v_x(λ)`, the inner value of the
Sinkhorn-DRO dual (prose Eq. `(1)` inner term; the paper's `M`-functional, cf.
`M_logPartition` in `reference/V4.lean`).

For nominal point `xhat`, tilted reward `A(ζ) = f(ζ) − λ·c(xhat, ζ)` and temperature
`τ = λ·κ` (paper `λε`),
  `v_x(λ) = λ·κ · log ∫_ζ exp((f(ζ) − λ·c(xhat, ζ))/(λ·κ)) dν`.
This is the entropic **log-sum-exp** that replaces the Wasserstein dual's pointwise
`sup_z` (prose §3.4 step 2 / Lemma EC.2(II)).  Here `κ` = paper's entropic regularizer
`ε`, `ε` (elsewhere) = paper's radius `ρ`. -/
noncomputable def logPartition
    (ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ) (xhat : X) : ℝ :=
  lam * κ *
    Real.log (∫ ζ, Real.exp ((f ζ - lam * c xhat ζ) / (lam * κ)) ∂(ν : Measure X))

/-! ## The Sinkhorn disintegration (the entropic counterpart of a transport plan) -/

/-- **A Sinkhorn disintegration** of the source `μ` at budget `b`: the conditional family `P`
(each `P x ≪ ν`) whose `p₀`-mixture is `μ`, whose disintegrated entropic budget
`∫ (𝔼_{P_x}[c(x,·)] + κ·KL(P_x‖ν)) dp₀` is `≤ b`, and which carries the Donsker–Varadhan /
aggregate integrability the dual bound needs.

The entropic counterpart of a transport plan, and a `structure` rather than a nested `∃ _ ∧ _`
so that every consumer gets stable field names instead of a twelve-deep anonymous constructor.

The conditions on the conditionals are `p₀`-**a.e.**, because `Measure.condKernel` — the only
thing that ever produces `P` — is determined only up to a `p₀`-null set. `isProbabilityMeasure`
stays `∀ x` since `condKernel` is a Markov kernel on the nose.

`integrable_exp` and `integrable_logPartition` are the odd ones out: they constrain the *dual*
(the log-partition of `f` against `ν`) and say nothing about `P`. They ride along because the
Donsker–Varadhan aggregation needs them at the same `lam`. -/
structure IsSinkhornDisintegration (c : X → X → ℝ) (p₀ ν : ProbabilityMeasure X) (f : X → ℝ) (κ : ℝ)
    (μ : ProbabilityMeasure X) (b : ℝ) (P : X → Measure X) : Prop where
  /-- Each conditional is a probability measure (`condKernel` is a Markov kernel). -/
  isProbabilityMeasure : ∀ x, IsProbabilityMeasure (P x)
  /-- Each conditional is absolutely continuous against the reference, `p₀`-a.e. -/
  absolutelyContinuous : ∀ᵐ x ∂(p₀ : Measure X), P x ≪ (ν : Measure X)
  /-- The `p₀`-mixture of the conditionals reproduces `μ`'s expectation of `V`. -/
  expect_eq : expect μ f = ∫ x, (∫ y, f y ∂(P x)) ∂(p₀ : Measure X)
  /-- The disintegrated Sinkhorn budget is within `b`. -/
  budget_le : (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure X))
      ∂(p₀ : Measure X)) ≤ b
  /-- `V` is integrable against each conditional, `p₀`-a.e. -/
  integrable_V : ∀ᵐ x ∂(p₀ : Measure X), Integrable f (P x)
  /-- The transport cost is integrable against each conditional, `p₀`-a.e. -/
  integrable_cost : ∀ᵐ x ∂(p₀ : Measure X), Integrable (fun y => c x y) (P x)
  /-- The log-likelihood ratio is integrable, `p₀`-a.e. (the Donsker–Varadhan hypothesis). -/
  integrable_llr : ∀ᵐ x ∂(p₀ : Measure X),
      Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x)
  /-- The Gibbs tilt is `ν`-integrable at every positive multiplier (a condition on the dual). -/
  integrable_exp : ∀ lam, 0 < lam → ∀ x, Integrable
      (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure X)
  /-- The conditional mean of `V` is `p₀`-integrable. -/
  integrable_integral_V : Integrable (fun x => ∫ y, f y ∂(P x)) (p₀ : Measure X)
  /-- The conditional mean cost is `p₀`-integrable. -/
  integrable_integral_cost : Integrable (fun x => ∫ y, c x y ∂(P x)) (p₀ : Measure X)
  /-- The conditional relative entropy is `p₀`-integrable. -/
  integrable_klReal : Integrable (fun x => klReal (P x) (ν : Measure X)) (p₀ : Measure X)
  /-- The log-partition is `p₀`-integrable at every positive multiplier (a condition on the dual). -/
  integrable_logPartition : ∀ lam, 0 < lam → Integrable
      (fun x => logPartition ν c f κ lam x) (p₀ : Measure X)

/-- **The source `μ` admits a Sinkhorn disintegration at budget `b`.** The existential over the
conditional family; this is what the SDRSB cost bound consumes, one witness per `η > 0`.

Discharged by `hasSinkhornDisintegration_of_isSinkhornPlan`: on a standard-Borel `X` you hand
over a *transport plan* `γ`, not a conditional family, and `condKernel` + the KL chain rule build
the disintegration. -/
def HasSinkhornDisintegration (c : X → X → ℝ) (p₀ ν : ProbabilityMeasure X) (f : X → ℝ) (κ : ℝ)
    (μ : ProbabilityMeasure X) (b : ℝ) : Prop :=
  ∃ P : X → Measure X, IsSinkhornDisintegration c p₀ ν f κ μ b P

omit [NormedAddCommGroup X] in
/-- A disintegration at a tighter budget is one at a looser budget. -/
theorem IsSinkhornDisintegration.mono {c : X → X → ℝ} {p₀ ν : ProbabilityMeasure X} {f : X → ℝ} {κ : ℝ}
    {μ : ProbabilityMeasure X} {b b' : ℝ} {P : X → Measure X}
    (h : IsSinkhornDisintegration c p₀ ν f κ μ b P) (hb : b ≤ b') :
    IsSinkhornDisintegration c p₀ ν f κ μ b' P :=
  { h with budget_le := h.budget_le.trans hb }

omit [NormedAddCommGroup X] in
/-- A witness for a tighter budget is a witness for a looser one. -/
theorem HasSinkhornDisintegration.mono {c : X → X → ℝ} {p₀ ν : ProbabilityMeasure X} {f : X → ℝ} {κ : ℝ}
    {μ : ProbabilityMeasure X} {b b' : ℝ} (h : HasSinkhornDisintegration c p₀ ν f κ μ b)
    (hb : b ≤ b') : HasSinkhornDisintegration c p₀ ν f κ μ b' :=
  let ⟨P, hP⟩ := h; ⟨P, hP.mono hb⟩

omit [NormedAddCommGroup X] in
/-- **The SDRSB disintegration edge, discharged.** On a standard-Borel `X` you do not have to
supply a conditional family at all: hand over a **coupling** `γ ∈ Π(p₀, μ)` of finite entropy
relative to `p₀ ⊗ ν`, and `Measure.condKernel` + the KL chain rule build the witness.

Everything the old edge asked you to assert about `P` is now derived:

* `P := γ.condKernel`, and `p₀ ⊗ₘ P = γ` because `γ.fst = p₀` (`γ` is a coupling);
* `expect μ f = ∫∫ f dP dp₀` because `γ.snd = μ` (`Measure.integral_compProd`);
* the disintegrated budget equals `sinkhornObjective c κ p₀ ν γ`, by `integral_compProd` on the
  cost and `ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_integral` (the chain rule with
  `η := Kernel.const X ν`, whose `p₀`-marginal term vanishes) on the entropy;
* `P x ≪ ν` and `Integrable (llr (P x) ν) (P x)` hold `p₀`-**a.e.**, because a finite conditional
  KL has a.e. finite slices (`ae_klDiv_kernel_ne_top`) and `klDiv_ne_top_iff` splits each finite
  slice into exactly those two facts. This is why the kernel had to be weakened to a.e. first.
* `hI_kl` is `integrable_toReal_klDiv_kernel`, and the two slice-integrability facts are
  `Measure.integrable_compProd_iff`.

Residual hypotheses are the log-partition conditions on `ν`/`V`, which concern the dual and not the
transport, plus `hV`. **No second moments are needed**: `IsSinkhornPlan.integrable_cost` is derived
from the finiteness of the plan's `ℝ≥0∞` cost. The plan itself comes from ball membership
(`ForMathlib.OT.exists_isSinkhornPlan_of_mem_sinkhornBall`), so no edge survives. -/
theorem hasSinkhornDisintegration_of_isSinkhornPlan
    [StandardBorelSpace X] [Nonempty X]
    {c : X → X → ℝ} {p₀ ν μ : ProbabilityMeasure X} {κ b : ℝ} {γ : ProbabilityMeasure (X × X)}
    (hplan : ForMathlib.OT.IsSinkhornPlan c κ p₀ ν μ b γ) (f : X → ℝ)
    (hf : Integrable f (μ : Measure X))
    (h_exp : ∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure X))
    (hI_lp : ∀ lam, 0 < lam → Integrable
        (fun x => logPartition ν c f κ lam x) (p₀ : Measure X)) :
    HasSinkhornDisintegration c p₀ ν f κ μ b := by
  classical
  obtain ⟨hγ, hac, hfin, hcγ, hbudget⟩ := hplan
  have hfstγ : Measure.map Prod.fst (γ : Measure (X × X)) = (p₀ : Measure X) := hγ.1
  have hsndγ : Measure.map Prod.snd (γ : Measure (X × X)) = (μ : Measure X) := hγ.2
  -- the conditional family is the coupling's conditional kernel
  set P : ProbabilityTheory.Kernel X X := (γ : Measure (X × X)).condKernel with hPdef
  have hfst' : (γ : Measure (X × X)).fst = (p₀ : Measure X) := hfstγ
  have hdis : (p₀ : Measure X) ⊗ₘ P = (γ : Measure (X × X)) := by
    rw [← hfst']; exact (γ : Measure (X × X)).disintegrate P
  have href : (p₀ : Measure X) ⊗ₘ (ProbabilityTheory.Kernel.const X (ν : Measure X))
      = prodMeasure p₀ ν := Measure.compProd_const
  have hac' : (p₀ : Measure X) ⊗ₘ P
      ≪ (p₀ : Measure X) ⊗ₘ (ProbabilityTheory.Kernel.const X (ν : Measure X)) := by
    rw [hdis, href]; exact hac
  have hfin' : InformationTheory.klDiv ((p₀ : Measure X) ⊗ₘ P)
      ((p₀ : Measure X) ⊗ₘ (ProbabilityTheory.Kernel.const X (ν : Measure X))) ≠ ⊤ := by
    rw [hdis, href]; exact hfin
  -- a.e. slice facts: absolute continuity, finiteness, and hence integrable `llr`
  have hac_slice : ∀ᵐ x ∂(p₀ : Measure X), P x ≪ (ν : Measure X) := by
    have := Measure.absolutelyContinuous_compProd_right_iff.mp hac'
    simpa using this
  have hfin_slice : ∀ᵐ x ∂(p₀ : Measure X),
      InformationTheory.klDiv (P x) (ν : Measure X) ≠ ⊤ := by
    have := ForMathlib.MeasureTheory.ae_klDiv_kernel_ne_top (p₀ : Measure X) P
      (ProbabilityTheory.Kernel.const X (ν : Measure X)) hac' hfin'
    simpa using this
  have h_llr : ∀ᵐ x ∂(p₀ : Measure X),
      Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x) := by
    filter_upwards [hfin_slice] with x hx
    exact (InformationTheory.klDiv_ne_top_iff.mp hx).2
  have hI_kl : Integrable (fun x => klReal (P x) (ν : Measure X)) (p₀ : Measure X) := by
    have := ForMathlib.MeasureTheory.integrable_toReal_klDiv_kernel (p₀ : Measure X) P
      (ProbabilityTheory.Kernel.const X (ν : Measure X)) hac' hfin'
    simpa [klReal] using this
  -- the entropy term disintegrates (KL chain rule, constant second kernel)
  have hKL : klReal (γ : Measure (X × X)) (prodMeasure p₀ ν)
      = ∫ x, klReal (P x) (ν : Measure X) ∂(p₀ : Measure X) := by
    have := ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_integral (p₀ : Measure X) P
      (ProbabilityTheory.Kernel.const X (ν : Measure X)) hac' hfin'
    rw [hdis, href] at this
    simpa [klReal] using this
  -- integrability of the two integrands against `γ`
  have hfae : AEStronglyMeasurable f (Measure.map Prod.snd (γ : Measure (X × X))) := hsndγ ▸ hf.1
  have hfγ : Integrable (fun z : X × X => f z.2) (γ : Measure (X × X)) :=
    (integrable_map_measure hfae measurable_snd.aemeasurable).mp (hsndγ ▸ hf)
  have hfcp : Integrable (fun z : X × X => f z.2) ((p₀ : Measure X) ⊗ₘ P) := by rw [hdis]; exact hfγ
  have hccp : Integrable (fun z : X × X => c z.1 z.2) ((p₀ : Measure X) ⊗ₘ P) := by
    rw [hdis]; exact hcγ
  -- slice integrability and integrability of the inner integrals
  have hf_P : ∀ᵐ x ∂(p₀ : Measure X), Integrable f (P x) := by
    have := ((Measure.integrable_compProd_iff hfcp.aestronglyMeasurable).mp hfcp).1
    simpa using this
  have hc_P : ∀ᵐ x ∂(p₀ : Measure X), Integrable (fun y => c x y) (P x) :=
    ((Measure.integrable_compProd_iff hccp.aestronglyMeasurable).mp hccp).1
  have hI_V : Integrable (fun x => ∫ y, f y ∂(P x)) (p₀ : Measure X) := by
    have h := hfcp
    rw [Measure.compProd] at h
    simpa using h.integral_compProd
  have hI_c : Integrable (fun x => ∫ y, c x y ∂(P x)) (p₀ : Measure X) := by
    have h := hccp
    rw [Measure.compProd] at h
    simpa using h.integral_compProd
  -- the two disintegration identities
  have hfdis : expect μ f = ∫ x, (∫ y, f y ∂(P x)) ∂(p₀ : Measure X) := by
    have h1 : expect μ f = ∫ z : X × X, f z.2 ∂(γ : Measure (X × X)) := by
      rw [expect, ← hsndγ, integral_map measurable_snd.aemeasurable hfae]
    rw [h1, ← hdis, Measure.integral_compProd hfcp]
  have hcostdis : couplingCost c γ = ∫ x, (∫ y, c x y ∂(P x)) ∂(p₀ : Measure X) := by
    show ∫ z : X × X, c z.1 z.2 ∂(γ : Measure (X × X)) = _
    rw [← hdis, Measure.integral_compProd hccp]
  -- the disintegrated budget IS the Sinkhorn objective
  have hbud : (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure X))
      ∂(p₀ : Measure X)) ≤ b := by
    rw [integral_add hI_c (hI_kl.const_mul κ), integral_const_mul, ← hcostdis, ← hKL]
    exact hbudget
  exact ⟨fun x => P x,
    { isProbabilityMeasure := fun x => inferInstance
      absolutelyContinuous := hac_slice
      expect_eq := hfdis
      budget_le := hbud
      integrable_V := hf_P
      integrable_cost := hc_P
      integrable_llr := h_llr
      integrable_exp := h_exp
      integrable_integral_V := hI_V
      integrable_integral_cost := hI_c
      integrable_klReal := hI_kl
      integrable_logPartition := hI_lp }⟩


/-- **Sinkhorn-DRO dual objective** at multiplier `λ` (prose Eq. `(1)`, the `(Dual)`
integrand):
  `sinkhornDualObjective(λ) = λ·ε + 𝔼_{x̂∼μhat}[ v_{x̂}(λ) ]`
    `= λ·ε + λ·κ · 𝔼_{x̂∼μhat}[ log ∫_ζ exp((f(ζ) − λ·c(x̂,ζ))/(λ·κ)) dν ]`.
With our convention `κ` = paper `ε` (regularizer) and `ε` = paper `ρ` (radius), this
is exactly `V_D`'s integrand `λρ + λε · 𝔼_{x∼P̂}[log 𝔼_{z∼ν} e^{(f(z)−λc(x,z))/(λε)}]`.
The log-partition term is the `Real.log (∫ ζ, Real.exp …)` inside `logPartition`. -/
noncomputable def sinkhornDualObjective
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ ε lam : ℝ) : ℝ :=
  lam * ε + expect μhat (fun xhat => logPartition ν c f κ lam xhat)

/-! ## Theorem 1 (Strong Duality) -/

-- `strong_duality` (Theorem 1(II)) is proved below, after the weak-duality kernel it uses.

omit [NormedAddCommGroup X] in
/-- **Theorem 1(I) (Feasibility), necessity direction.** For a nonnegative regularizer
`κ`, feasibility of `(Primal)` *requires* a nonnegative radius: if the Sinkhorn ball is
nonempty then `0 ≤ ε`. Dependency-clean.

Proof: `0 ≤ W_{κ,ν}(μ̂, μ)` for every `μ` — the Sinkhorn objective
`𝔼_γ[‖x−y‖²] + κ·KL(γ‖μ̂⊗ν)` is a sum of two nonnegatives (squared cost; `κ ≥ 0` times
`KL ≥ 0`), so its infimum over couplings is `≥ 0` — and any ball member satisfies
`W_{κ,ν}(μ̂, μ) ≤ ε`.

⚠ **Why this is the necessity half only, not the paper's full `↔ ρ ≥ 0`** (audit
resolution of the former `primal_feasible_iff` placeholder, AGENTS.md §6 / the audit note in
`prose/sinkhorn-dro-duality.md`). Against the **raw** entropic-OT ball
`sinkhornBall μhat ν κ ε = {μ : W_{κ,ν}(μ̂,μ) ≤ ε}`, sufficiency (`0 ≤ ε ⇒ nonempty`) is
**false**: unlike a metric ball, `W_{κ,ν}(μ̂, μ̂) > 0` in general (the entropic term
`κ·KL(·‖μ̂⊗ν)` forbids the diagonal coupling), so the ball's true nonemptiness threshold
is the free energy `inf_μ W_{κ,ν}(μ̂, μ) = −κ·𝔼_{x∼μ̂}[log ∫ e^{−‖x−·‖²/κ} dν] ≥ 0`, which
is *strictly* positive unless the cost is `ν`-a.e. zero. The paper's `ρ ≥ 0` characterization
holds only after the reference-kernel reformulation (prose Eq. `(2)`–`(3)`: shift to
`ρ̄ = ρ + κ·𝔼_{μ̂}[log ∫ e^{−c/κ} dν]` and the Gibbs kernel `Q_{x,κ}`), where the constraint
becomes `κ·𝔼_{μ̂}[KL(γ_x ‖ Q_{x,κ})] ≤ ρ̄` and `KL ≥ 0` gives feasibility ⇔ `ρ̄ ≥ 0`. That
sufficiency direction is the worst-case-measure **attainment** edge (an OT existence result
absent from Mathlib, §6 T4) and stays deferred; the necessity below is unconditional.

`W_{κ,ν}` is `ℝ≥0∞`-valued, so nonnegativity of the discrepancy is now carried by the type and
the necessity half is immediate from `ENNReal.toReal_nonneg`. (`_hκ` is the source theorem's own
hypothesis, no longer proof-critical — the `κ ≥ 0` sign work it used to do is subsumed. Kept for
fidelity, `_`-prefixed per AGENTS.md.) This is also exactly why `sinkhornBall` is stated as
"`W_{κ,ν}` finite ∧ `toReal ≤ ε`" and not "`W_{κ,ν} ≤ ENNReal.ofReal ε`": the latter sends every
negative radius to `0`, making the negative-radius ball `{μ | W_{κ,ν} = 0}`, which is nonempty
when `μ̂ = ν = μ = δₐ` — and this theorem would be **false**. -/
theorem primal_feasible_radius_nonneg (c : X → X → ℝ)
    (μhat ν : ProbabilityMeasure X) (κ ε : ℝ) (_hκ : 0 ≤ κ)
    (h : (sinkhornBall c μhat ν κ ε).Nonempty) : 0 ≤ ε := by
  obtain ⟨μ, -, hle⟩ := h
  exact le_trans ENNReal.toReal_nonneg hle

/-! ## The inner Gibbs variational identity (engine of Theorem 1, step 2)

Prose §3.4 step 2 / **Lemma EC.2(II)**: the per-point inner problem is a
Gibbs/entropy-penalised maximization whose value is the log-partition and whose
maximizer is the exponential tilt. This is the Donsker–Varadhan / Gibbs variational
principle (`ForMathlib.MeasureTheory.log_integral_exp_eq_sSup`). -/

omit [NormedAddCommGroup X] in
/-- **Lemma EC.2(II) / Donsker–Varadhan engine.** For fixed `xhat`, with tilted
reward-per-temperature `A(ζ) = (f(ζ) − λ·c(xhat,ζ))/(λ·κ)`, the log-partition equals
the Gibbs variational supremum over posteriors `μ ≪ ν`:
  `log ∫ exp(A) dν = sup_{μ≪ν} ( 𝔼_μ[A] − KL(μ‖ν) )`,
attained at the Gibbs tilt `ν.tilted A`.  Multiplying by `λκ` recovers `logPartition`.
(Prose "Donsker–Varadhan / Gibbs variational identity", displayed identity.) -/
theorem logPartition_eq_gibbs_sSup
    (ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ) (xhat : X)
    (hint : Integrable (fun ζ => Real.exp ((f ζ - lam * c xhat ζ) / (lam * κ))) (ν : Measure X))
    (htilt : Integrable (fun ζ => (f ζ - lam * c xhat ζ) / (lam * κ))
        ((ν : Measure X).tilted (fun ζ => (f ζ - lam * c xhat ζ) / (lam * κ)))) :
    Real.log (∫ ζ, Real.exp ((f ζ - lam * c xhat ζ) / (lam * κ)) ∂(ν : Measure X))
      = sSup { r : ℝ | ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ ≪ (ν : Measure X) ∧
          Integrable (fun ζ => (f ζ - lam * c xhat ζ) / (lam * κ)) μ ∧
          Integrable (llr μ (ν : Measure X)) μ ∧
          r = (∫ ζ, (f ζ - lam * c xhat ζ) / (lam * κ) ∂μ)
                - (InformationTheory.klDiv μ (ν : Measure X)).toReal } :=
  -- Exactly the proved Donsker–Varadhan variational identity, applied to the
  -- tilted-reward-per-temperature integrand `A(ζ) = (f ζ − λ·c(x̂,ζ))/(λ·κ)`.
  ForMathlib.MeasureTheory.log_integral_exp_eq_sSup hint htilt

/-! ## Remark 4: the Gibbs / exponential-tilt worst-case distribution -/

/-- **Unnormalized worst-case Gibbs measure** (prose Remark 4 numerator; cf.
`gibbsUnnormalized` in `reference/V4.lean`). For nominal `xhat` and dual optimum
`λ = λ*`, this is the reference `ν` reweighted by the exponential tilt:
  `dγ̃_x(z) = exp((f(z) − λ·c(xhat,z))/(λ·κ)) dν(z)`. -/
noncomputable def gibbsUnnormalized
    (ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ) (xhat : X) :
    Measure X :=
  (ν : Measure X).withDensity
    (fun z => ENNReal.ofReal (Real.exp ((f z - lam * c xhat z) / (lam * κ))))

/-- **Gibbs-form worst-case conditional (proportionality form)** (prose Remark 4).
A family `P : X → Measure X` of conditionals is the Sinkhorn worst-case iff each
`P xhat` is proportional to the unnormalized Gibbs measure, i.e. the exponential tilt
`∝ exp((f − λ·c)/(λ·κ))` of the reference `ν`. -/
def GibbsWorstCase
    (ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ)
    (P : X → Measure X) : Prop :=
  ∀ xhat : X, ∃ α : ℝ≥0∞, P xhat = α • gibbsUnnormalized ν c f κ lam xhat

omit [NormedAddCommGroup X] in
/-- **Remark 4 (Worst-case Distribution), existence.** Under `ρ > 0`, Condition 1 and
an optimal `λ* > 0`, the worst-case conditional exists and is the normalized
exponential tilt of `ν` (prose Remark 4).  The normalizability hypotheses `hpos`/`hfin`
(unnormalized Gibbs mass `≠ 0`, `≠ ⊤`) are the measure-theoretic form of Assumption
1(II) + Condition 1 that make the normalizer `α_x = (∫ e^{(f−λc)/(λε)} dν)⁻¹`
well-defined. The resulting `P xhat` is a probability measure with density
`α_x · exp((f − λ·c)/(λ·κ))` w.r.t. `ν`. -/
theorem exists_worstCase_gibbs
    (ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ)
    (hpos : ∀ xhat, gibbsUnnormalized ν c f κ lam xhat Set.univ ≠ 0)   -- normalizer 𝔼_ν[e^{(f−λc)/(λε)}] ≠ 0
    (hfin : ∀ xhat, gibbsUnnormalized ν c f κ lam xhat Set.univ ≠ ⊤) : -- Condition 1: 𝔼_ν[e^{(f−λc)/(λε)}] < ∞
    ∃ P : X → Measure X,
      (∀ xhat, IsProbabilityMeasure (P xhat)) ∧ GibbsWorstCase ν c f κ lam P := by
  -- Normalize each unnormalized Gibbs measure by its (finite, nonzero) total mass
  -- `α_x = (𝔼_ν[e^{(f−λc)/(λε)}])⁻¹`; the normalizer is well-defined precisely by
  -- `hpos`/`hfin`, and the result is a probability measure proportional to `γ̃_x`.
  refine ⟨fun xhat => (gibbsUnnormalized ν c f κ lam xhat Set.univ)⁻¹
            • gibbsUnnormalized ν c f κ lam xhat, ?_, ?_⟩
  · -- probability measure: the staged ForMathlib normalization lemma, `hpos`/`hfin`
    intro xhat
    exact ForMathlib.MeasureTheory.isProbabilityMeasure_inv_univ_smul _ (hpos xhat) (hfin xhat)
  · -- proportionality is definitional: the scalar is the normalizer `α_x`
    intro xhat
    exact ⟨(gibbsUnnormalized ν c f κ lam xhat Set.univ)⁻¹, rfl⟩

omit [NormedAddCommGroup X] in
/-- **Remark 4 density is the Gibbs tilt** (prose Remark 4 density formula; the
`Measure.tilted` form).  The worst-case conditional `γ*_x` equals the normalized
exponential tilt `ν.tilted A` with `A(z) = (f(z) − λ·c(xhat,z))/(λ·κ)`, whose density
w.r.t. `ν` is `α_x · exp(A(z))`, `α_x = (∫ exp(A) dν)⁻¹`.  This is the continuous,
full-support Gibbs conditional (contrast the Wasserstein worst-case's `n+1` atoms). -/
theorem worstCase_conditional_tilted
    (ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ) (xhat : X)
    (_hint : Integrable (fun z => Real.exp ((f z - lam * c xhat z) / (lam * κ))) (ν : Measure X)) :
    (ν : Measure X).tilted (fun z => (f z - lam * c xhat z) / (lam * κ))
      = (ν : Measure X).withDensity (fun z => ENNReal.ofReal
          ((∫ u, Real.exp ((f u - lam * c xhat u) / (lam * κ)) ∂(ν : Measure X))⁻¹
            * Real.exp ((f z - lam * c xhat z) / (lam * κ)))) := by
  -- `Measure.tilted ν A = ν.withDensity (z ↦ ofReal (exp (A z) / ∫ exp A dν))`;
  -- the claim only rewrites `a / b` as `b⁻¹ * a` inside the density.
  unfold MeasureTheory.Measure.tilted
  congr 1 with z
  rw [div_eq_inv_mul]

/-! ## Sinkhorn weak-duality kernel (the entropic per-coupling Lagrangian bound) -/

omit [NormedAddCommGroup X] in
/-- **Sinkhorn per-conditional-family weak-duality kernel.** For a family of conditionals
`P : X → Measure X` (each `≪` the reference `ν`), the nominal `p₀`, and `λ, κ > 0`, the
`p₀`-averaged reward is bounded by `λ·(disintegrated Sinkhorn budget) + 𝔼_{p₀}[logPartition]`:
`∫_{x∼p₀} 𝔼_{P_x}[f] ≤ λ · ∫_{x∼p₀} (𝔼_{P_x}[c(x,·)] + κ·KL(P_x‖ν)) + 𝔼_{x∼p₀}[v_x(λ)]`.

This is the entropic analogue of `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost`:
the proved Gibbs/Donsker–Varadhan inequality (`ForMathlib.MeasureTheory.
integral_le_klDiv_add_log_integral_exp`) applied to `A_x = (f − λc(x,·))/(λκ)` per nominal
point `x`, then integrated over `p₀`. It is the load-bearing `≤` half behind
`WangGaoXie2023.strong_duality` and `Drsb.sdrsb_cost_bound` (once composed with a
disintegration of the ball-witnessing coupling `γ = p₀ ⊗ₘ P`). The many integrability
hypotheses make the per-point DV bound apply and the aggregate integrals well defined.

The conditions on the conditionals (`hac`, `hf_P`, `hc_P`, `h_llr`) are `p₀`-**a.e.**, not
`∀ x`. This is essential, not cosmetic: the only way anyone produces the family `P` is by
disintegrating a coupling (`Measure.condKernel`), and a `condKernel` is determined only up
to a `p₀`-null set — it satisfies these conditions a.e. and nothing stronger. Demanding
`∀ x` here would make the kernel unusable by its sole intended caller
(`Drsb.hasSinkhornDisintegration_of_isSinkhornPlan`). `hP` stays `∀ x` because `condKernel` *is* a Markov
kernel on the nose. -/
theorem sinkhorn_weak_duality_kernel
    (p₀ ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ)
    (hκ : 0 < κ) (hlam : 0 < lam)
    (P : X → Measure X) (hP : ∀ x, IsProbabilityMeasure (P x))
    (hac : ∀ᵐ x ∂(p₀ : Measure X), P x ≪ (ν : Measure X))
    (hf_P : ∀ᵐ x ∂(p₀ : Measure X), Integrable f (P x))
    (hc_P : ∀ᵐ x ∂(p₀ : Measure X), Integrable (fun y => c x y) (P x))
    (h_llr : ∀ᵐ x ∂(p₀ : Measure X), Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x))
    (h_exp : ∀ x, Integrable
        (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure X))
    (hI_f : Integrable (fun x => ∫ y, f y ∂(P x)) (p₀ : Measure X))
    (hI_c : Integrable (fun x => ∫ y, c x y ∂(P x)) (p₀ : Measure X))
    (hI_kl : Integrable (fun x => klReal (P x) (ν : Measure X)) (p₀ : Measure X))
    (hI_lp : Integrable (fun x => logPartition ν c f κ lam x) (p₀ : Measure X)) :
    (∫ x, (∫ y, f y ∂(P x)) ∂(p₀ : Measure X))
      ≤ lam * (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure X)) ∂(p₀ : Measure X))
        + ∫ x, logPartition ν c f κ lam x ∂(p₀ : Measure X) := by
  have hlamκ : (0 : ℝ) < lam * κ := mul_pos hlam hκ
  have hne : lam * κ ≠ 0 := ne_of_gt hlamκ
  -- per-nominal-point Gibbs/DV bound, `p₀`-a.e.
  have hpt : ∀ᵐ x ∂(p₀ : Measure X), (∫ y, f y ∂(P x))
      ≤ lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure X)
        + logPartition ν c f κ lam x := by
    filter_upwards [hac, hf_P, hc_P, h_llr] with x hacx hf_Px hc_Px h_llrx
    haveI := hP x
    have hsub : Integrable (fun y => f y - lam * c x y) (P x) :=
      hf_Px.sub (hc_Px.const_mul lam)
    have hA_int : Integrable (fun y => (f y - lam * c x y) / (lam * κ)) (P x) :=
      hsub.div_const _
    have hDV := ForMathlib.MeasureTheory.integral_le_klDiv_add_log_integral_exp
      hacx hA_int h_llrx (h_exp x)
    have hAeq : (∫ y, (f y - lam * c x y) / (lam * κ) ∂(P x))
        = (lam * κ)⁻¹ * ((∫ y, f y ∂(P x)) - lam * ∫ y, c x y ∂(P x)) := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_sub hf_Px (hc_Px.const_mul lam),
        integral_const_mul]
      ring
    rw [hAeq] at hDV
    have hlp : logPartition ν c f κ lam x
        = lam * κ * Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure X)) :=
      rfl
    have hmul := mul_le_mul_of_nonneg_left hDV (le_of_lt hlamκ)
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_add] at hmul
    have hkl : (InformationTheory.klDiv (P x) (ν : Measure X)).toReal
        = klReal (P x) (ν : Measure X) := rfl
    rw [hkl] at hmul
    rw [hlp]
    linarith [hmul]
  -- integrate the pointwise bound over p₀
  have hRHS_int : Integrable
      (fun x => lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure X)
        + logPartition ν c f κ lam x) (p₀ : Measure X) :=
    ((hI_c.const_mul lam).add (hI_kl.const_mul (lam * κ))).add hI_lp
  calc (∫ x, (∫ y, f y ∂(P x)) ∂(p₀ : Measure X))
      ≤ ∫ x, (lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure X)
          + logPartition ν c f κ lam x) ∂(p₀ : Measure X) := integral_mono_ae hI_f hRHS_int hpt
    _ = lam * (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure X)) ∂(p₀ : Measure X))
          + ∫ x, logPartition ν c f κ lam x ∂(p₀ : Measure X) := by
        have e1 : (∫ x, (lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure X)
              + logPartition ν c f κ lam x) ∂(p₀ : Measure X))
            = lam * (∫ x, (∫ y, c x y ∂(P x)) ∂(p₀ : Measure X))
              + lam * κ * (∫ x, klReal (P x) (ν : Measure X) ∂(p₀ : Measure X))
              + ∫ x, logPartition ν c f κ lam x ∂(p₀ : Measure X) := by
          have hAB : Integrable (fun x => lam * (∫ y, c x y ∂(P x))
              + lam * κ * klReal (P x) (ν : Measure X)) (p₀ : Measure X) :=
            (hI_c.const_mul lam).add (hI_kl.const_mul (lam * κ))
          rw [integral_add hAB hI_lp,
            integral_add (hI_c.const_mul lam) (hI_kl.const_mul (lam * κ)),
            integral_const_mul, integral_const_mul]
        have e2 : (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure X)) ∂(p₀ : Measure X))
            = (∫ x, (∫ y, c x y ∂(P x)) ∂(p₀ : Measure X))
              + κ * (∫ x, klReal (P x) (ν : Measure X) ∂(p₀ : Measure X)) := by
          rw [integral_add hI_c (hI_kl.const_mul κ), integral_const_mul]
        rw [e1, e2]; ring

omit [NormedAddCommGroup X] in
/-! ## The Sinkhorn cost bound (weak duality), edge-free -/

omit [NormedAddCommGroup X] in
omit [NormedAddCommGroup X] in
/-- **Sinkhorn weak duality, given near-optimal disintegrations.** If for every `η > 0` the source
`μ` admits a Sinkhorn disintegration of budget `≤ ε + η`, its expected reward is bounded by the
log-partition dual. Only *near-optimal* disintegrations are needed, never an attained one —
`W_{κ,ν}` is an infimum and supplies the former only. -/
theorem sinkhorn_cost_bound_of_disintegrations (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ)
    (f : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ) (μ : ProbabilityMeasure X)
    (hSink : ∀ η : ℝ, 0 < η → HasSinkhornDisintegration c μhat ν f κ μ (ε + η)) :
    expect μ f
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧ v = sinkhornDualObjective μhat ν c f κ ε lam } := by
  refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
  rintro v ⟨lam, hlam, rfl⟩
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  obtain ⟨P, hd⟩ := hSink (δ / lam) (div_pos hδ hlam)
  have key := sinkhorn_weak_duality_kernel μhat ν c f κ lam hκ hlam P
    hd.isProbabilityMeasure hd.absolutelyContinuous hd.integrable_V hd.integrable_cost
    hd.integrable_llr (hd.integrable_exp lam hlam) hd.integrable_integral_V
    hd.integrable_integral_cost hd.integrable_klReal (hd.integrable_logPartition lam hlam)
  have hb := mul_le_mul_of_nonneg_left hd.budget_le (le_of_lt hlam)
  rw [show lam * (ε + δ / lam) = lam * ε + δ by field_simp] at hb
  rw [hd.expect_eq]
  simp only [sinkhornDualObjective, expect]
  linarith [key, hb]

omit [NormedAddCommGroup X] in
/-- **The Sinkhorn cost bound, with no transport, attainment or disintegration edge.**
Ball membership alone produces everything: `exists_isSinkhornPlan_of_mem_sinkhornBall` extracts a
near-optimal finite-entropy plan (a theorem, because `Wkappa` infimises the `ℝ≥0∞` objective),
`hasSinkhornDisintegration_of_isSinkhornPlan` turns it into a conditional family, and
`sinkhorn_cost_bound_of_disintegrations` runs Donsker–Varadhan and lets `η ↓ 0`.

Surviving hypotheses are checkable regularity: `hc`/`hcm` on the cost, `hf`, and `h_exp`/`hI_lp`,
which constrain the *dual* and say nothing about transport. No second moments — the plan's
`integrable_cost` is derived from the finiteness of its `ℝ≥0∞` cost. -/
theorem sinkhorn_cost_bound [StandardBorelSpace X] [Nonempty X]
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ)
    (hc : ∀ x y, 0 ≤ c x y) (hcm : Measurable fun z : X × X => c z.1 z.2)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ sinkhornBall c μhat ν κ ε)
    (hf : Integrable f (μ : Measure X))
    (h_exp : ∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure X))
    (hI_lp : ∀ lam, 0 < lam → Integrable
        (fun x => logPartition ν c f κ lam x) (μhat : Measure X)) :
    expect μ f
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧ v = sinkhornDualObjective μhat ν c f κ ε lam } :=
  sinkhorn_cost_bound_of_disintegrations μhat ν c f κ ε hκ μ fun η hη => by
    obtain ⟨γ, hplan⟩ := ForMathlib.OT.exists_isSinkhornPlan_of_mem_sinkhornBall
      c hc hcm μhat ν μ κ ε η hκ hη hμ
    exact hasSinkhornDisintegration_of_isSinkhornPlan hplan f hf h_exp hI_lp

omit [NormedAddCommGroup X] in
/-- **An attaining worst-case measure gives the `≥` direction.** The receipt that
`strong_duality`'s `hge` is weaker than the customary attainment hypothesis. The converse fails:
a vanishing duality gap does not produce a maximizer. -/
theorem sinkhornDual_le_droValue_of_attaining_measure
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ ε : ℝ)
    (hfbdd : BddAbove (Set.range f))
    (hfAll : ∀ μ : ProbabilityMeasure X, μ ∈ sinkhornBall c μhat ν κ ε →
        Integrable f (μ : Measure X))
    (hattain : ∃ μ : ProbabilityMeasure X, μ ∈ sinkhornBall c μhat ν κ ε ∧
        expect μ f = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = sinkhornDualObjective μhat ν c f κ ε lam }) :
    sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧ v = sinkhornDualObjective μhat ν c f κ ε lam }
      ≤ droValue (sinkhornBall c μhat ν κ ε) f := by
  have hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
      μ ∈ sinkhornBall c μhat ν κ ε ∧ r = expect μ f } :=
    ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range _ f hfbdd hfAll
  obtain ⟨μ, hμ, hμeq⟩ := hattain
  rw [← hμeq]
  exact le_csSup hbddP ⟨μ, hμ, rfl⟩

omit [NormedAddCommGroup X] in
/-- **Theorem 1 (Strong Duality), part (II)** — `V = V_D`: the Sinkhorn-DRO worst-case
value over the ball equals the log-partition dual. `le_antisymm` of `droValue ≤ dual`
(each source's Sinkhorn cost bound, inlined from `sinkhorn_weak_duality_kernel` + `le_csInf`,
via `csSup_le`) and `dual ≤ droValue` (the attaining worst-case measure, `le_csSup`).

**The `hSinkAll` edge is gone.** The `≤` half is `sinkhorn_cost_bound`, which is edge-free: ball
membership yields a near-optimal finite-entropy plan (`exists_isSinkhornPlan_of_mem_sinkhornBall`),
`condKernel` and the KL chain rule turn it into a conditional family
(`hasSinkhornDisintegration_of_isSinkhornPlan`), and Donsker–Varadhan plus `η ↓ 0` finishes.
`BddAbove` is likewise derived, from `hfbdd`. The dual runs over `0 < lam` (the `lam=0`
`logPartition` is junk, cf. `Drsb.sdrsb_cost_bound`); since there is no `lam = 0` conjugate term to
read `hfbdd` off, it is stated explicitly.

**What remains assumed is exactly `hattain`** — the `≥`/worst-case-measure attainment, the OT
measurable-selection seam (§6) — plus checkable regularity (`hc`/`hcm` on the cost, `hfAll`,
`h_exp`, `hI_lp`). -/
theorem strong_duality [StandardBorelSpace X] [Nonempty X]
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ)
    (hc : ∀ x y, 0 ≤ c x y) (hcm : Measurable fun z : X × X => c z.1 z.2)
    (hfAll : ∀ μ : ProbabilityMeasure X, μ ∈ sinkhornBall c μhat ν κ ε →
        Integrable f (μ : Measure X))
    (h_exp : ∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure X))
    (hI_lp : ∀ lam, 0 < lam → Integrable
        (fun x => logPartition ν c f κ lam x) (μhat : Measure X))
    (hfbdd : BddAbove (Set.range f))
    (hfeas : (sinkhornBall c μhat ν κ ε).Nonempty)
    -- the `≥` direction — **the duality gap is zero**; strictly weaker than assuming an attaining
    -- worst-case measure (`sinkhornDual_le_droValue_of_attaining_measure` is the receipt).
    (hge : sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧ v = sinkhornDualObjective μhat ν c f κ ε lam }
        ≤ droValue (sinkhornBall c μhat ν κ ε) f) :
    droValue (sinkhornBall c μhat ν κ ε) f
      = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = sinkhornDualObjective μhat ν c f κ ε lam } := by
  -- the `BddAbove` gate follows from `f` being bounded above; it is not an assumption
  have hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
      μ ∈ sinkhornBall c μhat ν κ ε ∧ r = expect μ f } :=
    ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range _ f hfbdd hfAll
  refine le_antisymm ?_ ?_
  · refine csSup_le ?_ ?_
    · obtain ⟨μ, hμ⟩ := hfeas; exact ⟨expect μ f, μ, hμ, rfl⟩
    · rintro a ⟨μ, hμ, rfl⟩
      exact sinkhorn_cost_bound μhat ν c f κ ε hκ hc hcm μ hμ (hfAll μ hμ) h_exp hI_lp
  · exact hge

end WangGaoXie2023
