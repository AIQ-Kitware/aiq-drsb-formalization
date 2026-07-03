/-
# Wang–Gao–Xie (2023), "Sinkhorn Distributionally Robust Optimization"

Core theorem library: the **Sinkhorn-DRO strong-duality** chain and its
**log-partition / log-sum-exp** dual, together with the **Gibbs (exponential-tilt)
worst-case distribution**. This is the source of the DRSB "Eq. 47" entropic
log-partition term.

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
import ForMathlib.MeasureTheory.DonskerVaradhan
set_option autoImplicit false
open MeasureTheory
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

/-- **Theorem 1 (Strong Duality), part (II)** — the load-bearing Sinkhorn-DRO
strong-duality identity `V = V_D` (prose "Strong duality theorem", Theorem 1(II);
dual is Eq. `(1)`).  The worst-case value over the Sinkhorn ball equals the infimum
over the dual multiplier `λ ≥ 0` of the log-partition dual objective:
  `sup_{P ∈ 𝓑_{ρ,ε}(P̂)} 𝔼_P[f] = inf_{λ≥0} { λρ + λε 𝔼_{x∼P̂}[log 𝔼_{z∼ν} e^{(f−λc)/(λε)}] }`.
Recall (symbol swap) our `κ` = paper regularizer `ε`, our `ε` = paper radius `ρ`,
so `sinkhornBall μhat κ ε = 𝓑_{ρ,ε}(P̂)`.

The hypotheses below transcribe **Assumption 1** (I)–(IV) and the `ρ ≥ 0` gate of
Theorem 1(II). Assumption 1(IV) (existence of a regular conditional distribution, e.g.
on a Polish space) is left as a prose-level side condition (not encoded). -/
theorem strong_duality
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ ε : ℝ)
    (hρ : 0 ≤ ε)                         -- Theorem 1(II): "whenever ρ ≥ 0" (our ε = paper ρ)
    (hκ : 0 < κ)                         -- ε > 0 (paper): positive entropic regularizer (paper allows ε ≥ 0 with λ↓0 limit conventions; we take ε > 0)
    (hf : Measurable f)                  -- Assumption 1(III): f measurable
    (hc : Measurable (fun p : X × X => c p.1 p.2))  -- Assumption 1(I): c is P̂⊗ν-measurable
    (hcnn : ∀ x z, 0 ≤ c x z)            -- Assumption 1(I): ν{z : 0 ≤ c(x,z) < ∞} = 1 (nonnegative, finite a.e.)
    (hK : ∀ xhat, Integrable (fun z => Real.exp (-(c xhat z) / κ)) (ν : Measure X)) :
        -- Assumption 1(II): 𝔼_{z∼ν}[e^{−c(x,z)/ε}] < ∞ (makes the cost-Gibbs kernel Q_{x,ε} well-defined)
    droValue (sinkhornBall μhat κ ε) f
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ v = sinkhornDualObjective μhat ν c f κ ε lam } := by
  sorry

/-- **Theorem 1(I) (Feasibility).** `(Primal)` is feasible iff the radius `ρ ≥ 0`
(our `ε ≥ 0`): the nominal `P̂` itself lies in the Sinkhorn ball. (Prose Theorem 1(I).) -/
theorem primal_feasible_iff
    (μhat : ProbabilityMeasure X) (κ ε : ℝ) :
    (sinkhornBall μhat κ ε).Nonempty ↔ 0 ≤ ε := by
  sorry

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
  · -- `((∫γ̃)⁻¹ • γ̃) univ = (∫γ̃)⁻¹ · (∫γ̃) = 1`
    intro xhat
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (hpos xhat) (hfin xhat)]
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

end WangGaoXie2023
