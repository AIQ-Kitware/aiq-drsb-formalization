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
import ForMathlib.MeasureTheory.Normalization
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

-- `strong_duality` (Theorem 1(II)) is proved below, after the weak-duality kernel it uses.

/-- **Theorem 1(I) (Feasibility), necessity direction.** For a nonnegative regularizer
`κ`, feasibility of `(Primal)` *requires* a nonnegative radius: if the Sinkhorn ball is
nonempty then `0 ≤ ε`. Axiom-clean.

Proof: `0 ≤ W_{κ,ν}(μ̂, μ)` for every `μ` — the Sinkhorn objective
`𝔼_γ[‖x−y‖²] + κ·KL(γ‖μ̂⊗ν)` is a sum of two nonnegatives (squared cost; `κ ≥ 0` times
`KL ≥ 0`), so its infimum over couplings is `≥ 0` — and any ball member satisfies
`W_{κ,ν}(μ̂, μ) ≤ ε`.

⚠ **Why this is the necessity half only, not the paper's full `↔ ρ ≥ 0`** (audit
resolution of the former `primal_feasible_iff` `sorry`, AGENTS.md §6 / the audit note in
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
absent from Mathlib, §6 T4) and stays deferred; the necessity below is unconditional. -/
theorem primal_feasible_radius_nonneg
    (μhat ν : ProbabilityMeasure X) (κ ε : ℝ) (hκ : 0 ≤ κ)
    (h : (sinkhornBall μhat ν κ ε).Nonempty) : 0 ≤ ε := by
  obtain ⟨μ, hμ⟩ := h
  -- `hμ : W_{κ,ν}(μ̂, μ) ≤ ε` (ball membership is the defining inequality)
  have hW : 0 ≤ Wkappa κ ν μhat μ := by
    unfold Wkappa
    apply Real.sInf_nonneg
    rintro r ⟨γ, _, rfl⟩
    -- each candidate value is `couplingCost2 γ + κ·klReal(γ ‖ μ̂⊗ν) ≥ 0`
    have h1 : 0 ≤ couplingCost2 γ := by
      unfold couplingCost2 couplingCost
      exact integral_nonneg (fun z => sq_nonneg _)
    have h2 : 0 ≤ klReal (γ : Measure (X × X)) (prodMeasure μhat ν) :=
      ENNReal.toReal_nonneg
    unfold sinkhornObjective
    exact add_nonneg h1 (mul_nonneg hκ h2)
  exact le_trans hW hμ

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
hypotheses make the per-point DV bound apply and the aggregate integrals well defined. -/
theorem sinkhorn_weak_duality_kernel
    (p₀ ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ)
    (hκ : 0 < κ) (hlam : 0 < lam)
    (P : X → Measure X) (hP : ∀ x, IsProbabilityMeasure (P x))
    (hac : ∀ x, P x ≪ (ν : Measure X))
    (hf_P : ∀ x, Integrable f (P x))
    (hc_P : ∀ x, Integrable (fun y => c x y) (P x))
    (h_llr : ∀ x, Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x))
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
  -- per-nominal-point Gibbs/DV bound
  have hpt : ∀ x, (∫ y, f y ∂(P x))
      ≤ lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure X)
        + logPartition ν c f κ lam x := by
    intro x
    haveI := hP x
    have hsub : Integrable (fun y => f y - lam * c x y) (P x) :=
      (hf_P x).sub ((hc_P x).const_mul lam)
    have hA_int : Integrable (fun y => (f y - lam * c x y) / (lam * κ)) (P x) :=
      hsub.div_const _
    have hDV := ForMathlib.MeasureTheory.integral_le_klDiv_add_log_integral_exp
      (hac x) hA_int (h_llr x) (h_exp x)
    have hAeq : (∫ y, (f y - lam * c x y) / (lam * κ) ∂(P x))
        = (lam * κ)⁻¹ * ((∫ y, f y ∂(P x)) - lam * ∫ y, c x y ∂(P x)) := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_sub (hf_P x) ((hc_P x).const_mul lam),
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
          + logPartition ν c f κ lam x) ∂(p₀ : Measure X) := integral_mono hI_f hRHS_int hpt
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

/-- **Theorem 1 (Strong Duality), part (II)** — `V = V_D`: the Sinkhorn-DRO worst-case
value over the ball equals the log-partition dual. `le_antisymm` of `droValue ≤ dual`
(each source's Sinkhorn cost bound, inlined from `sinkhorn_weak_duality_kernel` + `le_csInf`,
via `csSup_le`) and `dual ≤ droValue` (the attaining worst-case measure, `le_csSup`).

The paper's Assumption 1 is replaced by the operational **edges** that make it provable:
`hSinkAll` (the `∀ μ` attainment+disintegration bundle — the OT measurable-selection +
`condKernel` disintegration + KL chain rule, §6), `hbddP`, `hattain`; the dual runs over
`0 < lam` (the `lam=0` `logPartition` is junk, cf. `Drsb.sdrsb_cost_bound`). -/
theorem strong_duality
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ)
    (hSinkAll : ∀ μ : ProbabilityMeasure X, μ ∈ sinkhornBall μhat ν κ ε →
      (Wkappa κ ν μhat μ ≤ ε →
        ∃ P : X → Measure X,
          (∀ x, IsProbabilityMeasure (P x)) ∧ (∀ x, P x ≪ (ν : Measure X)) ∧
          expect μ f = (∫ x, (∫ y, f y ∂(P x)) ∂(μhat : Measure X)) ∧
          (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure X))
              ∂(μhat : Measure X)) ≤ ε ∧
          (∀ x, Integrable f (P x)) ∧ (∀ x, Integrable (fun y => c x y) (P x)) ∧
          (∀ x, Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x)) ∧
          (∀ lam, 0 < lam → ∀ x, Integrable
              (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure X)) ∧
          Integrable (fun x => ∫ y, f y ∂(P x)) (μhat : Measure X) ∧
          Integrable (fun x => ∫ y, c x y ∂(P x)) (μhat : Measure X) ∧
          Integrable (fun x => klReal (P x) (ν : Measure X)) (μhat : Measure X) ∧
          (∀ lam, 0 < lam → Integrable
              (fun x => logPartition ν c f κ lam x) (μhat : Measure X))))
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ sinkhornBall μhat ν κ ε ∧ r = expect μ f })
    (hattain : ∃ μ : ProbabilityMeasure X, μ ∈ sinkhornBall μhat ν κ ε ∧
        expect μ f = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = sinkhornDualObjective μhat ν c f κ ε lam }) :
    droValue (sinkhornBall μhat ν κ ε) f
      = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = sinkhornDualObjective μhat ν c f κ ε lam } := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ?_ ?_
    · obtain ⟨μ, hμ, _⟩ := hattain; exact ⟨expect μ f, μ, hμ, rfl⟩
    · rintro a ⟨μ, hμ, rfl⟩
      obtain ⟨P, hP, hac, hVdis, hbudget, hf_P, hc_P, h_llr, h_exp, hI_f, hI_c, hI_kl, hI_lp⟩ :=
        hSinkAll μ hμ hμ
      refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
      rintro d ⟨lam, hlam, rfl⟩
      have key := sinkhorn_weak_duality_kernel μhat ν c f κ lam hκ hlam P hP hac
        hf_P hc_P h_llr (h_exp lam hlam) hI_f hI_c hI_kl (hI_lp lam hlam)
      have hb := mul_le_mul_of_nonneg_left hbudget (le_of_lt hlam)
      rw [hVdis]
      simp only [sinkhornDualObjective, expect]
      linarith [key, hb]
  · obtain ⟨μ, hμ, hμeq⟩ := hattain
    rw [← hμeq]
    exact le_csSup hbddP ⟨μ, hμ, rfl⟩

end WangGaoXie2023
