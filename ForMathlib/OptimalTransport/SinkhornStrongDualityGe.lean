/-
# The entropic duality gap is zero: the `≥` half of Sinkhorn-DRO strong duality

**`hge` for the entropic ball, proved.** Wang–Gao–Xie Theorem 1's `≥` direction:

`inf_{λ>0} ( λε + 𝔼_μ̂[λκ·log ∫ exp((f − λc(x,·))/(λκ)) dν] ) ≤ sup { 𝔼_μ[f] : W_{κ,ν}(μ̂,μ) ≤ ε }`.

## The three ingredients

1. `ForMathlib.OT.exists_coupling_sinkhorn_lagrangian_eq` — the **converse Lagrangian bound**, an
   *equality* with an explicit witness `γ = μ̂ ⊗ₘ P`, `P` the tilted kernel. The Gibbs
   (over-measures) Donsker–Varadhan supremum is attained, so unlike the Wasserstein path there is
   no `ε` to lose and no measurable ε-argmax selection to perform.
2. `ForMathlib.Analysis.exists_nonneg_multiplier'` — the **optimal multiplier** `λ*`.
3. `ForMathlib.OT.concaveOn_sinkhornValueAt` — the **entropic value function is concave**, because
   `couplingCost` is affine and `klDiv` is convex (`ForMathlib.MeasureTheory.klDiv_mix_le`).

## Slater, and why it is not optional

The Wasserstein assembly takes its supergradient at `δ > 0` knowing the value set is nonempty at
`t = 0`: the diagonal coupling has zero cost. **The entropic objective has no zero** — even `γ = μ̂⊗ν`
pays `∫∫c dμ̂dν`. So `ε` is interior to the value function's domain exactly when some coupling is
*strictly* feasible, and we take that as the hypothesis `ht₀ : t₀ ∈ sinkhornDomain`, `ht₀ε : t₀ < ε`.
Mere feasibility (`ε ≥ inf_γ obj γ`) is **not** enough for this argument, and no rearrangement of the
proof avoids it. This is a strictly better assumption surface than `hge` itself: Slater is
checkable, `hge` is the conclusion.

## The assembly

Run (1) at `λ = λ* + η` for small `η > 0` — never at `λ*`, so that `λ > 0` is available and the
`λ* = 0` case needs no separate treatment. With `t = sinkhornObjective … γ ≥ 0`, which lies in the
domain because `γ` itself witnesses it:

`λε + 𝔼_μ̂[v(λ)] = 𝔼_μ[f] + λ(ε − t) = 𝔼_μ[f] + λ*(ε − t) + η(ε − t) ≤ h ε + ηε ≤ h ε + δ`.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.Coupling
import ForMathlib.OptimalTransport.DroValue
import ForMathlib.OptimalTransport.SinkhornConverse
import ForMathlib.OptimalTransport.SinkhornValueFunction
import ForMathlib.Analysis.Supergradient

set_option autoImplicit false

open MeasureTheory InformationTheory ForMathlib.Analysis
open scoped ENNReal

namespace ForMathlib.OT

variable {X : Type*} [MeasurableSpace X]

/-- The entropic objective is nonnegative when the transport cost is. -/
theorem sinkhornObjective_nonneg {c : X → X → ℝ} (hc0 : ∀ x y, 0 ≤ c x y) {κ : ℝ} (hκ : 0 ≤ κ)
    (μhat ν : ProbabilityMeasure X) (γ : ProbabilityMeasure (X × X)) :
    0 ≤ sinkhornObjective c κ μhat ν γ := by
  have h1 : 0 ≤ couplingCost c γ := integral_nonneg fun z => hc0 z.1 z.2
  have h2 : 0 ≤ klReal (γ : Measure (X × X)) (prodMeasure μhat ν) := ENNReal.toReal_nonneg
  simp only [sinkhornObjective]
  nlinarith

/-- **The dual value is at most the entropic value function at the radius.** The heart of the
Sinkhorn `hge`. -/
theorem sinkhornDual_le_sinkhornValueAt
    [MeasurableSpace.CountableOrCountablyGenerated X X]
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ ε : ℝ)
    (hκ : 0 < κ) (hc0 : ∀ x y, 0 ≤ c x y)
    (hfm : Measurable f) (hcm : Measurable fun z : X × X => c z.1 z.2)
    (C : ℝ) (hfb : ∀ x, f x ≤ C)
    (hexp : ∀ lam : ℝ, 0 < lam → ∀ x, Integrable
      (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure X))
    (hf_P : ∀ lam : ℝ, 0 < lam → ∀ x, Integrable f
      ((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ)))
    (hc_P : ∀ lam : ℝ, 0 < lam → ∀ x, Integrable (fun y => c x y)
      ((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ)))
    (hf_norm : ∀ lam : ℝ, 0 < lam → Integrable (fun x => ∫ y, ‖f y‖
      ∂((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ))) (μhat : Measure X))
    (hc_norm : ∀ lam : ℝ, 0 < lam → Integrable (fun x => ∫ y, ‖c x y‖
      ∂((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ))) (μhat : Measure X))
    (hklint : ∀ lam : ℝ, 0 < lam → Integrable (fun x => klReal
      ((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ)) (ν : Measure X))
      (μhat : Measure X))
    {t₀ : ℝ} (ht₀ : t₀ ∈ sinkhornDomain c f κ μhat ν) (ht₀ε : t₀ < ε)
    (hBdd : BddBelow { v : ℝ | ∃ lam : ℝ, 0 < lam ∧ v = lam * ε
      + expect μhat (fun x => lam * κ * Real.log
          (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure X))) }) :
    sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧ v = lam * ε
      + expect μhat (fun x => lam * κ * Real.log
          (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure X))) }
      ≤ sinkhornValueAt c f κ μhat ν ε := by
  classical
  -- the Slater point is nonnegative, hence so is the radius
  have ht₀0 : 0 ≤ t₀ := by
    obtain ⟨r, μ, γ, -, -, -, -, hobj, -⟩ := ht₀
    exact le_trans (sinkhornObjective_nonneg hc0 hκ.le μhat ν γ) hobj
  have hε0 : 0 < ε := lt_of_le_of_lt ht₀0 ht₀ε
  have hεmem : ε ∈ sinkhornDomain c f κ μhat ν := sinkhornDomain_upward ht₀ε.le ht₀
  have hbmem : ε + 1 ∈ sinkhornDomain c f κ μhat ν :=
    sinkhornDomain_upward (by linarith) hεmem
  obtain ⟨lstar, hl0, hmul⟩ := exists_nonneg_multiplier'
    (s := sinkhornDomain c f κ μhat ν)
    (concaveOn_sinkhornValueAt hfb hκ.le) (monotoneOn_sinkhornValueAt hfb)
    ht₀ hbmem ht₀ε (by linarith) hεmem
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set η : ℝ := min 1 (δ / (2 * ε)) with hηdef
  have hη : 0 < η := lt_min one_pos (div_pos hδ (by linarith))
  have hηε : η * ε ≤ δ / 2 := by
    have h1 : η ≤ δ / (2 * ε) := min_le_right _ _
    calc η * ε ≤ (δ / (2 * ε)) * ε := mul_le_mul_of_nonneg_right h1 hε0.le
      _ = δ / 2 := by field_simp
  set lam : ℝ := lstar + η with hlamdef
  have hlam : 0 < lam := by positivity
  obtain ⟨μ, γ, hγ, hfμ, hcγ, hkltop, heq⟩ := exists_coupling_sinkhorn_lagrangian_eq
    μhat ν c f κ lam hκ hlam hfm hcm (hexp lam hlam) (hf_P lam hlam) (hc_P lam hlam)
    (hf_norm lam hlam) (hc_norm lam hlam) (hklint lam hlam)
  set t : ℝ := sinkhornObjective c κ μhat ν γ with htdef
  have hts : t ∈ sinkhornDomain c f κ μhat ν :=
    mem_sinkhornDomain_of_coupling hγ hfμ hcγ hkltop
  have ht0 : 0 ≤ t := sinkhornObjective_nonneg hc0 hκ.le μhat ν γ
  have hexpect : expect μ f ≤ sinkhornValueAt c f κ μhat ν t :=
    le_csSup (bddAbove_sinkhornValueSet hfb t) ⟨μ, γ, hγ, hfμ, hcγ, hkltop, le_rfl, rfl⟩
  have hmt := hmul t hts
  have hinf : sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧ v = lam * ε
      + expect μhat (fun x => lam * κ * Real.log
          (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure X))) }
      ≤ lam * ε + expect μhat (fun x => lam * κ * Real.log
          (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure X))) :=
    csInf_le hBdd ⟨lam, hlam, rfl⟩
  have hd : lam * ε - lam * t = lam * (ε - t) := by ring
  have hsplit : lam * (ε - t) = lstar * (ε - t) + η * (ε - t) := by rw [hlamdef]; ring
  have h4 : η * (ε - t) ≤ η * ε := by nlinarith [ht0, hη.le]
  linarith [hinf, heq, hexpect, hmt, hd, hsplit, h4, hηε]

/-- The entropic value function at the radius is at most the DRO primal value: a coupling of
objective `≤ ε` witnesses `W_{κ,ν} ≤ ε`, so its second marginal lies in the Sinkhorn ball. -/
theorem sinkhornValueAt_le_droValue
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ ε : ℝ)
    (hκ : 0 < κ) (hc0 : ∀ x y, 0 ≤ c x y) (hcm : Measurable fun z : X × X => c z.1 z.2)
    (C : ℝ) (hfb : ∀ x, f x ≤ C)
    (hne : (sinkhornValueSet c f κ μhat ν ε).Nonempty)
    (hfint : ∀ μ : ProbabilityMeasure X, μ ∈ sinkhornBall c μhat ν κ ε →
      Integrable f (μ : Measure X)) :
    sinkhornValueAt c f κ μhat ν ε ≤ droValue (sinkhornBall c μhat ν κ ε) f := by
  refine csSup_le_csSup ?_ hne ?_
  · exact bddAbove_expect_set_of_bddAbove_range _ f
      ⟨C, by rintro _ ⟨x, rfl⟩; exact hfb x⟩ hfint
  · rintro r ⟨μ, γ, hγ, hfμ, hcγ, hkltop, hobj, rfl⟩
    refine ⟨μ, ?_, rfl⟩
    have hcENN : couplingCostENN c γ ≠ ⊤ := hcγ.lintegral_lt_top.ne
    have hobjENN : sinkhornObjectiveENN c κ μhat ν γ ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hcENN, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hkltop⟩
    have hW : Wkappa c κ ν μhat μ ≤ sinkhornObjectiveENN c κ μhat ν γ := iInf₂_le γ hγ
    refine ⟨ne_top_of_le_ne_top hobjENN hW, ?_⟩
    calc (Wkappa c κ ν μhat μ).toReal
        ≤ (sinkhornObjectiveENN c κ μhat ν γ).toReal := ENNReal.toReal_mono hobjENN hW
      _ = sinkhornObjective c κ μhat ν γ :=
          (sinkhornObjective_eq_toReal_of_ne_top hc0 hcm hκ.le hobjENN).symm
      _ ≤ ε := hobj

end ForMathlib.OT
