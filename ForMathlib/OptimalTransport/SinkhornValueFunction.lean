/-
# The entropic (Sinkhorn) DRO value function (Mathlib-staging)

`h t = sup { 𝔼_μ[f] : ∃ γ ∈ Π(μ̂, μ), 𝔼_γ[c] + κ·KL(γ‖μ̂⊗ν) ≤ t }`, and its concavity —
ingredient (3) of the `≥` half of Sinkhorn-DRO strong duality (Wang–Gao–Xie).

The Sinkhorn objective is **convex in the coupling**: `couplingCost` is affine
(`couplingCost_mix`) and `klDiv` is convex in its first argument
(`ForMathlib.MeasureTheory.klDiv_mix_le`, in `ℝ≥0∞` and hence supplying the mixture's finiteness
for free). The coupling set is convex in the *second* marginal (`mix_mem_couplings'`, the mirror of
`mix_mem_couplings` — Sinkhorn's nominal measure is the first marginal). So the constraint set is
convex and the value function concave.

## The domain is not `Ici 0`

Unlike the Wasserstein cost, the entropic objective **has no zero**: even `γ = μ̂⊗ν`, which kills the
KL term, pays `∫∫c dμ̂dν`. So `sinkhornValueSet … t` is empty for small `t`, and `sSup ∅ = 0` would
wreck both monotonicity and concavity on `Ici 0`. We therefore work on the *actual* domain
`sinkhornDomain = {t | (sinkhornValueSet … t).Nonempty}`, an upward-closed — hence convex — subset
of `ℝ`. Every objective value `t = sinkhornObjective … γ` lies in it, witnessed by `γ` itself, which
is exactly what the assembly needs.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.Convexity
import ForMathlib.OptimalTransport.DroValue

set_option autoImplicit false

open MeasureTheory InformationTheory ForMathlib.MeasureTheory
open scoped ENNReal NNReal

namespace ForMathlib.OT


section ValueFunction

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The achievable rewards at entropic budget `≤ t`. The `klDiv ≠ ⊤` field is not decoration:
`sinkhornObjective` reads the KL through `toReal`, which returns the junk value `0` on a coupling
singular against `μ̂⊗ν` — the worst coupling would otherwise score best. -/
def sinkhornValueSet (c : α → β → ℝ) (f : β → ℝ) (κ : ℝ) (μhat : ProbabilityMeasure α)
    (ν : ProbabilityMeasure β) (t : ℝ) : Set ℝ :=
  { r : ℝ | ∃ (μ : ProbabilityMeasure β) (γ : ProbabilityMeasure (α × β)),
      γ ∈ couplings μhat μ ∧ Integrable f (μ : Measure β) ∧
      Integrable (fun z : α × β => c z.1 z.2) (γ : Measure (α × β)) ∧
      klDiv (γ : Measure (α × β)) (prodMeasure μhat ν) ≠ ⊤ ∧
      sinkhornObjective c κ μhat ν γ ≤ t ∧ r = expect μ f }

/-- The **entropic DRO value function** `h t = sup (sinkhornValueSet … t)`. -/
noncomputable def sinkhornValueAt (c : α → β → ℝ) (f : β → ℝ) (κ : ℝ)
    (μhat : ProbabilityMeasure α) (ν : ProbabilityMeasure β) (t : ℝ) : ℝ :=
  sSup (sinkhornValueSet c f κ μhat ν t)

/-- The budgets at which *some* coupling is admissible. Upward closed, hence convex; and it contains
every attained objective value. -/
def sinkhornDomain (c : α → β → ℝ) (f : β → ℝ) (κ : ℝ) (μhat : ProbabilityMeasure α)
    (ν : ProbabilityMeasure β) : Set ℝ :=
  { t : ℝ | (sinkhornValueSet c f κ μhat ν t).Nonempty }

variable {c : α → β → ℝ} {f : β → ℝ} {κ : ℝ} {μhat : ProbabilityMeasure α}
  {ν : ProbabilityMeasure β} {C : ℝ}

/-- Relaxing the budget enlarges the achievable set. -/
theorem subset_sinkhornValueSet {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    sinkhornValueSet c f κ μhat ν t₁ ⊆ sinkhornValueSet c f κ μhat ν t₂ := by
  rintro r ⟨μ, γ, hγ, hfμ, hcγ, hkl, hobj, rfl⟩
  exact ⟨μ, γ, hγ, hfμ, hcγ, hkl, hobj.trans h, rfl⟩

/-- Bounded above, because `f` is. -/
theorem bddAbove_sinkhornValueSet (hfb : ∀ x, f x ≤ C) (t : ℝ) :
    BddAbove (sinkhornValueSet c f κ μhat ν t) := by
  refine ⟨C, ?_⟩
  rintro r ⟨μ, γ, -, hfμ, -, -, -, rfl⟩
  exact expect_le_of_le μ f C hfb hfμ

/-- Every attained objective value is a feasible budget, witnessed by its own coupling. -/
theorem mem_sinkhornDomain_of_coupling {μ : ProbabilityMeasure β} {γ : ProbabilityMeasure (α × β)}
    (hγ : γ ∈ couplings μhat μ) (hfμ : Integrable f (μ : Measure β))
    (hcγ : Integrable (fun z : α × β => c z.1 z.2) (γ : Measure (α × β)))
    (hkl : klDiv (γ : Measure (α × β)) (prodMeasure μhat ν) ≠ ⊤) :
    sinkhornObjective c κ μhat ν γ ∈ sinkhornDomain c f κ μhat ν :=
  ⟨expect μ f, μ, γ, hγ, hfμ, hcγ, hkl, le_rfl, rfl⟩

/-- The domain is upward closed. -/
theorem sinkhornDomain_upward {t₁ t₂ : ℝ} (h : t₁ ≤ t₂)
    (ht : t₁ ∈ sinkhornDomain c f κ μhat ν) : t₂ ∈ sinkhornDomain c f κ μhat ν :=
  ht.mono (subset_sinkhornValueSet h)

/-- An upward-closed subset of `ℝ` is convex. -/
theorem convex_sinkhornDomain : Convex ℝ (sinkhornDomain c f κ μhat ν) := by
  intro x hx y hy a b ha hb hab
  have hmin : min x y ≤ a * x + b * y := by
    have h1 : a * min x y ≤ a * x := mul_le_mul_of_nonneg_left (min_le_left _ _) ha
    have h2 : b * min x y ≤ b * y := mul_le_mul_of_nonneg_left (min_le_right _ _) hb
    have h3 : a * min x y + b * min x y = min x y := by rw [← add_mul, hab, one_mul]
    linarith
  refine sinkhornDomain_upward hmin ?_
  rcases le_total x y with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- **The entropic value function is nondecreasing** on its domain. -/
theorem monotoneOn_sinkhornValueAt (hfb : ∀ x, f x ≤ C) :
    MonotoneOn (sinkhornValueAt c f κ μhat ν) (sinkhornDomain c f κ μhat ν) :=
  fun _t₁ h₁ _t₂ _ hle =>
    csSup_le_csSup (bddAbove_sinkhornValueSet hfb _) h₁ (subset_sinkhornValueSet hle)

/-- **The entropic value function is concave** on its domain — ingredient (3) of the Sinkhorn `hge`.

Mix two near-optimal couplings. `mix_mem_couplings'` keeps the nominal first marginal fixed and
mixes the second; `couplingCost_mix` is affine; `klReal_mix_le` is convexity of `klDiv`, whose
`ℝ≥0∞` form (`klDiv_mix_ne_top'`) also certifies that the mixture stays out of the `toReal` junk
branch. -/
theorem concaveOn_sinkhornValueAt (hfb : ∀ x, f x ≤ C) (hκ : 0 ≤ κ) :
    ConcaveOn ℝ (sinkhornDomain c f κ μhat ν) (sinkhornValueAt c f κ μhat ν) := by
  haveI : IsProbabilityMeasure (prodMeasure μhat ν) := by
    haveI : IsProbabilityMeasure (μhat : Measure α) := μhat.2
    haveI : IsProbabilityMeasure (ν : Measure β) := ν.2
    rw [prodMeasure]; infer_instance
  refine ⟨convex_sinkhornDomain, fun t₁ h₁ t₂ h₂ a b ha hb hab => ?_⟩
  have hane : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha, by linarith⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨r₁, hr₁mem, hr₁⟩ := exists_lt_of_lt_csSup h₁
    (show sinkhornValueAt c f κ μhat ν t₁ - ε < sinkhornValueAt c f κ μhat ν t₁ by linarith)
  obtain ⟨r₂, hr₂mem, hr₂⟩ := exists_lt_of_lt_csSup h₂
    (show sinkhornValueAt c f κ μhat ν t₂ - ε < sinkhornValueAt c f κ μhat ν t₂ by linarith)
  obtain ⟨μ₁, γ₁, hγ₁, hf₁, hc₁, hkl₁, hobj₁, rfl⟩ := hr₁mem
  obtain ⟨μ₂, γ₂, hγ₂, hf₂, hc₂, hkl₂, hobj₂, rfl⟩ := hr₂mem
  have hac₁ : (γ₁ : Measure (α × β)) ≪ prodMeasure μhat ν := (klDiv_ne_top_iff.mp hkl₁).1
  have hac₂ : (γ₂ : Measure (α × β)) ≪ prodMeasure μhat ν := (klDiv_ne_top_iff.mp hkl₂).1
  have h1a : (0:ℝ) ≤ 1 - a := by linarith
  have hmemMix : a * expect μ₁ f + (1 - a) * expect μ₂ f
      ∈ sinkhornValueSet c f κ μhat ν (a * t₁ + (1 - a) * t₂) := by
    refine ⟨mix a hane μ₁ μ₂, mix a hane γ₁ γ₂, mix_mem_couplings' a hane hγ₁ hγ₂,
      integrable_mix a hane μ₁ μ₂ f hf₁ hf₂,
      integrable_mix a hane γ₁ γ₂ (fun z => c z.1 z.2) hc₁ hc₂,
      klDiv_mix_ne_top' a hane γ₁ γ₂ _ hac₁ hac₂ hkl₁ hkl₂, ?_, ?_⟩
    · have hcost := couplingCost_mix a hane γ₁ γ₂ c hc₁ hc₂
      have hklm := klReal_mix_le a hane γ₁ γ₂ (prodMeasure μhat ν) hac₁ hac₂ hkl₁ hkl₂
      simp only [sinkhornObjective] at hobj₁ hobj₂ ⊢
      rw [hcost]
      have ha1 := mul_le_mul_of_nonneg_left hobj₁ ha
      have ha2 := mul_le_mul_of_nonneg_left hobj₂ h1a
      have hkm := mul_le_mul_of_nonneg_left hklm hκ
      nlinarith [ha1, ha2, hkm]
    · exact (expect_mix a hane μ₁ μ₂ f hf₁ hf₂).symm
  have hle : a * expect μ₁ f + (1 - a) * expect μ₂ f
      ≤ sinkhornValueAt c f κ μhat ν (a * t₁ + (1 - a) * t₂) :=
    le_csSup (bddAbove_sinkhornValueSet hfb _) hmemMix
  have hb1 := mul_le_mul_of_nonneg_left hr₁.le ha
  have hb2 := mul_le_mul_of_nonneg_left hr₂.le h1a
  have h3 : a * ε + (1 - a) * ε = ε := by ring
  nlinarith [hb1, hb2, hle, h3]

end ValueFunction

end ForMathlib.OT
