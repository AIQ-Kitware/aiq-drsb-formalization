/-
# The DRO value function is concave and nondecreasing

`h t = sup { 𝔼_μ[f] : ∃ π ∈ Π(μ,ν), 𝔼_π[c] ≤ t }` — the best expected reward achievable at
transport budget `t`.

## Why

This is **ingredient (3)** of the `≥` half of Wasserstein-DRO strong duality
(`GaoKleywegt2023.strong_duality_thm1`'s `hge`, Blanchet–Murthy Thm 1). The three ingredients:

1. `ForMathlib.OT.exists_coupling_lagrangian_ge` — the Lagrangian value `𝔼_ν[φ_λ]` is *achieved* by
   a pushforward along a measurable near-maximizer of the `c`-transform (no KRN needed);
2. `ForMathlib.Analysis.exists_nonneg_multiplier'` — a nondecreasing concave function on a convex
   set has a nonnegative supergradient `λ*` at an interior point, giving
   `h t + λ*·(δ − t) ≤ h δ`;
3. **this file** — `h` *is* nondecreasing and concave.

Concavity is exactly the convexity of the coupling set (`ForMathlib.OT.mix_mem_couplings`): mixing
two admissible plans `π₁, π₂` gives an admissible plan for the mixed budget, and both `expect` and
`couplingCost` are affine in the plan. Monotonicity is relaxing the budget.

The `BddAbove` hypothesis is `f` bounded above; the `Nonempty` hypothesis at some base budget `t₀`
is feasibility (Slater), and it propagates upward by monotonicity of the value set.

Chaining (1)–(3):
`dualValue = inf_λ (λδ + 𝔼_ν[φ_λ]) ≤ λ*δ + 𝔼_ν[φ_{λ*}] = sup_π (𝔼_μ[f] + λ*(δ − 𝔼_π[c]))`
`≤ sup_t (h t + λ*(δ − t)) ≤ h δ ≤ primalValue`.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.Convexity
import ForMathlib.OptimalTransport.DroValue

set_option autoImplicit false

open MeasureTheory

namespace ForMathlib.OT

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The achievable rewards at transport budget `≤ t`: expectations `𝔼_μ[f]` for sources `μ`
admitting a coupling with `ν` of cost at most `t`. -/
def droValueSet (c : α → β → ℝ) (f : α → ℝ) (ν : ProbabilityMeasure β) (t : ℝ) : Set ℝ :=
  { r : ℝ | ∃ (μ : ProbabilityMeasure α) (π : ProbabilityMeasure (α × β)),
      π ∈ couplings μ ν ∧ Integrable f (μ : Measure α) ∧
      Integrable (fun z : α × β => c z.1 z.2) (π : Measure (α × β)) ∧
      couplingCost c π ≤ t ∧ r = expect μ f }

/-- The **DRO value function** `h t = sup { 𝔼_μ[f] : ∃ π ∈ Π(μ,ν), 𝔼_π[c] ≤ t }`. -/
noncomputable def droValueAt (c : α → β → ℝ) (f : α → ℝ) (ν : ProbabilityMeasure β) (t : ℝ) : ℝ :=
  sSup (droValueSet c f ν t)

variable {c : α → β → ℝ} {f : α → ℝ} {ν : ProbabilityMeasure β} {C : ℝ}

/-- Bounded above, because `f` is. -/
theorem bddAbove_droValueSet (hfb : ∀ x, f x ≤ C) (t : ℝ) : BddAbove (droValueSet c f ν t) := by
  refine ⟨C, ?_⟩
  rintro r ⟨μ, π, -, hfμ, -, -, rfl⟩
  exact expect_le_of_le μ f C hfb hfμ

/-- Relaxing the budget enlarges the achievable set. -/
theorem subset_droValueSet {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    droValueSet c f ν t₁ ⊆ droValueSet c f ν t₂ := by
  rintro r ⟨μ, π, hπ, hfμ, hcπ, hcost, rfl⟩
  exact ⟨μ, π, hπ, hfμ, hcπ, hcost.trans h, rfl⟩

/-- **The DRO value function is nondecreasing.** -/
theorem monotoneOn_droValueAt (hfb : ∀ x, f x ≤ C) {t₀ : ℝ}
    (hne0 : (droValueSet c f ν t₀).Nonempty) :
    MonotoneOn (droValueAt c f ν) (Set.Ici t₀) := fun _t₁ h₁ t₂ _ hle =>
  csSup_le_csSup (bddAbove_droValueSet hfb t₂) (hne0.mono (subset_droValueSet h₁))
    (subset_droValueSet hle)

/-- **The DRO value function is concave** — ingredient (3) of `hge`.

Mix two near-optimal plans: `a·π₁ + (1−a)·π₂` couples `a·μ₁ + (1−a)·μ₂` with the *same* `ν`
(`mix_mem_couplings`), its cost is the mixed cost (`couplingCost_mix`) hence within the mixed
budget, and its reward is the mixed reward (`expect_mix`). -/
theorem concaveOn_droValueAt (hfb : ∀ x, f x ≤ C) {t₀ : ℝ}
    (hne0 : (droValueSet c f ν t₀).Nonempty) :
    ConcaveOn ℝ (Set.Ici t₀) (droValueAt c f ν) := by
  refine ⟨convex_Ici t₀, fun t₁ h₁ t₂ h₂ a b ha hb hab => ?_⟩
  have hane : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha, by linarith⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hne1 : (droValueSet c f ν t₁).Nonempty := hne0.mono (subset_droValueSet h₁)
  have hne2 : (droValueSet c f ν t₂).Nonempty := hne0.mono (subset_droValueSet h₂)
  obtain ⟨r₁, hr₁mem, hr₁⟩ := exists_lt_of_lt_csSup hne1
    (show droValueAt c f ν t₁ - ε < droValueAt c f ν t₁ by linarith)
  obtain ⟨r₂, hr₂mem, hr₂⟩ := exists_lt_of_lt_csSup hne2
    (show droValueAt c f ν t₂ - ε < droValueAt c f ν t₂ by linarith)
  obtain ⟨μ₁, π₁, hπ₁, hf₁, hc₁, hcost₁, rfl⟩ := hr₁mem
  obtain ⟨μ₂, π₂, hπ₂, hf₂, hc₂, hcost₂, rfl⟩ := hr₂mem
  -- the mixture is admissible at the mixed budget
  have hmemMix : a * expect μ₁ f + (1 - a) * expect μ₂ f
      ∈ droValueSet c f ν (a * t₁ + (1 - a) * t₂) := by
    refine ⟨mix a hane μ₁ μ₂, mix a hane π₁ π₂, mix_mem_couplings a hane hπ₁ hπ₂,
      integrable_mix a hane μ₁ μ₂ f hf₁ hf₂,
      integrable_mix a hane π₁ π₂ (fun z => c z.1 z.2) hc₁ hc₂, ?_, ?_⟩
    · rw [couplingCost_mix a hane π₁ π₂ c hc₁ hc₂]
      have h1a : 0 ≤ 1 - a := by linarith
      nlinarith [hcost₁, hcost₂]
    · exact (expect_mix a hane μ₁ μ₂ f hf₁ hf₂).symm
  have hle : a * expect μ₁ f + (1 - a) * expect μ₂ f
      ≤ droValueAt c f ν (a * t₁ + (1 - a) * t₂) :=
    le_csSup (bddAbove_droValueSet hfb (a * t₁ + (1 - a) * t₂)) hmemMix
  have h1a : 0 ≤ 1 - a := by linarith
  have k1 : a * (droValueAt c f ν t₁ - ε) ≤ a * expect μ₁ f :=
    mul_le_mul_of_nonneg_left hr₁.le ha
  have k2 : (1 - a) * (droValueAt c f ν t₂ - ε) ≤ (1 - a) * expect μ₂ f :=
    mul_le_mul_of_nonneg_left hr₂.le h1a
  have e1 : a * (droValueAt c f ν t₁ - ε) = a * droValueAt c f ν t₁ - a * ε := by ring
  have e2 : (1 - a) * (droValueAt c f ν t₂ - ε)
      = (1 - a) * droValueAt c f ν t₂ - (1 - a) * ε := by ring
  have e3 : a * ε + (1 - a) * ε = ε := by ring
  linarith [k1, k2, hle]


end ForMathlib.OT
