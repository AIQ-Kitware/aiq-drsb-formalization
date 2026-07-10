/-
# The set of couplings is convex; cost and reward are affine on it

`Π(μ, ν)` is stable under convex combination: if `π₁` couples `μ₁` with `ν` and `π₂` couples `μ₂`
with `ν`, then `a·π₁ + (1−a)·π₂` couples `a·μ₁ + (1−a)·μ₂` with the *same* `ν`. Both `expect` and
`couplingCost` are affine in the measure, so the achievable `(reward, cost)` pairs form a convex set.

## Why

This is ingredient (3) of the `≥` half of Wasserstein-DRO strong duality
(`GaoKleywegt2023.strong_duality_thm1`'s `hge`): it makes the DRO value function

`h t = sup { 𝔼_μ[f] : ∃ π ∈ Π(μ,ν), 𝔼_π[c] ≤ t }`

**concave**, which is what lets `ForMathlib.Analysis.exists_nonneg_multiplier` produce the optimal
multiplier `λ*`. Ingredients (1) and (2) are `ForMathlib.OT.exists_coupling_lagrangian_ge` and
`ForMathlib.Analysis.exists_nonneg_multiplier`.

Note the second marginal is preserved *exactly* — `a·ν + (1−a)·ν = ν` — which is why the mixture
stays in the same ambiguity problem. That is the whole content of the convexity.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic

set_option autoImplicit false

open MeasureTheory ENNReal

namespace ForMathlib.OT

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The convex combination `a·μ₁ + (1−a)·μ₂` of two probability measures. -/
noncomputable def mix (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1)
    (μ₁ μ₂ : ProbabilityMeasure α) : ProbabilityMeasure α :=
  ⟨ENNReal.ofReal a • (μ₁ : Measure α) + ENNReal.ofReal (1 - a) • (μ₂ : Measure α), by
    constructor
    simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    rw [← ENNReal.ofReal_add ha.1 (by linarith [ha.2])]
    simp⟩

theorem mix_coe (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (μ₁ μ₂ : ProbabilityMeasure α) :
    (mix a ha μ₁ μ₂ : Measure α)
      = ENNReal.ofReal a • (μ₁ : Measure α) + ENNReal.ofReal (1 - a) • (μ₂ : Measure α) := rfl

/-- **The set of couplings is convex.** -/
theorem mix_mem_couplings (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1)
    {μ₁ μ₂ : ProbabilityMeasure α} {ν : ProbabilityMeasure β}
    {π₁ π₂ : ProbabilityMeasure (α × β)}
    (h₁ : π₁ ∈ couplings μ₁ ν) (h₂ : π₂ ∈ couplings μ₂ ν) :
    mix a ha π₁ π₂ ∈ couplings (mix a ha μ₁ μ₂) ν := by
  have hsum : ENNReal.ofReal a + ENNReal.ofReal (1 - a) = 1 := by
    rw [← ENNReal.ofReal_add ha.1 (by linarith [ha.2])]; simp
  constructor
  · show Measure.map Prod.fst (ENNReal.ofReal a • (π₁ : Measure (α × β))
        + ENNReal.ofReal (1 - a) • (π₂ : Measure (α × β)))
      = ENNReal.ofReal a • (μ₁ : Measure α) + ENNReal.ofReal (1 - a) • (μ₂ : Measure α)
    rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, h₁.1, h₂.1]
  · show Measure.map Prod.snd (ENNReal.ofReal a • (π₁ : Measure (α × β))
        + ENNReal.ofReal (1 - a) • (π₂ : Measure (α × β))) = (ν : Measure β)
    rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, h₁.2, h₂.2,
      ← add_smul, hsum, one_smul]

/-- `expect` is affine in the measure. -/
theorem expect_mix (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (μ₁ μ₂ : ProbabilityMeasure α) (f : α → ℝ)
    (h₁ : Integrable f (μ₁ : Measure α)) (h₂ : Integrable f (μ₂ : Measure α)) :
    expect (mix a ha μ₁ μ₂) f = a * expect μ₁ f + (1 - a) * expect μ₂ f := by
  have hne1 : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hne2 : ENNReal.ofReal (1 - a) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [expect, mix_coe, integral_add_measure (h₁.smul_measure hne1) (h₂.smul_measure hne2),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal ha.1, ENNReal.toReal_ofReal (by linarith [ha.2])]
  simp [expect, smul_eq_mul]


/-- `couplingCost` is affine in the coupling. It is literally `expect` of the uncurried cost, so
this is `expect_mix` at the product space. -/
theorem couplingCost_mix (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1)
    (π₁ π₂ : ProbabilityMeasure (α × β)) (c : α → β → ℝ)
    (h₁ : Integrable (fun z : α × β => c z.1 z.2) (π₁ : Measure (α × β)))
    (h₂ : Integrable (fun z : α × β => c z.1 z.2) (π₂ : Measure (α × β))) :
    couplingCost c (mix a ha π₁ π₂) = a * couplingCost c π₁ + (1 - a) * couplingCost c π₂ :=
  expect_mix a ha π₁ π₂ (fun z => c z.1 z.2) h₁ h₂

/-- Integrability is preserved by convex combination. -/
theorem integrable_mix (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (μ₁ μ₂ : ProbabilityMeasure α)
    (f : α → ℝ) (h₁ : Integrable f (μ₁ : Measure α)) (h₂ : Integrable f (μ₂ : Measure α)) :
    Integrable f (mix a ha μ₁ μ₂ : Measure α) := by
  rw [mix_coe]
  exact (h₁.smul_measure ENNReal.ofReal_ne_top).add_measure (h₂.smul_measure ENNReal.ofReal_ne_top)

/-- **The set of couplings is convex in the second marginal.** The mirror of `mix_mem_couplings`,
for the DRO problems whose nominal measure is the *first* marginal (Sinkhorn: `Π(μ̂, μ)`). -/
theorem mix_mem_couplings' (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1)
    {μ : ProbabilityMeasure α} {ν₁ ν₂ : ProbabilityMeasure β}
    {π₁ π₂ : ProbabilityMeasure (α × β)}
    (h₁ : π₁ ∈ couplings μ ν₁) (h₂ : π₂ ∈ couplings μ ν₂) :
    mix a ha π₁ π₂ ∈ couplings μ (mix a ha ν₁ ν₂) := by
  have hsum : ENNReal.ofReal a + ENNReal.ofReal (1 - a) = 1 := by
    rw [← ENNReal.ofReal_add ha.1 (by linarith [ha.2])]; simp
  constructor
  · show Measure.map Prod.fst (ENNReal.ofReal a • (π₁ : Measure (α × β))
        + ENNReal.ofReal (1 - a) • (π₂ : Measure (α × β))) = (μ : Measure α)
    rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, h₁.1, h₂.1,
      ← add_smul, hsum, one_smul]
  · show Measure.map Prod.snd (ENNReal.ofReal a • (π₁ : Measure (α × β))
        + ENNReal.ofReal (1 - a) • (π₂ : Measure (α × β)))
      = ENNReal.ofReal a • (ν₁ : Measure β) + ENNReal.ofReal (1 - a) • (ν₂ : Measure β)
    rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, h₁.2, h₂.2]

end ForMathlib.OT
