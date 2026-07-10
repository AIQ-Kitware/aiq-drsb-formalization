/-
# The DRO worst-case value: boundedness and elementary bounds (Mathlib-staging)

`droValue 𝓐 f = sSup { 𝔼_μ[f] : μ ∈ 𝓐 }` is a `sSup` of real numbers, so every theorem about it
needs the value set to be bounded above before `le_csSup`/`csSup_le` say anything. That hypothesis
is traditionally carried as an opaque `BddAbove {r | ∃ μ ∈ 𝓐, r = expect μ f}` side condition.

It is not an opaque side condition. **A function bounded above has bounded-above expectations**,
uniformly over *every* set of probability measures that integrates it. Since a DRO dual's
`λ = 0` term already asserts `BddAbove (Set.range f)` (the conjugate `sup_x (f x − 0·c)` must be
finite), the `BddAbove` hypothesis is redundant wherever the dual ranges over `λ ≥ 0`.

This file makes that precise so the strong-duality statements can drop it.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic

set_option autoImplicit false

open MeasureTheory

namespace ForMathlib.OT

variable {X : Type*} [MeasurableSpace X]

/-- A probability measure's expectation of a function bounded above by `M` is at most `M`. -/
theorem expect_le_of_le (μ : ProbabilityMeasure X) (f : X → ℝ)
    (M : ℝ) (hf : ∀ x, f x ≤ M) (hint : Integrable f (μ : Measure X)) :
    expect μ f ≤ M := by
  haveI : IsProbabilityMeasure (μ : Measure X) := μ.2
  calc expect μ f = ∫ x, f x ∂(μ : Measure X) := rfl
    _ ≤ ∫ _x, M ∂(μ : Measure X) := integral_mono hint (integrable_const M) hf
    _ = M := by simp

/-- **The DRO value set is bounded above as soon as the objective is.** No property of the
ambiguity set `𝓐` is used beyond integrability of `f` on it.

This discharges the `BddAbove` (`hbddP`) hypothesis of every DRO strong-duality theorem whose dual
ranges over `λ ≥ 0`: the `λ = 0` term of such a dual is `𝔼_ν[sup_x (f x − 0 · c x ·)] = sup_x f x`,
so its finiteness — which those theorems already assume, as the `λ = 0` case of the conjugate's
`BddAbove` hypothesis — is exactly `BddAbove (Set.range f)`. -/
theorem bddAbove_expect_set_of_bddAbove_range (𝓐 : Set (ProbabilityMeasure X)) (f : X → ℝ)
    (hf : BddAbove (Set.range f))
    (hint : ∀ μ : ProbabilityMeasure X, μ ∈ 𝓐 → Integrable f (μ : Measure X)) :
    BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X, μ ∈ 𝓐 ∧ r = expect μ f } := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨M, ?_⟩
  rintro r ⟨μ, hμ, rfl⟩
  exact expect_le_of_le μ f M (fun x => hM ⟨x, rfl⟩) (hint μ hμ)

omit [MeasurableSpace X] in
/-- The `λ = 0` instance of a conjugate-`BddAbove` hypothesis *is* `BddAbove (Set.range f)`.
Stated separately because the `- 0 * c x y` needs clearing before the two match syntactically. -/
theorem bddAbove_range_of_bddAbove_dualIntegrand (f : X → ℝ) (c : X → X → ℝ) (y : X)
    (h : BddAbove (Set.range (fun x => f x - 0 * c x y))) :
    BddAbove (Set.range f) := by
  simpa using h

end ForMathlib.OT
