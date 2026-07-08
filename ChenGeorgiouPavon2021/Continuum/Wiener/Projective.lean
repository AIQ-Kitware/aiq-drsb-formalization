/-
# Concrete Wiener projective reductions

This module reduces normalized dyadic increment laws under concrete Wiener
measure to finite Brownian projective-family increment algebra.
-/

import ChenGeorgiouPavon2021.Continuum.Wiener.Concrete

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- The normalized dyadic increment law under Wiener measure reduces to a finite-dimensional
Brownian projective-family statement on the dyadic endpoint grid.

This is the main structural reduction needed before invoking independent-increment/product-Gaussian
lemmas for `BrownianReal.projectiveFamily`. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_reduce_to_projectiveFamily
    (level : ℕ) :
    Measure.map (normalizedWienerDyadicIncrementMap level) standardWienerMeasure
      = Measure.map (normalizedWienerDyadicIncrementFromGrid level)
          (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)) := by
  rw [normalizedWienerDyadicIncrementMap_eq_fromGrid level]
  let r : WienerRealPath → (wienerDyadicGrid level → ℝ) :=
    fun ω => (wienerDyadicGrid level).restrict ω
  let g : (wienerDyadicGrid level → ℝ) → (Fin (2 ^ level) → ℝ) :=
    normalizedWienerDyadicIncrementFromGrid level
  have hr : Measurable r := by
    dsimp [r]
    exact (wienerDyadicGrid level).measurable_restrict
  have hg : Measurable g := by
    dsimp [g]
    unfold normalizedWienerDyadicIncrementFromGrid dyadicMesh
    fun_prop
  have hmap : Measure.map g (Measure.map r standardWienerMeasure)
      = Measure.map (g ∘ r) standardWienerMeasure :=
    Measure.map_map hg hr
  change Measure.map (g ∘ r) standardWienerMeasure =
    Measure.map g (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
  rw [← hmap]
  rw [standardWienerMeasure_finite_coordinate_law (wienerDyadicGrid level)]

/-- Remaining Brownian finite-dimensional algebra capstone: under the Brownian projective-family law
on dyadic endpoint coordinates, normalized consecutive increments are iid standard Gaussian.

This is now the single finite-dimensional theorem left between the concrete Wiener construction and
the sequence-model Cameron--Martin theorem. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_law_target : Prop :=
  ∀ level : ℕ,
    Measure.map (normalizedWienerDyadicIncrementFromGrid level)
        (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- One-dimensional Brownian increment normalization target on the concrete dyadic grid.

For each dyadic edge, the corresponding normalized increment should have law `N(0,1)`.
This is the coordinate-level theorem that should follow from Mathlib's Brownian increment law
`measurePreserving_eval_sub_eval_projectiveFamily` plus the scaling `Δt = 2⁻ˡᵉᵛᵉˡ`. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_coord_law_target : Prop :=
  ∀ (level : ℕ) (i : Fin (2 ^ level)),
    Measure.map (fun x : wienerDyadicGrid level → ℝ =>
        normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = gaussianReal 0 1

/-- Finite-dimensional independence target for normalized dyadic increments.

Together with the coordinate law above, this is the product-law route to
`brownianProjectiveFamily_normalizedDyadicIncrement_law_target`.  It isolates the remaining
Brownian covariance/independent-increment work from the already-proved projective-limit reduction. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_indepFun_target : Prop :=
  ∀ level : ℕ,
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun x : wienerDyadicGrid level → ℝ =>
          normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))

/-- Next concrete capstone, now exposed as an ordinary theorem target instead of a hidden interface
field: derive the iid standard-normal law of normalized dyadic increments from
`isPreBrownianReal_standardWienerMeasure`, Brownian independent increments, and the Gaussian
product/normalization lemmas. -/
def normalizedWienerDyadicIncrementMap_standardWiener_law_target : Prop :=
  ∀ level : ℕ,
    Measure.map (normalizedWienerDyadicIncrementMap level) standardWienerMeasure
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- Concrete normalized dyadic iid-Gaussian law for the vendored Wiener measure, assuming the finite
Brownian projective-family increment algebra. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_of_projectiveFamily
    (hproj : brownianProjectiveFamily_normalizedDyadicIncrement_law_target) :
    normalizedWienerDyadicIncrementMap_standardWiener_law_target := by
  intro level
  rw [normalizedWienerDyadicIncrementMap_standardWiener_law_reduce_to_projectiveFamily level]
  exact hproj level

end ChenGeorgiouPavon2021
