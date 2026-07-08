/-
# Concrete Wiener measure interface

This module wraps the vendored Wiener measure construction on `NNReal → ℝ` and
records its finite-coordinate Brownian projective-family law.
-/

import ChenGeorgiouPavon2021.Continuum.Wiener.Grid

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Concrete standard Wiener measure on nonnegative-time real paths. -/
noncomputable def standardWienerMeasure : Measure WienerRealPath :=
  ForMathlib.MeasureTheory.wienerMeasure

/-- The concrete Wiener measure is a probability measure. -/
instance isProbabilityMeasure_standardWienerMeasure : IsProbabilityMeasure standardWienerMeasure := by
  dsimp [standardWienerMeasure]
  infer_instance

/-- Concrete standard-Wiener interface for measures on `NNReal → ℝ`.

This is the first real-Wiener capstone that follows directly from the vendored Kolmogorov
extension: the canonical coordinate process on `NNReal → ℝ` has the Brownian projective-family law.
The stronger normalized-dyadic-product law is now a downstream consequence target, not an implicit
`sorry` hidden inside this interface. -/
structure IsConcreteStandardWiener (W : Measure WienerRealPath) : Prop where
  is_probability : IsProbabilityMeasure W
  is_preBrownian : ProbabilityTheory.IsPreBrownianReal (fun t (ω : WienerRealPath) => ω t) W

/-- The canonical coordinate process under the vendored Wiener measure is a pre-Brownian motion.

This discharges the concrete projective-family part of the "real Wiener measure" capstone: every
finite coordinate marginal of `standardWienerMeasure` is exactly `BrownianReal.projectiveFamily`.
The proof is a direct wrapper around `ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure`. -/
theorem isPreBrownianReal_standardWienerMeasure :
    ProbabilityTheory.IsPreBrownianReal (fun t (ω : WienerRealPath) => ω t)
      standardWienerMeasure := by
  refine ProbabilityTheory.IsPreBrownianReal.mk' ?_
  intro I
  refine ⟨?_, ?_⟩
  · fun_prop
  · simpa [standardWienerMeasure] using
      (ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure I)

/-- The vendored concrete Wiener measure satisfies the focused nonnegative-time standard-Wiener
interface. -/
theorem isConcreteStandardWiener_standardWienerMeasure :
    IsConcreteStandardWiener standardWienerMeasure := by
  exact ⟨inferInstance, isPreBrownianReal_standardWienerMeasure⟩

/-- Finite-dimensional coordinate law of the concrete Wiener measure.

This is the direct projective-limit marginal statement: restricting a Wiener path to any finite set
of nonnegative times has Mathlib's Brownian projective-family law on that finite coordinate set. -/
theorem standardWienerMeasure_finite_coordinate_law (I : Finset NNReal) :
    Measure.map (fun ω : WienerRealPath => I.restrict ω) standardWienerMeasure
      = ProbabilityTheory.BrownianReal.projectiveFamily I := by
  simpa [standardWienerMeasure] using
    (ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure I)

end ChenGeorgiouPavon2021
