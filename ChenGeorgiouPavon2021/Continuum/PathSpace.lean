/-
# Ideal interval path-space carrier targets

This module records the path-space carrier facts that should eventually make the
continuum DRSB/M4 theorem live on a canonical anchored continuous interval path
space rather than on the ambient `RealPath := ℝ → ℝ` scaffold.
-/

import ChenGeorgiouPavon2021.Continuum.IntervalPath

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Canonical anchored continuous scalar paths on `[0,1]`.

This is the intended carrier for the final continuum Brownian/Cameron--Martin theorem:
continuous paths are determined by their values on dyadic/rational times, and the Brownian anchor
turns dyadic increments into dyadic coordinate values. -/
abbrev ContinuousAnchoredIntervalPath : Type :=
  {ω : IntervalPath // IntervalPathAnchored ω ∧ Continuous ω}

/-- Forget the anchored-continuous subtype back to the lightweight interval-path function space. -/
def continuousAnchoredIntervalPathToIntervalPath (ω : ContinuousAnchoredIntervalPath) : IntervalPath :=
  ω.1

/-- Normalized dyadic increments on the anchored-continuous interval carrier. -/
noncomputable def normalizedContinuousAnchoredIntervalDyadicIncrementMap (level : ℕ) :
    ContinuousAnchoredIntervalPath → (Fin (2 ^ level) → ℝ) :=
  fun ω => normalizedIntervalDyadicIncrementMap level ω.1

/-- Subtype extensionality for the anchored-continuous carrier.

This closes the non-analytic part of the path-space extensionality target: once the underlying
interval paths are equal, the subtype proof fields are proof-irrelevant. -/
theorem continuousAnchoredIntervalPath_ext_of_intervalPath_eq
    (ω η : ContinuousAnchoredIntervalPath)
    (h : continuousAnchoredIntervalPathToIntervalPath ω
      = continuousAnchoredIntervalPathToIntervalPath η) :
    ω = η := by
  exact Subtype.ext h

/-- Point-separation target reduced to equality of the underlying interval paths.

This is the remaining mathematical seam: the Brownian anchor recovers dyadic values from increments,
dyadic points are dense in `[0,1]`, and continuity extends equality from dyadic points to the whole
interval. -/
theorem continuousAnchoredIntervalPath_toIntervalPath_eq_of_normalizedDyadicIncrements_eq
    (ω η : ContinuousAnchoredIntervalPath)
    (hN : ∀ level : ℕ,
      normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω
        = normalizedContinuousAnchoredIntervalDyadicIncrementMap level η) :
    continuousAnchoredIntervalPathToIntervalPath ω
      = continuousAnchoredIntervalPathToIntervalPath η := by
  sorry

/-- Point-separation wrapper: anchored continuous paths are determined by all normalized dyadic
increment vectors. -/
theorem continuousAnchoredIntervalPath_ext_of_normalizedDyadicIncrements_eq
    (ω η : ContinuousAnchoredIntervalPath)
    (hN : ∀ level : ℕ,
      normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω
        = normalizedContinuousAnchoredIntervalDyadicIncrementMap level η) :
    ω = η := by
  exact continuousAnchoredIntervalPath_ext_of_intervalPath_eq ω η
    (continuousAnchoredIntervalPath_toIntervalPath_eq_of_normalizedDyadicIncrements_eq ω η hN)

/-- Generation target for the canonical anchored continuous interval path space.

This is the corrected replacement for the discarded overstrong theorem that dyadic increments on
`[0,1]` generate all of `RealPath := ℝ → ℝ`.  On the anchored continuous interval carrier, dyadic
increments should generate the Borel/subtype measurable space. -/
theorem normalizedContinuousAnchoredIntervalDyadicIncrementMap_iSup_comap_eq :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedContinuousAnchoredIntervalDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
      = (inferInstance : MeasurableSpace ContinuousAnchoredIntervalPath) := by
  sorry

end ChenGeorgiouPavon2021
