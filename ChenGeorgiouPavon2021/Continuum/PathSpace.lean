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

@[simp] theorem normalizedContinuousAnchoredIntervalDyadicIncrementMap_apply
    (level : ℕ) (ω : ContinuousAnchoredIntervalPath) (i : Fin (2 ^ level)) :
    normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω i
      = normalizedIntervalDyadicIncrementMap level ω.1 i := rfl

/-- Equality on the lightweight interval-path projection is enough to identify two elements of the
anchored-continuous subtype. -/
theorem continuousAnchoredIntervalPath_ext_of_intervalPath_eq
    {ω η : ContinuousAnchoredIntervalPath}
    (h : continuousAnchoredIntervalPathToIntervalPath ω
      = continuousAnchoredIntervalPathToIntervalPath η) :
    ω = η := by
  exact Subtype.ext h

/-- Pointwise equality on interval times is enough to identify two anchored-continuous paths. -/
theorem continuousAnchoredIntervalPath_ext_of_pointwise_eq
    {ω η : ContinuousAnchoredIntervalPath}
    (h : ∀ t : UnitInterval, ω.1 t = η.1 t) :
    ω = η := by
  apply continuousAnchoredIntervalPath_ext_of_intervalPath_eq
  funext t
  exact h t

/-- A levelwise equality of normalized dyadic vectors gives equality of every normalized dyadic
coordinate.  This is the finite-grid extraction step used before the remaining density/continuity
argument. -/
theorem normalizedContinuousAnchoredIntervalDyadicIncrement_eq_of_maps_eq
    {ω η : ContinuousAnchoredIntervalPath}
    (hN : ∀ level : ℕ,
      normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω
        = normalizedContinuousAnchoredIntervalDyadicIncrementMap level η)
    (level : ℕ) (i : Fin (2 ^ level)) :
    normalizedIntervalDyadicIncrementMap level ω.1 i
      = normalizedIntervalDyadicIncrementMap level η.1 i := by
  simpa using congrFun (hN level) i

/-- Pointwise equality target behind dyadic point separation.

Mathematically, the Brownian anchor recovers the dyadic values from increments, dyadic points are
dense in `[0,1]`, and continuity extends equality from dyadic points to every interval time. -/
theorem continuousAnchoredIntervalPath_pointwise_eq_of_normalizedDyadicIncrements_eq
    (ω η : ContinuousAnchoredIntervalPath)
    (hN : ∀ level : ℕ,
      normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω
        = normalizedContinuousAnchoredIntervalDyadicIncrementMap level η) :
    ∀ t : UnitInterval, ω.1 t = η.1 t := by
  sorry

/-- Point-separation target: anchored continuous paths are determined by all normalized dyadic
increment vectors. -/
theorem continuousAnchoredIntervalPath_ext_of_normalizedDyadicIncrements_eq
    (ω η : ContinuousAnchoredIntervalPath)
    (hN : ∀ level : ℕ,
      normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω
        = normalizedContinuousAnchoredIntervalDyadicIncrementMap level η) :
    ω = η := by
  exact continuousAnchoredIntervalPath_ext_of_pointwise_eq
    (continuousAnchoredIntervalPath_pointwise_eq_of_normalizedDyadicIncrements_eq ω η hN)

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
