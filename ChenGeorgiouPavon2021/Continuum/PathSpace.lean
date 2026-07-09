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

/-- The zeroth dyadic grid point is the interval anchor. -/
theorem intervalDyadicTime_zero (level : ℕ) :
    intervalDyadicTime level 0 = unitIntervalZero := by
  apply Subtype.ext
  simp [intervalDyadicTime, dyadicTime, unitIntervalZero]

/-- Bounded dyadic grid points, indexed by a countable subtype of `(level, vertex)`.

The bound `i ≤ 2^level` records the true finite grid vertices, including both endpoints.
Out-of-range natural indices in `intervalDyadicTime` are a clamped implementation detail and are
not used in the density/separation argument. -/
noncomputable def boundedIntervalDyadicGridPoint :
    {p : ℕ × ℕ // p.2 ≤ 2 ^ p.1} → UnitInterval :=
  fun p => intervalDyadicTime p.1.1 p.1.2

/-- The true bounded dyadic grid points are dense in the interval carrier.

This is the remaining real-analysis seam for path separation: every `t ∈ [0,1]` is a limit of
vertices `i / 2^level` with `0 ≤ i ≤ 2^level`. -/
theorem denseRange_boundedIntervalDyadicGridPoint :
    DenseRange boundedIntervalDyadicGridPoint := by
  sorry

/-- Anchored continuous interval paths agree at the zeroth dyadic grid point. -/
theorem continuousAnchoredIntervalPath_dyadicGrid_zero_eq
    (ω η : ContinuousAnchoredIntervalPath) (level : ℕ) :
    continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level 0)
      = continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level 0) := by
  rw [intervalDyadicTime_zero level]
  calc
    continuousAnchoredIntervalPathToIntervalPath ω unitIntervalZero = 0 := ω.2.1
    _ = continuousAnchoredIntervalPathToIntervalPath η unitIntervalZero := (η.2.1).symm

/-- One raw dyadic increment step transports equality from one grid vertex to the next. -/
theorem continuousAnchoredIntervalPath_dyadicGrid_succ_eq_of_increment_eq
    (ω η : ContinuousAnchoredIntervalPath) (level : ℕ) (i : Fin (2 ^ level))
    (hinc : intervalDyadicIncrement level
        (continuousAnchoredIntervalPathToIntervalPath ω) i
      = intervalDyadicIncrement level
        (continuousAnchoredIntervalPathToIntervalPath η) i)
    (hbase : continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level i.1)
      = continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level i.1)) :
    continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level (i.1 + 1))
      = continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level (i.1 + 1)) := by
  unfold intervalDyadicIncrement at hinc
  calc
    continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level (i.1 + 1))
        = (continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level (i.1 + 1))
            - continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level i.1))
          + continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level i.1) := by ring
    _ = (continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level (i.1 + 1))
            - continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level i.1))
          + continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level i.1) := by
            rw [hinc, hbase]
    _ = continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level (i.1 + 1)) := by ring

/-- Normalized dyadic increment equality implies raw dyadic increment equality.

This is the small nonzero-mesh algebra seam needed before the finite telescoping induction can use
`continuousAnchoredIntervalPath_dyadicGrid_succ_eq_of_increment_eq`. -/
theorem intervalDyadicIncrement_eq_of_normalizedContinuousAnchoredIntervalDyadicIncrement_eq
    (ω η : ContinuousAnchoredIntervalPath) (level : ℕ) (i : Fin (2 ^ level))
    (hN : normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω
      = normalizedContinuousAnchoredIntervalDyadicIncrementMap level η) :
    intervalDyadicIncrement level
        (continuousAnchoredIntervalPathToIntervalPath ω) i
      = intervalDyadicIncrement level
        (continuousAnchoredIntervalPathToIntervalPath η) i := by
  change intervalDyadicIncrement level ω.1 i = intervalDyadicIncrement level η.1 i
  have hpoint :
      intervalDyadicIncrement level ω.1 i / Real.sqrt (dyadicMesh level)
        = intervalDyadicIncrement level η.1 i / Real.sqrt (dyadicMesh level) := by
    simpa [normalizedContinuousAnchoredIntervalDyadicIncrementMap,
      normalizedIntervalDyadicIncrementMap, normalizedIntervalDyadicIncrement] using congrFun hN i
  have hsqrt_ne : Real.sqrt (dyadicMesh level) ≠ 0 := by
    have hmesh_pos : 0 < dyadicMesh level := by
      unfold dyadicMesh
      positivity
    exact ne_of_gt (Real.sqrt_pos.2 hmesh_pos)
  field_simp [hsqrt_ne] at hpoint
  exact hpoint

/-- Bounded finite telescoping target for dyadic grid values.

After normalized increments are converted to raw increment equality, this is a pure finite induction
from the anchor at `0`.  The unbounded wrapper below only uses this theorem at true grid vertices
`i ≤ 2^level`; out-of-range clamped values should be handled separately as the right endpoint. -/
theorem continuousAnchoredIntervalPath_dyadicGrid_eq_of_rawIncrements_eq
    (ω η : ContinuousAnchoredIntervalPath) (level i : ℕ) (hi : i ≤ 2 ^ level)
    (hinc : ∀ k : Fin (2 ^ level),
      intervalDyadicIncrement level (continuousAnchoredIntervalPathToIntervalPath ω) k
        = intervalDyadicIncrement level (continuousAnchoredIntervalPathToIntervalPath η) k) :
    continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level i)
      = continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level i) := by
  induction i with
  | zero =>
      exact continuousAnchoredIntervalPath_dyadicGrid_zero_eq ω η level
  | succ i ih =>
      have hi_pred : i ≤ 2 ^ level := Nat.le_trans (Nat.le_succ i) hi
      have hi_fin : i < 2 ^ level := Nat.lt_of_succ_le hi
      exact continuousAnchoredIntervalPath_dyadicGrid_succ_eq_of_increment_eq ω η level
        ⟨i, hi_fin⟩ (hinc ⟨i, hi_fin⟩) (ih hi_pred)

/-- Dyadic increment equality recovers equality at every true finite dyadic grid point.

The bounded index `i ≤ 2^level` is the honest finite-grid statement; unbounded natural indices in
`intervalDyadicTime` are merely a clamped implementation detail, not part of the mathematical grid. -/
theorem continuousAnchoredIntervalPath_dyadicGrid_eq_of_normalizedDyadicIncrements_eq
    (ω η : ContinuousAnchoredIntervalPath)
    (hN : ∀ level : ℕ,
      normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω
        = normalizedContinuousAnchoredIntervalDyadicIncrementMap level η) :
    ∀ level i, i ≤ 2 ^ level →
      continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level i)
        = continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level i) := by
  intro level i hi
  exact continuousAnchoredIntervalPath_dyadicGrid_eq_of_rawIncrements_eq ω η level i hi
    (fun k => intervalDyadicIncrement_eq_of_normalizedContinuousAnchoredIntervalDyadicIncrement_eq
      ω η level k (hN level))

/-- General interval-path density seam for dyadic-grid equality.

This is the topological/density part of path separation, stated without the anchored subtype:
bounded dyadic grid points are dense in `[0,1]`, and two continuous interval paths agreeing on that
dense grid agree everywhere. -/
theorem intervalPath_eq_of_continuous_of_dyadicGrid_eq
    (ω η : IntervalPath) (hω : Continuous ω) (hη : Continuous η)
    (hgrid : ∀ level i, i ≤ 2 ^ level →
      ω (intervalDyadicTime level i) = η (intervalDyadicTime level i)) :
    ω = η := by
  refine Continuous.ext_on denseRange_boundedIntervalDyadicGridPoint hω hη ?_
  rintro _ ⟨p, rfl⟩
  exact hgrid p.1.1 p.1.2 p.2

/-- Equality on all true dyadic grid points extends to equality of anchored continuous interval paths.

This wrapper now contains only subtype bookkeeping; the analytic density statement is isolated in
`intervalPath_eq_of_continuous_of_dyadicGrid_eq`. -/
theorem continuousAnchoredIntervalPath_toIntervalPath_eq_of_dyadicGrid_eq
    (ω η : ContinuousAnchoredIntervalPath)
    (hgrid : ∀ level i, i ≤ 2 ^ level →
      continuousAnchoredIntervalPathToIntervalPath ω (intervalDyadicTime level i)
        = continuousAnchoredIntervalPathToIntervalPath η (intervalDyadicTime level i)) :
    continuousAnchoredIntervalPathToIntervalPath ω
      = continuousAnchoredIntervalPathToIntervalPath η := by
  have hωcont : Continuous (continuousAnchoredIntervalPathToIntervalPath ω) := by
    simpa [continuousAnchoredIntervalPathToIntervalPath] using ω.2.2
  have hηcont : Continuous (continuousAnchoredIntervalPathToIntervalPath η) := by
    simpa [continuousAnchoredIntervalPathToIntervalPath] using η.2.2
  exact intervalPath_eq_of_continuous_of_dyadicGrid_eq
    (continuousAnchoredIntervalPathToIntervalPath ω)
    (continuousAnchoredIntervalPathToIntervalPath η) hωcont hηcont hgrid

/-- Point-separation target reduced to finite-grid recovery plus dyadic-density continuity. -/
theorem continuousAnchoredIntervalPath_toIntervalPath_eq_of_normalizedDyadicIncrements_eq
    (ω η : ContinuousAnchoredIntervalPath)
    (hN : ∀ level : ℕ,
      normalizedContinuousAnchoredIntervalDyadicIncrementMap level ω
        = normalizedContinuousAnchoredIntervalDyadicIncrementMap level η) :
    continuousAnchoredIntervalPathToIntervalPath ω
      = continuousAnchoredIntervalPathToIntervalPath η := by
  exact continuousAnchoredIntervalPath_toIntervalPath_eq_of_dyadicGrid_eq ω η
    (continuousAnchoredIntervalPath_dyadicGrid_eq_of_normalizedDyadicIncrements_eq ω η hN)

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

/-- Normalized dyadic increment maps on the anchored-continuous carrier are measurable. -/
theorem measurable_normalizedContinuousAnchoredIntervalDyadicIncrementMap (level : ℕ) :
    Measurable (normalizedContinuousAnchoredIntervalDyadicIncrementMap level) := by
  change Measurable (fun ω : ContinuousAnchoredIntervalPath =>
    normalizedIntervalDyadicIncrementMap level ω.1)
  exact (measurable_normalizedIntervalDyadicIncrementMap level).comp measurable_subtype_coe

/-- The dyadic-increment sigma-algebra is bounded above by the subtype measurable space. -/
theorem normalizedContinuousAnchoredIntervalDyadicIncrementMap_iSup_comap_le :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedContinuousAnchoredIntervalDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
      ≤ (inferInstance : MeasurableSpace ContinuousAnchoredIntervalPath) := by
  refine iSup_le ?_
  intro level
  exact (measurable_normalizedContinuousAnchoredIntervalDyadicIncrementMap level).comap_le

/-- Reverse generation seam for the canonical anchored continuous interval path space.

This is the corrected replacement for the discarded overstrong theorem that dyadic increments on
`[0,1]` generate all of `RealPath := ℝ → ℝ`.  On the anchored continuous interval carrier, dyadic
increments should generate the Borel/subtype measurable space. -/
theorem continuousAnchoredIntervalPath_measurableSpace_le_iSup_comap_normalizedDyadicIncrementMap :
    (inferInstance : MeasurableSpace ContinuousAnchoredIntervalPath)
      ≤ (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedContinuousAnchoredIntervalDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ))) := by
  sorry

/-- Generation target for the canonical anchored continuous interval path space. -/
theorem normalizedContinuousAnchoredIntervalDyadicIncrementMap_iSup_comap_eq :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedContinuousAnchoredIntervalDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
      = (inferInstance : MeasurableSpace ContinuousAnchoredIntervalPath) := by
  apply le_antisymm
  · exact normalizedContinuousAnchoredIntervalDyadicIncrementMap_iSup_comap_le
  · exact continuousAnchoredIntervalPath_measurableSpace_le_iSup_comap_normalizedDyadicIncrementMap

end ChenGeorgiouPavon2021
