/-
# Transport from concrete Wiener paths to the ambient RealPath scaffold

This module contains the nonnegative-time to real-time transport map and the
resulting `IsStandardWiener` wrapper for the transported concrete law.
-/

import ChenGeorgiouPavon2021.Continuum.Wiener.FiniteIncrement

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Extension map from nonnegative-time Wiener paths to the current real-time `RealPath` scaffold.

The extension freezes the negative-time query by evaluating at `max t 0`.  The M4 theorem only uses
nonnegative dyadic times, so the normalized dyadic increments commute with this extension. -/
noncomputable def wienerToRealPath (ω : WienerRealPath) : RealPath :=
  fun t : ℝ => ω ⟨max t 0, by exact le_max_right t 0⟩

/-- Measurability of the nonnegative-time-to-real-time Wiener path extension. -/
theorem measurable_wienerToRealPath : Measurable wienerToRealPath := by
  unfold wienerToRealPath
  fun_prop

/-- Real-time path measure obtained by transporting the vendored concrete Wiener measure. -/
noncomputable def standardWienerRealPathMeasure : Measure RealPath :=
  Measure.map wienerToRealPath standardWienerMeasure

/-- The transported real-time Wiener path measure is a probability measure. -/
instance isProbabilityMeasure_standardWienerRealPathMeasure :
    IsProbabilityMeasure standardWienerRealPathMeasure := by
  unfold standardWienerRealPathMeasure
  exact Measure.isProbabilityMeasure_map measurable_wienerToRealPath.aemeasurable

/-- Normalized dyadic increments commute with the nonnegative-time-to-real-time extension. -/
theorem normalizedDyadicIncrementMap_wienerToRealPath
    (level : ℕ) (ω : WienerRealPath) :
    normalizedDyadicIncrementMap level (wienerToRealPath ω)
      = normalizedWienerDyadicIncrementMap level ω := by
  funext i
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement
    normalizedWienerDyadicIncrementMap normalizedWienerDyadicIncrement wienerDyadicIncrement
    wienerToRealPath
  have hsucc_nn :
      (⟨max (dyadicTime level (i.1 + 1)) 0,
          by exact le_max_right (dyadicTime level (i.1 + 1)) 0⟩ : NNReal)
        = dyadicTimeNNReal level (i.1 + 1) := by
    ext
    change max ((((i.1 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))) (0 : ℝ)
      = (((i.1 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))
    exact max_eq_left (by positivity)
  have hi_nn :
      (⟨max (dyadicTime level i.1) 0,
          by exact le_max_right (dyadicTime level i.1) 0⟩ : NNReal)
        = dyadicTimeNNReal level i.1 := by
    ext
    change max ((((i.1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))) (0 : ℝ)
      = (((i.1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))
    exact max_eq_left (by positivity)
  rw [hsucc_nn, hi_nn]

/-- Concrete-to-abstract transport interface for the real Wiener capstone.

A map `Φ : (NNReal → ℝ) → RealPath` transports the concrete vendored Wiener measure into the
current CGP-facing `RealPath` scaffold if it is measurable, preserves all normalized dyadic
increment maps, and satisfies the path-space KL exhaustion theorem after transport. -/
structure ConcreteWienerTransport (Φ : WienerRealPath → RealPath) : Prop where
  measurable : Measurable Φ
  normalized_dyadic_commutes : ∀ level : ℕ,
    normalizedDyadicIncrementMap level ∘ Φ = normalizedWienerDyadicIncrementMap level

/-- The canonical extension map is the intended concrete-to-abstract Wiener transport. -/
theorem concreteWienerTransport_wienerToRealPath :
    ConcreteWienerTransport wienerToRealPath := by
  refine ⟨measurable_wienerToRealPath, ?_⟩
  intro level
  funext ω
  exact normalizedDyadicIncrementMap_wienerToRealPath level ω

/-- Transporting the concrete Wiener law through a valid concrete-to-abstract map gives the
finite-dimensional normalized-dyadic Gaussian laws required by `IsStandardWiener`. -/
theorem normalizedDyadicIncrementMap_concrete_transport_law
    (Φ : WienerRealPath → RealPath) (hΦ : ConcreteWienerTransport Φ) (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level) (Measure.map Φ standardWienerMeasure)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  have hN : Measurable (normalizedDyadicIncrementMap level) := by
    unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement dyadicMesh dyadicTime
    fun_prop
  have hmap :
      Measure.map (normalizedDyadicIncrementMap level) (Measure.map Φ standardWienerMeasure)
        = Measure.map (normalizedDyadicIncrementMap level ∘ Φ) standardWienerMeasure := by
    simpa using (Measure.map_map (μ := standardWienerMeasure) hN hΦ.measurable)
  rw [hmap, hΦ.normalized_dyadic_commutes level]
  exact normalizedWienerDyadicIncrementMap_standardWiener_law level

/-- Any probability-measure wrapper around the transported concrete Wiener law satisfies the
abstract `IsStandardWiener` interface used by the M4 path-level theorem. -/
theorem isStandardWiener_of_concrete_transport
    (Φ : WienerRealPath → RealPath) (hΦ : ConcreteWienerTransport Φ)
    (W : ProbabilityMeasure RealPath)
    (hW : (W : Measure RealPath) = Measure.map Φ standardWienerMeasure) :
    IsStandardWiener W := by
  constructor
  · intro level
    rw [hW]
    exact normalizedDyadicIncrementMap_concrete_transport_law Φ hΦ level

/-- The canonical transported real-time Wiener law satisfies `IsStandardWiener`, modulo choosing any
`ProbabilityMeasure` wrapper whose underlying measure is `standardWienerRealPathMeasure`. -/
theorem isStandardWiener_standardWienerRealPathMeasure
    (W : ProbabilityMeasure RealPath)
    (hW : (W : Measure RealPath) = standardWienerRealPathMeasure) :
    IsStandardWiener W := by
  unfold standardWienerRealPathMeasure at hW
  exact isStandardWiener_of_concrete_transport wienerToRealPath
    concreteWienerTransport_wienerToRealPath W hW

end ChenGeorgiouPavon2021
