/-
# Ideal interval Wiener closure targets

This module gathers the theorem targets that should discharge the final M4/continuum assumptions on
the corrected interval carrier.  The final assembly theorems in this file are proof-bearing wrappers;
the placeholders are only the missing mathematical capstones.
-/

import ChenGeorgiouPavon2021.Continuum.PathSpace
import ChenGeorgiouPavon2021.Continuum.Sobolev
import ChenGeorgiouPavon2021.Continuum.KLExhaustion
import ChenGeorgiouPavon2021.Continuum.Wiener.RealPathTransport

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Restrict an ambient real-time path to the closed unit interval. -/
def restrictRealPathToInterval (ω : RealPath) : IntervalPath :=
  fun t : UnitInterval => ω (t : ℝ)

/-- Interval Wiener measure obtained by restricting the transported real-time Wiener law to `[0,1]`.

This is a staging measure on the lightweight interval function carrier.  The canonical final carrier
is expected to be the anchored continuous subtype above; this measure is the current bridge from the
vendored `NNReal → ℝ` Wiener construction into the interval theorem ladder. -/
noncomputable def standardIntervalWienerMeasure : Measure IntervalPath :=
  Measure.map restrictRealPathToInterval standardWienerRealPathMeasure

/-- Restricting an ambient real-time path to `[0,1]` preserves every dyadic normalized-increment
vector. -/
theorem normalizedIntervalDyadicIncrementMap_restrictRealPathToInterval
    (level : ℕ) (ω : RealPath) :
    normalizedIntervalDyadicIncrementMap level (restrictRealPathToInterval ω)
      = normalizedDyadicIncrementMap level ω := by
  funext i
  have hsucc_le : dyadicTime level (i.1 + 1) ≤ 1 := by
    unfold dyadicTime
    have hle_nat : i.1 + 1 ≤ 2 ^ level := Nat.succ_le_of_lt i.2
    rw [div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ level)]
    exact_mod_cast hle_nat
  have hsucc_nonneg : 0 ≤ dyadicTime level (i.1 + 1) := by
    unfold dyadicTime
    positivity
  have hi_le : dyadicTime level i.1 ≤ 1 := by
    unfold dyadicTime
    have hle_nat : i.1 ≤ 2 ^ level := le_of_lt i.2
    rw [div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ level)]
    exact_mod_cast hle_nat
  have hi_nonneg : 0 ≤ dyadicTime level i.1 := by
    unfold dyadicTime
    positivity
  have hsucc : ((intervalDyadicTime level (i.1 + 1) : UnitInterval) : ℝ)
      = dyadicTime level (i.1 + 1) := by
    unfold intervalDyadicTime
    rw [coe_clampUnitInterval, min_eq_right hsucc_le, max_eq_right hsucc_nonneg]
  have hi : ((intervalDyadicTime level i.1 : UnitInterval) : ℝ)
      = dyadicTime level i.1 := by
    unfold intervalDyadicTime
    rw [coe_clampUnitInterval, min_eq_right hi_le, max_eq_right hi_nonneg]
  unfold normalizedIntervalDyadicIncrementMap normalizedIntervalDyadicIncrement intervalDyadicIncrement
    normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement restrictRealPathToInterval
  simp [hsucc, hi]

/-- Finite-dimensional interval Wiener law, obtained by restriction from the already-proved
transported real-time Wiener finite-increment law. -/
theorem isStandardIntervalWiener_standardIntervalWienerMeasure
    (W : ProbabilityMeasure IntervalPath)
    (hW : (W : Measure IntervalPath) = standardIntervalWienerMeasure) :
    IsStandardIntervalWiener W := by
  constructor
  intro level
  rw [hW]
  unfold standardIntervalWienerMeasure standardWienerRealPathMeasure
  have hN : Measurable (normalizedIntervalDyadicIncrementMap level) :=
    measurable_normalizedIntervalDyadicIncrementMap level
  have hrestrict : Measurable restrictRealPathToInterval := by
    unfold restrictRealPathToInterval
    fun_prop
  rw [Measure.map_map hN hrestrict]
  have hcomm : normalizedIntervalDyadicIncrementMap level ∘ restrictRealPathToInterval
      = normalizedDyadicIncrementMap level := by
    funext ω
    exact normalizedIntervalDyadicIncrementMap_restrictRealPathToInterval level ω
  rw [hcomm]
  exact normalizedDyadicIncrementMap_concrete_transport_law wienerToRealPath
    concreteWienerTransport_wienerToRealPath level

/-- KL exhaustion wrapper on the corrected interval carrier.

The missing mathematical work is not specific to the transported interval Wiener law; it is the
filtration theorem saying that normalized dyadic increments generate the chosen interval path
measurable space strongly enough for projected KLs to exhaust the full path-space KL.  Once that
structural generation edge is supplied, this wrapper delegates to the general KL-exhaustion target
`hasIntervalDyadicKLExhaustion_of_dyadicGeneration`. -/
theorem hasIntervalDyadicKLExhaustion_standardIntervalWienerMeasure
    (W : ProbabilityMeasure IntervalPath)
    (_hW : (W : Measure IntervalPath) = standardIntervalWienerMeasure)
    (hgen : HasIntervalDyadicGeneration (inferInstance : MeasurableSpace IntervalPath)) :
    HasIntervalDyadicKLExhaustion W := by
  exact hasIntervalDyadicKLExhaustion_of_dyadicGeneration W hgen

/-- Path-space Cameron--Martin quasi-invariance target on the corrected interval carrier. -/
theorem absCont_standardIntervalWienerMeasure_shift_of_analyticIntervalCameronMartinPath
    (W : ProbabilityMeasure IntervalPath)
    (_hW : (W : Measure IntervalPath) = standardIntervalWienerMeasure)
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (_hA : IsAnalyticIntervalCameronMartinPath h hderiv) :
    (W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h) ≪ (W : Measure IntervalPath) := by
  sorry

/-- Interval-carrier M4 ENNReal theorem from explicit finite-law, KL-exhaustion, dyadic-energy, and
absolute-continuity inputs.  This is assembly only; it should stay complete. -/
theorem klDiv_intervalWiener_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure IntervalPath) (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hW : IsStandardIntervalWiener W) (hKL : HasIntervalDyadicKLExhaustion W)
    (hCM : IsIntervalCameronMartinPath h hderiv)
    (hac : (W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h) ≪
      (W : Measure IntervalPath)) :
    InformationTheory.klDiv
        ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  have hkl := klDiv_normalizedIntervalDyadicIncrement_tendsto_path_kl W h hKL hac
  have hkl' : Filter.Tendsto
      (fun level : ℕ => ENNReal.ofReal (intervalDyadicPathEnergy level h)) Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath))) := by
    simpa [klDiv_normalizedIntervalDyadicIncrement_shifted_wiener W hW] using hkl
  have henergy : Filter.Tendsto
      (fun level : ℕ => ENNReal.ofReal (intervalDyadicPathEnergy level h)) Filter.atTop
      (nhds (ENNReal.ofReal (cameronMartinPathEnergy hderiv))) := by
    exact (ENNReal.continuous_ofReal.tendsto (cameronMartinPathEnergy hderiv)).comp
      (intervalDyadicPathEnergy_tendsto_cameronMartinPathEnergy h hderiv hCM)
  exact tendsto_nhds_unique hkl' henergy

/-- Interval-carrier M4 real-valued theorem from explicit interfaces. -/
theorem klReal_intervalWiener_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure IntervalPath) (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hW : IsStandardIntervalWiener W) (hKL : HasIntervalDyadicKLExhaustion W)
    (hCM : IsIntervalCameronMartinPath h hderiv)
    (hac : (W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h) ≪
      (W : Measure IntervalPath)) :
    klReal ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath)
      = cameronMartinPathEnergy hderiv := by
  rw [klReal, klDiv_intervalWiener_shift_eq_cameronMartinPathEnergy W h hderiv hW hKL hCM hac]
  exact ENNReal.toReal_ofReal (by
    unfold cameronMartinPathEnergy
    positivity)

/-- Ideal interval-carrier M4 theorem: once the target theorems above are proved, this final assembly
contains no remaining mathematical work. -/
theorem klReal_standardIntervalWienerMeasure_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure IntervalPath)
    (hWmeasure : (W : Measure IntervalPath) = standardIntervalWienerMeasure)
    (hgen : HasIntervalDyadicGeneration (inferInstance : MeasurableSpace IntervalPath))
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticIntervalCameronMartinPath h hderiv) :
    klReal ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_intervalWiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardIntervalWiener_standardIntervalWienerMeasure W hWmeasure)
    (hasIntervalDyadicKLExhaustion_standardIntervalWienerMeasure W hWmeasure hgen)
    (isIntervalCameronMartinPath_of_analyticIntervalCameronMartinPath h hderiv hA)
    (absCont_standardIntervalWienerMeasure_shift_of_analyticIntervalCameronMartinPath
      W hWmeasure h hderiv hA)

end ChenGeorgiouPavon2021
