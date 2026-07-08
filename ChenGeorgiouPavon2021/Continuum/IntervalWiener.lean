/-
# Ideal interval Wiener closure targets

This module gathers the theorem targets that should discharge the final M4/continuum assumptions on
the corrected interval carrier.  The final assembly theorems in this file are proof-bearing wrappers;
the placeholders are only the missing mathematical capstones.
-/

import ChenGeorgiouPavon2021.Continuum.PathSpace
import ChenGeorgiouPavon2021.Continuum.Sobolev
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

/-- Finite-dimensional interval Wiener law target.

This should be proved by showing that interval normalized dyadic increments commute with restriction
from `RealPath` and then reusing the already-proved transported Wiener finite-increment theorem. -/
theorem isStandardIntervalWiener_standardIntervalWienerMeasure
    (W : ProbabilityMeasure IntervalPath)
    (hW : (W : Measure IntervalPath) = standardIntervalWienerMeasure) :
    IsStandardIntervalWiener W := by
  sorry

/-- KL exhaustion target on the corrected interval carrier.

This is the information-theoretic capstone: finite dyadic projected KLs converge upward to full
path-space KL for Cameron--Martin shifts of the interval Wiener law. -/
theorem hasIntervalDyadicKLExhaustion_standardIntervalWienerMeasure
    (W : ProbabilityMeasure IntervalPath)
    (_hW : (W : Measure IntervalPath) = standardIntervalWienerMeasure) :
    HasIntervalDyadicKLExhaustion W := by
  sorry

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
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticIntervalCameronMartinPath h hderiv) :
    klReal ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_intervalWiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardIntervalWiener_standardIntervalWienerMeasure W hWmeasure)
    (hasIntervalDyadicKLExhaustion_standardIntervalWienerMeasure W hWmeasure)
    (isIntervalCameronMartinPath_of_analyticIntervalCameronMartinPath h hderiv hA)
    (absCont_standardIntervalWienerMeasure_shift_of_analyticIntervalCameronMartinPath
      W hWmeasure h hderiv hA)

end ChenGeorgiouPavon2021
