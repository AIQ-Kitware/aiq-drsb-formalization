/-
# Ideal interval Wiener closure targets

This module gathers the theorem targets needed to discharge the final M4/continuum assumptions on
the interval carrier.  The assembly theorems consume explicit interfaces for the remaining
path-space generation and quasi-invariance capstones.
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

This measure lives on the lightweight interval function carrier and bridges the `NNReal → ℝ` Wiener
construction to the interval theorem ladder.  The canonical anchored continuous subtype is the
target carrier for the final path-space results. -/
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
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace IntervalPath))
    (hℱ : ∀ level : ℕ,
      ℱ level = MeasurableSpace.comap (normalizedIntervalDyadicIncrementMap level)
        (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
    (hgen : ⨆ level : ℕ, ℱ level = (inferInstance : MeasurableSpace IntervalPath)) :
    HasIntervalDyadicKLExhaustion W := by
  exact hasIntervalDyadicKLExhaustion_of_dyadicGeneration W ℱ hℱ hgen

/-- Restricting an ambient shifted path is the same as shifting the restricted interval path by
the clamped interval shift. -/
theorem restrictRealPathToInterval_add_extendIntervalPathToRealPath
    (ω : RealPath) (h : IntervalPath) :
    restrictRealPathToInterval (ω + extendIntervalPathToRealPath h)
      = restrictRealPathToInterval ω + h := by
  funext t
  unfold restrictRealPathToInterval extendIntervalPathToRealPath
  have ht : clampUnitInterval (t : ℝ) = t := by
    apply Subtype.ext
    rw [coe_clampUnitInterval]
    rw [min_eq_right t.2.2, max_eq_right t.2.1]
  simp [Pi.add_apply, ht]

/-- Absolute continuity descends from an ambient real-path shift to the restricted interval law.

This is a genuine transport lemma: it does not assume interval quasi-invariance.  It only says that
if a deterministic shift is absolutely continuous before restriction, then its restriction is also
absolutely continuous. -/
theorem intervalShift_absCont_of_realPathShift_absCont
    (μ : Measure RealPath) (h : IntervalPath)
    (hac : Measure.map (fun ω : RealPath => ω + extendIntervalPathToRealPath h) μ ≪ μ) :
    Measure.map (fun ω : IntervalPath => ω + h)
        (Measure.map restrictRealPathToInterval μ)
      ≪ Measure.map restrictRealPathToInterval μ := by
  have hrestrict : Measurable restrictRealPathToInterval := by
    unfold restrictRealPathToInterval
    fun_prop
  have hshiftI : Measurable (fun ω : IntervalPath => ω + h) := by
    fun_prop
  have hshiftR : Measurable (fun ω : RealPath => ω + extendIntervalPathToRealPath h) := by
    fun_prop
  have hcomp : (fun ω : IntervalPath => ω + h) ∘ restrictRealPathToInterval
      = restrictRealPathToInterval ∘
          (fun ω : RealPath => ω + extendIntervalPathToRealPath h) := by
    funext ω
    exact (restrictRealPathToInterval_add_extendIntervalPathToRealPath ω h).symm
  have hacRestrict :
      Measure.map restrictRealPathToInterval
          (Measure.map (fun ω : RealPath => ω + extendIntervalPathToRealPath h) μ)
        ≪ Measure.map restrictRealPathToInterval μ :=
    hac.map hrestrict
  rw [Measure.map_map hshiftI hrestrict]
  rw [Measure.map_map hrestrict hshiftR] at hacRestrict
  rw [hcomp]
  exact hacRestrict

/-- Path-space Cameron--Martin quasi-invariance on the corrected interval carrier, descended from the
corresponding ambient real-path quasi-invariance for the clamped extension. -/
theorem absCont_standardIntervalWienerMeasure_shift_of_analyticIntervalCameronMartinPath
    (W : ProbabilityMeasure IntervalPath)
    (hW : (W : Measure IntervalPath) = standardIntervalWienerMeasure)
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (_hA : IsAnalyticIntervalCameronMartinPath h hderiv)
    (hacReal :
      Measure.map (fun ω : RealPath => ω + extendIntervalPathToRealPath h)
          standardWienerRealPathMeasure
        ≪ standardWienerRealPathMeasure) :
    (W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h) ≪ (W : Measure IntervalPath) := by
  rw [hW, standardIntervalWienerMeasure]
  exact intervalShift_absCont_of_realPathShift_absCont standardWienerRealPathMeasure h hacReal

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

/-- Ideal interval-carrier M4 theorem. The conclusion follows by composing the path-generation and
quasi-invariance target theorems above. -/
theorem klReal_standardIntervalWienerMeasure_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure IntervalPath)
    (hWmeasure : (W : Measure IntervalPath) = standardIntervalWienerMeasure)
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace IntervalPath))
    (hℱ : ∀ level : ℕ,
      ℱ level = MeasurableSpace.comap (normalizedIntervalDyadicIncrementMap level)
        (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
    (hgen : ⨆ level : ℕ, ℱ level = (inferInstance : MeasurableSpace IntervalPath))
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticIntervalCameronMartinPath h hderiv)
    (hacReal :
      Measure.map (fun ω : RealPath => ω + extendIntervalPathToRealPath h)
          standardWienerRealPathMeasure
        ≪ standardWienerRealPathMeasure) :
    klReal ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_intervalWiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardIntervalWiener_standardIntervalWienerMeasure W hWmeasure)
    (hasIntervalDyadicKLExhaustion_standardIntervalWienerMeasure W hWmeasure ℱ hℱ hgen)
    (isIntervalCameronMartinPath_of_analyticIntervalCameronMartinPath h hderiv hA)
    (absCont_standardIntervalWienerMeasure_shift_of_analyticIntervalCameronMartinPath
      W hWmeasure h hderiv hA hacReal)

end ChenGeorgiouPavon2021
