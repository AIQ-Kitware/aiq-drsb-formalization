/-
# RealPath finite-shift and Cameron--Martin assembly lemmas

This module contains the proved finite-shift projection laws and the remaining
assembly lemmas that consume explicit continuum interfaces. It does not add
new mathematical frontier obligations.
-/

import ChenGeorgiouPavon2021.Continuum.Wiener.RealPathTransport

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- M4.1: dyadic normalized increment maps are measurable. -/
theorem measurable_normalizedDyadicIncrementMap (level : ℕ) :
    Measurable (normalizedDyadicIncrementMap level) := by
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement dyadicMesh dyadicTime
  fun_prop

/-- M4.1: normalized increments commute with deterministic path shifts. -/
theorem normalizedDyadicIncrementMap_add (level : ℕ) (ω h : RealPath) :
    normalizedDyadicIncrementMap level (ω + h)
      = normalizedDyadicIncrementMap level ω + normalizedDyadicIncrementMap level h := by
  funext i
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement
  simp [Pi.add_apply]
  ring

/-- M4.2: standard Wiener measure has standard-normal normalized dyadic
increments.  This is exposed as a theorem wrapper around `IsStandardWiener` so
downstream statements do not inspect the structure field directly. -/
theorem normalizedDyadicIncrementMap_wiener_law (W : ProbabilityMeasure RealPath)
    (hW : IsStandardWiener W) (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  exact hW.normalized_dyadic_law level

/-- M4.2/M4.3: after shifting a Wiener path by a deterministic path `h`, the
normalized dyadic increment law is the finite-dimensional standard Gaussian
shifted by the normalized increment vector of `h`. -/
theorem normalizedDyadicIncrementMap_shifted_wiener_law
    (W : ProbabilityMeasure RealPath) (hW : IsStandardWiener W)
    (level : ℕ) (h : RealPath) :
    Measure.map (normalizedDyadicIncrementMap level)
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
      = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) := by
  let N : RealPath → (Fin (2 ^ level) → ℝ) := normalizedDyadicIncrementMap level
  let v : Fin (2 ^ level) → ℝ := normalizedDyadicIncrementMap level h
  have hN : Measurable N := measurable_normalizedDyadicIncrementMap level
  have hshift : Measurable (fun ω : RealPath => ω + h) := by fun_prop
  have hshiftFin : Measurable (fun x : Fin (2 ^ level) → ℝ => x + v) := by fun_prop
  have hcomp : N ∘ (fun ω : RealPath => ω + h) =
      (fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N := by
    funext ω
    exact normalizedDyadicIncrementMap_add level ω h
  calc
    Measure.map N ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        = (W : Measure RealPath).map (N ∘ (fun ω : RealPath => ω + h)) := by
            rw [Measure.map_map hN hshift]
    _ = (W : Measure RealPath).map ((fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N) := by
            rw [hcomp]
    _ = ((W : Measure RealPath).map N).map (fun x : Fin (2 ^ level) → ℝ => x + v) := by
            rw [Measure.map_map hshiftFin hN]
    _ = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) := by
            change ((W : Measure RealPath).map (normalizedDyadicIncrementMap level)).map
                (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) = _
            rw [normalizedDyadicIncrementMap_wiener_law W hW level]

/-- M4.3: finite dyadic projection of the deterministic Wiener shift has exactly
the finite-dimensional Cameron--Martin cost. -/
theorem klDiv_normalizedDyadicIncrement_shifted_wiener
    (W : ProbabilityMeasure RealPath) (hW : IsStandardWiener W)
    (level : ℕ) (h : RealPath) :
    InformationTheory.klDiv
        (Measure.map (normalizedDyadicIncrementMap level)
          ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
        (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath))
      = ENNReal.ofReal (dyadicPathEnergy level h) := by
  rw [normalizedDyadicIncrementMap_shifted_wiener_law W hW level h,
    normalizedDyadicIncrementMap_wiener_law W hW level]
  simpa [dyadicPathEnergy] using
    (ForMathlib.MeasureTheory.klDiv_stdGaussian_map_add
      (normalizedDyadicIncrementMap level h))

/-- M4.4: dyadic finite-grid Cameron--Martin energies converge to the continuum
energy of a Cameron--Martin path. -/
theorem dyadicPathEnergy_tendsto_cameronMartinPathEnergy
    (h : RealPath) (hderiv : ℝ → ℝ) (hCM : IsCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  exact hCM.dyadic_energy_tendsto

/-- M4.5: dyadic normalized-increment KLs converge to the full path-law KL.
This is the path-level projection/exhaustion analogue of the sequence-model
prefix KL convergence theorem. -/
theorem klDiv_normalizedDyadicIncrement_tendsto_path_kl
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hKL : HasDyadicKLExhaustion W)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedDyadicIncrementMap level)
            ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
          (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath))) := by
  exact hKL.normalized_dyadic_kl_tendsto h hac

/-- M4 final ENNReal form: path-level deterministic Cameron--Martin identity for
standard Wiener measure.  This is the continuum theorem that should eventually
replace the abstract `hCM` edge in `energy_identity`. -/
theorem klDiv_wiener_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  have hkl := klDiv_normalizedDyadicIncrement_tendsto_path_kl W h hKL hac
  have hkl' : Filter.Tendsto (fun level : ℕ => ENNReal.ofReal (dyadicPathEnergy level h))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath))) := by
    simpa [klDiv_normalizedDyadicIncrement_shifted_wiener W hW] using hkl
  have henergy : Filter.Tendsto (fun level : ℕ => ENNReal.ofReal (dyadicPathEnergy level h))
      Filter.atTop (nhds (ENNReal.ofReal (cameronMartinPathEnergy hderiv))) := by
    exact (ENNReal.continuous_ofReal.tendsto (cameronMartinPathEnergy hderiv)).comp
      (dyadicPathEnergy_tendsto_cameronMartinPathEnergy h hderiv hCM)
  exact tendsto_nhds_unique hkl' henergy

/-- M4 final real-valued form: the path-level `klReal` identity used by the CGP
energy-identity edge. -/
theorem klReal_wiener_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  rw [klReal, klDiv_wiener_shift_eq_cameronMartinPathEnergy W h hderiv hW hKL hCM hac]
  exact ENNReal.toReal_ofReal (by
    unfold cameronMartinPathEnergy
    positivity)

/-- M4-to-CGP bridge: if a CGP conditional path-kernel edge is represented as a
standard Wiener law shifted by a Cameron--Martin path, then the abstract `hCM`
term required by `energy_identity` is supplied by the path-level theorem above.
The remaining future work is to instantiate these hypotheses for the actual
SDE/feedback kernels of CGP. -/
theorem hCM_from_wiener_shift_scaffold
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ) (E : ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath))
    (henergy : E = cameronMartinPathEnergy hderiv) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = E := by
  rw [henergy]
  exact klReal_wiener_shift_eq_cameronMartinPathEnergy W h hderiv hW hKL hCM hac


/-- End-to-end M4 Wiener-shift theorem for the transported concrete Wiener measure. -/
theorem klDiv_standardWienerRealPath_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  exact klDiv_wiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardWiener_standardWienerRealPathMeasure W hWmeasure) hKL hCM hac

/-- Real-valued end-to-end M4 Wiener-shift theorem for the transported concrete Wiener measure. -/
theorem klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_wiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardWiener_standardWienerRealPathMeasure W hWmeasure) hKL hCM hac

end ChenGeorgiouPavon2021
