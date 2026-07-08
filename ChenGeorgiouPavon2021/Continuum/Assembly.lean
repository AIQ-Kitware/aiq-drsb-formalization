/-
# Continuum frontier: final M4 assembly wrappers

This module contains only the final M4 assembly wrappers that consume the
frontier theorem interfaces. It should not host new mathematical proof debt.
-/

import ChenGeorgiouPavon2021.Continuum.Sobolev
import ChenGeorgiouPavon2021.Continuum.KLExhaustion
import ChenGeorgiouPavon2021.Continuum.QuasiInvariance

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- ENNReal M4 theorem for the transported Wiener law, with the two genuine path-space analytic
interfaces supplied explicitly: dyadic KL exhaustion and quasi-invariance/absolute continuity. -/
theorem klDiv_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  exact klDiv_standardWienerRealPath_shift_eq_cameronMartinPathEnergy W hWmeasure
    (hasDyadicKLExhaustion_standardWienerRealPathMeasure W hWmeasure hKL)
    h hderiv hCM
    (absCont_standardWienerRealPath_shift_of_isCameronMartinPath W hWmeasure h hderiv hCM hac)

/-- Real-valued M4 theorem for the transported Wiener law, with the two genuine path-space analytic
interfaces supplied explicitly: dyadic KL exhaustion and quasi-invariance/absolute continuity. -/
theorem klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy W hWmeasure
    (hasDyadicKLExhaustion_standardWienerRealPathMeasure W hWmeasure hKL)
    h hderiv hCM
    (absCont_standardWienerRealPath_shift_of_isCameronMartinPath W hWmeasure h hderiv hCM hac)

/-- Real-valued M4 theorem from ordinary Sobolev/Cameron--Martin path hypotheses, with the two
genuine path-space analytic interfaces supplied explicitly. -/
theorem klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_sobolev
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hSob : IsSobolevCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_isCameronMartinPath
    W hWmeasure hKL h hderiv
    (isCameronMartinPath_of_sobolevCameronMartinPath h hderiv hSob)
    hac

/-- Final CGP-facing M4 edge from a transported standard Wiener law and a Sobolev
Cameron--Martin deterministic shift, with the two path-space analytic interfaces supplied
explicitly. -/
theorem hCM_from_standardWienerRealPath_sobolev_shift
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ) (E : ℝ)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (hSob : IsSobolevCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath))
    (henergy : E = cameronMartinPathEnergy hderiv) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = E := by
  rw [henergy]
  exact klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_sobolev
    W hWmeasure hKL h hderiv hSob hac

end ChenGeorgiouPavon2021
