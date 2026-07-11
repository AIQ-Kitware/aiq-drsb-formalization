/-
# Continuum frontier: Cameron--Martin finite densities and quasi-invariance

This module contains the finite-dyadic density/absolute-continuity facts and
the assembly wrappers that consume an explicit path-space quasi-invariance
interface.
-/

import ChenGeorgiouPavon2021.Continuum.Sobolev
import ChenGeorgiouPavon2021.Continuum.KLExhaustion

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Finite-dimensional Cameron--Martin density formula for every dyadic normalized-increment
projection.

This is the finite-grid side of path-space quasi-invariance in its strongest useful form: after
projection to a dyadic normalized-increment vector, the shifted Wiener law is the unshifted projected
law with the finite-dimensional Cameron--Martin density. -/
theorem finiteDyadic_withDensity_standardWienerRealPath_shift_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (_hCM : IsCameronMartinPath h hderiv)
    (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level)
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
      = (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)).withDensity
          (fun x : Fin (2 ^ level) → ℝ =>
            ENNReal.ofReal
              (ForMathlib.MeasureTheory.finiteCmDensity
                (normalizedDyadicIncrementMap level h) x)) := by
  let hWstd : IsStandardWiener W :=
    isStandardWiener_standardWienerRealPathMeasure W hWmeasure
  rw [normalizedDyadicIncrementMap_shifted_wiener_law W hWstd level h]
  rw [normalizedDyadicIncrementMap_wiener_law W hWstd level]
  exact ForMathlib.MeasureTheory.stdGaussian_map_add_eq_withDensity_finiteCmDensity
    (normalizedDyadicIncrementMap level h)

/-- Finite-dimensional Cameron--Martin absolute continuity for every dyadic normalized-increment
projection. -/
theorem finiteDyadic_absCont_standardWienerRealPath_shift_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level)
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
      ≪ Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath) := by
  rw [finiteDyadic_withDensity_standardWienerRealPath_shift_of_isCameronMartinPath
    W hWmeasure h hderiv hCM level]
  exact withDensity_absolutelyContinuous _ _

/-- Sharp remaining density-closure interface behind the current finite-dyadic density theorem.

The ambient `RealPath := ℝ → ℝ` carrier does not contain enough structure to derive this theorem
from `IsCameronMartinPath` alone: negative-time/frozen coordinates and non-dyadic path information
must be controlled by a concrete path-space model.  This lemma therefore assembles the result from an
explicit absolute-continuity hypothesis. -/
theorem cameronMartinDyadicDensity_closes_path_absCont_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (_hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (_hderiv : ℝ → ℝ)
    (_hCM : IsCameronMartinPath h _hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath) := by
  exact hac

/-- Full path-space absolute continuity, assembled from an explicit density-closure/absolute-continuity
interface.

The closure is supplied by the explicit hypothesis `hac`. The finite-dyadic quasi-invariance family
`_hfin` provides source-facing context — it is the finite-dimensional evidence that motivates the
closure — but on the current `RealPath := ℝ → ℝ` carrier it does not by itself derive `hac`, so it is
carried as an unused witness rather than consumed. -/
theorem absCont_of_finiteDyadic_absCont_and_density_closure
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (_hfin : ∀ level : ℕ,
      Measure.map (normalizedDyadicIncrementMap level)
          ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        ≪ Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath))
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath) := by
  exact cameronMartinDyadicDensity_closes_path_absCont_of_isCameronMartinPath
    W hWmeasure h hderiv hCM hac

/-- Cameron--Martin shifts of the transported Wiener law are absolutely continuous, when the
path-space quasi-invariance interface is supplied explicitly.

The lightweight `IsCameronMartinPath` interface controls only
controls dyadic energies and does not by itself constrain all coordinates of `RealPath := ℝ → ℝ`.
The actual closure is supplied by the explicit hypothesis `hac`; the finite-dyadic absolute
continuity below is the source-facing finite-dimensional evidence, not a derivation of `hac`. -/
theorem absCont_standardWienerRealPath_shift_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath) := by
  exact absCont_of_finiteDyadic_absCont_and_density_closure W hWmeasure h hderiv hCM
    (finiteDyadic_absCont_standardWienerRealPath_shift_of_isCameronMartinPath
      W hWmeasure h hderiv hCM)
    hac

end ChenGeorgiouPavon2021
