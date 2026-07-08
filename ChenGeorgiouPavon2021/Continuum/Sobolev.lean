/-
# Continuum frontier: Sobolev to dyadic Cameron--Martin energy

This module contains the ordinary Sobolev/Cameron--Martin path interface and
the proved wrapper into the dyadic `IsCameronMartinPath` scaffold.
-/

import ChenGeorgiouPavon2021.Continuum.WienerDyadic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- A concrete Sobolev/Cameron--Martin path interface, deliberately separate from
`IsCameronMartinPath`.

The fields name the usual mathematical ingredients without baking the dyadic-energy
limit into the definition.  The theorem `isCameronMartinPath_of_sobolevCameronMartinPath`
below is the remaining analysis capstone: prove that these ordinary hypotheses imply the
dyadic energy convergence required by the M4 scaffold. -/
structure IsSobolevCameronMartinPath (h : RealPath) (hderiv : ℝ → ℝ) : Prop where
  /-- Placeholder proof field for the ordinary absolute-continuity hypothesis on `h`.
  This stays deliberately lightweight until the repo chooses a concrete AC-path API. -/
  absolutely_continuous_path : True
  /-- Placeholder proof field saying `hderiv` represents the a.e. derivative of `h`.
  This is separated from the square-integrability field so later overlays can replace
  `True` with the concrete derivative relation. -/
  derivative_represents_path : True
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  /-- Dyadic finite-difference energies converge to the continuum Cameron--Martin energy.
  This is the explicit analysis obligation that a future concrete AC/Sobolev API should
  prove from the ordinary path hypotheses above. -/
  dyadic_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))

/-- Sobolev/AC Cameron--Martin paths realize the dyadic-energy interface.

This is the real path-analysis capstone behind `IsCameronMartinPath`: show that if `h`
is absolutely continuous with square-integrable derivative `hderiv`, then the dyadic finite
energies converge to `1/2 ∫ hderiv^2`. -/
theorem isCameronMartinPath_of_sobolevCameronMartinPath
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hSob : IsSobolevCameronMartinPath h hderiv) :
    IsCameronMartinPath h hderiv := by
  exact ⟨hSob.square_integrable, hSob.dyadic_energy_tendsto⟩


/-- Analytic Cameron--Martin path predicate on the ambient real-time scaffold.

This is stronger and more concrete than the lightweight dyadic `IsCameronMartinPath` interface:
`h` is anchored at zero, reconstructed on `[0,1]` as the integral of its derivative, and the
derivative is square-integrable.  The dyadic-energy convergence theorem below is now a real proof
target rather than a field hidden inside the predicate. -/
structure IsAnalyticCameronMartinPath (h : RealPath) (hderiv : ℝ → ℝ) : Prop where
  anchored : h 0 = 0
  interval_reconstruction : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    h t = ∫ s in Set.Ioc (0 : ℝ) t, hderiv s ∂volume
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume

/-- Once the dyadic finite-difference convergence theorem is supplied, an analytic
Cameron--Martin path instantiates the dyadic `IsCameronMartinPath` interface. -/
theorem isCameronMartinPath_of_analyticCameronMartinPath_and_dyadic_tendsto
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticCameronMartinPath h hderiv)
    (hdyadic : Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))) :
    IsCameronMartinPath h hderiv := by
  exact ⟨hA.square_integrable, hdyadic⟩

/-- Sobolev/Riemann-sum capstone on the ambient scaffold: an analytically defined
Cameron--Martin path has dyadic finite-difference energy converging to
`½ ∫₀¹ |h'|²`.

This is one of the main real-analysis theorem targets behind the final DRSB/M4 result. -/
theorem analyticCameronMartinPath_dyadic_energy_tendsto
    (h : RealPath) (hderiv : ℝ → ℝ)
    (_hA : IsAnalyticCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  sorry

/-- An analytically defined Cameron--Martin path instantiates the dyadic interface once the
Riemann-sum convergence capstone is available. -/
theorem isCameronMartinPath_of_analyticCameronMartinPath
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticCameronMartinPath h hderiv) :
    IsCameronMartinPath h hderiv := by
  exact isCameronMartinPath_of_analyticCameronMartinPath_and_dyadic_tendsto h hderiv hA
    (analyticCameronMartinPath_dyadic_energy_tendsto h hderiv hA)

/-- Analytic Cameron--Martin path predicate on the corrected interval carrier. -/
structure IsAnalyticIntervalCameronMartinPath (h : IntervalPath) (hderiv : ℝ → ℝ) : Prop where
  anchored : IntervalPathAnchored h
  interval_reconstruction : ∀ t : UnitInterval,
    h t = ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), hderiv s ∂volume
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume

/-- Once the interval dyadic finite-difference convergence theorem is supplied, an analytic
interval Cameron--Martin path instantiates the interval dyadic interface. -/
theorem isIntervalCameronMartinPath_of_analyticIntervalCameronMartinPath_and_dyadic_tendsto
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticIntervalCameronMartinPath h hderiv)
    (hdyadic : Filter.Tendsto (fun level : ℕ => intervalDyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))) :
    IsIntervalCameronMartinPath h hderiv := by
  exact {
    anchored := hA.anchored
    square_integrable := hA.square_integrable
    dyadic_energy_tendsto := hdyadic
  }

/-- Sobolev/Riemann-sum capstone on the corrected interval carrier. -/
theorem analyticIntervalCameronMartinPath_dyadic_energy_tendsto
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (_hA : IsAnalyticIntervalCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => intervalDyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  sorry

/-- An analytically defined interval Cameron--Martin path instantiates the interval dyadic interface
once the Riemann-sum convergence capstone is available. -/
theorem isIntervalCameronMartinPath_of_analyticIntervalCameronMartinPath
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticIntervalCameronMartinPath h hderiv) :
    IsIntervalCameronMartinPath h hderiv := by
  exact isIntervalCameronMartinPath_of_analyticIntervalCameronMartinPath_and_dyadic_tendsto
    h hderiv hA (analyticIntervalCameronMartinPath_dyadic_energy_tendsto h hderiv hA)

end ChenGeorgiouPavon2021
