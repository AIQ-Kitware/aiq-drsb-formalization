/-
# Ideal theorem targets for the dynamic SOC/Hopf--Cole layer
-/

import ChenGeorgiouPavon2021.SocOt.Dynamic
import ChenGeorgiouPavon2021.EnergyIdentityTargets

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (d : SBData X)

/-- Existence target for a feasible control steering the two prescribed marginals.

The abstract `SBData` record does not contain controllability, support, endpoint, or existence
data.  A concrete CGP instance must supply those hypotheses. -/
theorem feasible_control_exists_of_cgp_hypotheses
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hfeas : ∃ u : Control X, Feasible d u ρ₀ ρ₁) :
    ∃ u : Control X, Feasible d u ρ₀ ρ₁ := by
  sorry

/-- Energy-identity family target supplying the hypothesis of `schrodingerBridge_KL_eq_SOC`. -/
theorem energyIdentity_family_of_finiteEnergyDiffusion
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hfed : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      FiniteEnergyDiffusionModelEdges d u ρ₀) :
    ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
        = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
          + energy u (d.pathLaw u ρ₀) := by
  intro u hu
  exact klReal_pathLaw_eq_initialKL_add_energy_of_finiteEnergyDiffusion d u ρ₀ ρ₁ hu (hfed u hu)

/-- Hopf--Cole verification theorem target: the logarithmic-transform feedback control is optimal.

This is where the Schrödinger PDE system, verification theorem, SDE well-posedness, and endpoint
constraints should enter.  The existing characterization theorem then turns this optimality plus
uniqueness into the pointwise formula `u* = ∇ log φ`. -/
theorem hopfCole_control_isOptimalSOC_of_schrodingerSystem
    (grad : (X → ℝ) → X → X) (lap : (X → ℝ) → X → ℝ)
    (φ φhat : ℝ → X → ℝ) (dens0 dens1 : X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hsys : SchrodingerSystem (d.sigma ^ 2) lap φ φhat dens0 dens1)
    (_hφpos : ∀ t x, 0 < φ t x)
    (_hverify : IsOptimalSOC d (fun t x => grad (fun y => Real.log (φ t y)) x) ρ₀ ρ₁) :
    IsOptimalSOC d (fun t x => grad (fun y => Real.log (φ t y)) x) ρ₀ ρ₁ := by
  sorry

/-- Diffusion-scaled Hopf--Cole verification theorem target for CGP Theorem 5.2. -/
theorem sigmaHopfCole_control_isOptimalSOC_of_schrodingerSystem
    (grad : (X → ℝ) → X → X) (lap : (X → ℝ) → X → ℝ)
    (φ φhat : ℝ → X → ℝ) (dens0 dens1 : X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hsys : SchrodingerSystem (d.sigma ^ 2) lap φ φhat dens0 dens1)
    (_hφpos : ∀ t x, 0 < φ t x)
    (_hverify : IsOptimalSOC d (fun t x => (d.sigma ^ 2) • grad (fun y => Real.log (φ t y)) x) ρ₀ ρ₁) :
    IsOptimalSOC d (fun t x => (d.sigma ^ 2) • grad (fun y => Real.log (φ t y)) x) ρ₀ ρ₁ := by
  sorry

/-- Uniqueness target for the stochastic optimal-control optimizer. -/
theorem soc_optimizer_unique_of_strictConvexEnergy
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_huniq : ∀ u u' : Control X,
      IsOptimalSOC d u ρ₀ ρ₁ → IsOptimalSOC d u' ρ₀ ρ₁ → u = u') :
    ∀ u u' : Control X,
      IsOptimalSOC d u ρ₀ ρ₁ → IsOptimalSOC d u' ρ₀ ρ₁ → u = u' := by
  sorry

/-- HJB verification target: a value-gradient feedback is optimal. -/
theorem valueGradient_control_isOptimalSOC_of_HamiltonJacobi
    (grad : (X → ℝ) → X → X) (lam : ℝ → X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hHJ : HamiltonJacobi grad lam)
    (_hverify : IsOptimalSOC d (fun t x => grad (lam t) x) ρ₀ ρ₁) :
    IsOptimalSOC d (fun t x => grad (lam t) x) ρ₀ ρ₁ := by
  sorry

end ChenGeorgiouPavon2021
