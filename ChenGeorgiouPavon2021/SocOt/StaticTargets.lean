/-
# Ideal theorem targets for dynamic/static Schrödinger bridge gluing
-/

import ChenGeorgiouPavon2021.SocOt.Static
import ChenGeorgiouPavon2021.EnergyIdentityTargets

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (d : SBData X)

/-- Gluing/path-reconstruction target for Léonard's dynamic-to-static Schrödinger bridge theorem.

This is the reverse inequality in `dynamic_eq_static_SB`: glue the reference bridges over a static
coupling to reconstruct a path law with the same endpoint relative entropy. -/
theorem dynamic_to_static_gluing_le
    (ρ₀ ρ₁ : ProbabilityMeasure X) :
    schrodingerBridgeValueKL d ρ₀ ρ₁ ≤ staticSBValue d ρ₀ ρ₁ := by
  sorry

/-- Feasible path laws are absolutely continuous with respect to the reference under the
finite-energy regime. -/
theorem feasible_pathLaw_absCont_reference
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hfed : ∀ u : Control X, Feasible d u ρ₀ ρ₁ → FiniteEnergyDiffusion d u ρ₀) :
    ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)) := by
  sorry

/-- Feasible path laws have finite relative entropy under the finite-energy regime. -/
theorem feasible_pathLaw_klDiv_ne_top
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hfed : ∀ u : Control X, Feasible d u ρ₀ ρ₁ → FiniteEnergyDiffusion d u ρ₀) :
    ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤ := by
  sorry

end ChenGeorgiouPavon2021
