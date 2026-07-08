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
coupling to reconstruct a path law with the same endpoint relative entropy.  The abstract `SBData`
record does not contain this bridge reconstruction theorem, so the statement exposes it as a
concrete gluing edge. -/
theorem dynamic_to_static_gluing_le
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hglue : schrodingerBridgeValueKL d ρ₀ ρ₁ ≤ staticSBValue d ρ₀ ρ₁) :
    schrodingerBridgeValueKL d ρ₀ ρ₁ ≤ staticSBValue d ρ₀ ρ₁ := by
  sorry

/-- Feasible path laws are absolutely continuous with respect to the reference under the
finite-energy SDE/Girsanov edge bundle. -/
theorem feasible_pathLaw_absCont_reference
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hfed : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      FiniteEnergyDiffusionModelEdges d u ρ₀) :
    ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)) := by
  intro u hu
  exact pathLaw_absCont_reference_of_finiteEnergyDiffusion d u ρ₀ (hfed u hu)

/-- Feasible path laws have finite relative entropy under the finite-energy SDE/Girsanov edge
bundle. -/
theorem feasible_pathLaw_klDiv_ne_top
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hfed : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      FiniteEnergyDiffusionModelEdges d u ρ₀) :
    ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤ := by
  intro u hu
  exact pathLaw_klDiv_ne_top_of_finiteEnergyDiffusion d u ρ₀ (hfed u hu)

end ChenGeorgiouPavon2021
