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

omit [NormedSpace ℝ X] in
/-- Gluing/path-reconstruction target for Léonard's dynamic-to-static Schrödinger bridge theorem.

The old scaffold stated the reverse dynamic/static inequality for arbitrary abstract `SBData`.
That is too strong: a generic `pathLaw` field need not realize the reference bridge obtained by
gluing conditional reference paths over an endpoint coupling.  The repaired statement exposes the
actual gluing theorem needed for Léonard's argument: every static coupling can be lifted to a
feasible path law whose relative entropy is no larger than the endpoint relative entropy.

From that non-circular path-reconstruction edge, the inequality is a direct infimum argument. -/
theorem dynamic_to_static_gluing_le
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hstatic_nonempty : ∃ π : ProbabilityMeasure (X × X), π ∈ couplings ρ₀ ρ₁)
    (hglue : ∀ π : ProbabilityMeasure (X × X), π ∈ couplings ρ₀ ρ₁ →
      ∃ u : Control X, Feasible d u ρ₀ ρ₁ ∧
        klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
          ≤ klReal (π : Measure (X × X)) (endpointLaw d)) :
    schrodingerBridgeValueKL d ρ₀ ρ₁ ≤ staticSBValue d ρ₀ ρ₁ := by
  unfold schrodingerBridgeValueKL staticSBValue
  refine le_csInf ?_ ?_
  · obtain ⟨π, hπ⟩ := hstatic_nonempty
    exact ⟨klReal (π : Measure (X × X)) (endpointLaw d), π, hπ, rfl⟩
  · rintro J ⟨π, hπ, rfl⟩
    obtain ⟨u, hu, hle⟩ := hglue π hπ
    have hKL_bdd : BddBelow {J : ℝ | ∃ u : Control X, Feasible d u ρ₀ ρ₁ ∧
        J = klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))} := by
      refine ⟨0, ?_⟩
      rintro _ ⟨u, _hu, rfl⟩
      exact ENNReal.toReal_nonneg
    exact le_trans (csInf_le hKL_bdd ⟨u, hu, rfl⟩) hle

/-- Feasible path laws are absolutely continuous with respect to the reference under the
finite-energy model-data regime. -/
theorem feasible_pathLaw_absCont_reference
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hfed : ∀ u : Control X, Feasible d u ρ₀ ρ₁ → FiniteEnergyDiffusion d u ρ₀)
    (hdata : ∀ u : Control X, (hu : Feasible d u ρ₀ ρ₁) →
      FiniteEnergyDiffusionEnergyIdentityData d u ρ₀) :
    ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)) := by
  intro u hu
  exact pathLaw_absCont_reference_of_finiteEnergyDiffusion d u ρ₀ (hfed u hu) (hdata u hu)

omit [NormedSpace ℝ X] in
/-- Feasible path laws have finite relative entropy under the finite-energy model-data regime. -/
theorem feasible_pathLaw_klDiv_ne_top
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hfed : ∀ u : Control X, Feasible d u ρ₀ ρ₁ → FiniteEnergyDiffusion d u ρ₀)
    (hdata : ∀ u : Control X, (hu : Feasible d u ρ₀ ρ₁) →
      FiniteEnergyDiffusionEnergyIdentityData d u ρ₀) :
    ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤ := by
  intro u hu
  exact pathLaw_klDiv_ne_top_of_finiteEnergyDiffusion d u ρ₀ (hfed u hu) (hdata u hu)

end ChenGeorgiouPavon2021
