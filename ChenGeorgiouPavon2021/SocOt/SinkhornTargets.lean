/-
# Ideal theorem targets for finite Sinkhorn uniqueness/convergence
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Uniqueness target for finite Schrödinger/Sinkhorn potentials up to reciprocal scaling. -/
theorem sinkhorn_potentials_unique_up_to_scaling {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hφpos : (∀ i, 0 < φ0 i) ∧ (∀ i, 0 < φhat0 i) ∧
      (∀ j, 0 < φ1 j) ∧ (∀ j, 0 < φhat1 j))
    (_hψpos : (∀ i, 0 < ψ0 i) ∧ (∀ i, 0 < ψhat0 i) ∧
      (∀ j, 0 < ψ1 j) ∧ (∀ j, 0 < ψhat1 j))
    (_hφsys :
      (∀ i, φ0 i = ∑ j, G i j * φ1 j) ∧
      (∀ j, φhat1 j = ∑ i, G i j * φhat0 i) ∧
      (∀ i, φ0 i * φhat0 i = p i) ∧
      (∀ j, φ1 j * φhat1 j = q j))
    (_hψsys :
      (∀ i, ψ0 i = ∑ j, G i j * ψ1 j) ∧
      (∀ j, ψhat1 j = ∑ i, G i j * ψhat0 i) ∧
      (∀ i, ψ0 i * ψhat0 i = p i) ∧
      (∀ j, ψ1 j * ψhat1 j = q j)) :
    ∃ c : ℝ, 0 < c ∧
      (∀ i, ψ0 i = c * φ0 i) ∧
      (∀ i, ψhat0 i = c⁻¹ * φhat0 i) ∧
      (∀ j, ψ1 j = c * φ1 j) ∧
      (∀ j, ψhat1 j = c⁻¹ * φhat1 j) := by
  sorry

/-- Algorithmic convergence target for Fortet-IPF/Sinkhorn iterates.

The concrete iterate definition should eventually replace the abstract sequence parameters here;
this theorem records the intended convergence endpoint without making downstream DRSB statements
carry an algorithmic assumption. -/
theorem sinkhorn_iterates_converge_to_potentials {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) ∧
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) ∧
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) ∧
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  sorry

end ChenGeorgiouPavon2021
