/-
# Ideal theorem targets for finite Sinkhorn uniqueness/convergence
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Uniqueness wrapper for finite Schrödinger/Sinkhorn potentials up to reciprocal scaling.

The current theorem is parameterized by arbitrary matrix data.  Positivity and irreducibility facts
for the concrete Sinkhorn operator should provide the reciprocal-scaling uniqueness edge. -/
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
      (∀ j, ψ1 j * ψhat1 j = q j))
    (hunique : ∃ c : ℝ, 0 < c ∧
      (∀ i, ψ0 i = c * φ0 i) ∧
      (∀ i, ψhat0 i = c⁻¹ * φhat0 i) ∧
      (∀ j, ψ1 j = c * φ1 j) ∧
      (∀ j, ψhat1 j = c⁻¹ * φhat1 j)) :
    ∃ c : ℝ, 0 < c ∧
      (∀ i, ψ0 i = c * φ0 i) ∧
      (∀ i, ψhat0 i = c⁻¹ * φhat0 i) ∧
      (∀ j, ψ1 j = c * φ1 j) ∧
      (∀ j, ψhat1 j = c⁻¹ * φhat1 j) := by
  sorry

/-- Algorithmic convergence wrapper for Fortet-IPF/Sinkhorn iterates.

Arbitrary sequences need not converge to the named potentials.  The concrete iterate definition and
its contraction/compactness proof should supply `hconv`; this theorem records the exact convergence
payload consumed downstream. -/
theorem sinkhorn_iterates_converge_to_potentials {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hconv :
      Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) ∧
      Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) ∧
      Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) ∧
      Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1)) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) ∧
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) ∧
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) ∧
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  sorry

end ChenGeorgiouPavon2021
