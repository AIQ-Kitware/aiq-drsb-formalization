/-
# Uniform-bounds front end for finite Sinkhorn convergence

This file contains the explicit-cluster packaging lemma and the gauge-normalized boundedness seam.
It is the intended work surface for proving the finite positive box that feeds compactness.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Topology

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Convert an explicit phase-compatible cluster point into the existential cluster predicate.

The compactness and bad-subsequence arguments naturally produce cluster points along named absolute
subsequences.  The uniqueness theorem, however, is stated against the target-facing existential
cluster predicate.  This bridge isolates that packaging step from the real topology. -/
theorem sinkhorn_cluster_point_of_along {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1 := by
  exact {
    exists_subseq := ⟨subseq, halong⟩
    positive := halong.positive
  }

/-- Uniform upper/lower bounds for gauge-normalized finite Sinkhorn iterates.

This is the first compactness input.  Strict positivity of the data and the gauge should give a
single finite box containing all four iterate families, after accounting for the reciprocal hatted
variables via the marginal equations. -/
theorem sinkhorn_gauge_normalized_uniform_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (_hp : ∀ i, 0 < p i) (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
      (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B) := by
  sorry


end ChenGeorgiouPavon2021
