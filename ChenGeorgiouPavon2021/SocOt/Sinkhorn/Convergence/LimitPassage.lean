/-
# Limit-passage seams for finite Sinkhorn cluster points

This file contains the four equation-specific convergence-to-equation lemmas and the packaging that
turns a phase-compatible cluster point into a finite Sinkhorn potential system.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Forward equation for an explicit phase-compatible cluster subsequence.

This is the real limit-passage seam: combine the iterate forward equation with finite weighted-sum
continuity along the named subsequence.  The target-facing existential wrapper below should remain
just packaging. -/
theorem sinkhorn_cluster_point_along_forward_equation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, ψ0 i = ∑ j, G i j * ψ1 j := by
  sorry

/-- Forward equation for phase-compatible cluster points. -/
theorem sinkhorn_cluster_point_forward_equation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, ψ0 i = ∑ j, G i j * ψ1 j := by
  obtain ⟨subseq, halong⟩ := hcluster.exists_subseq
  exact sinkhorn_cluster_point_along_forward_equation p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 hiter halong

/-- Backward equation for an explicit phase-compatible cluster subsequence. -/
theorem sinkhorn_cluster_point_along_backward_equation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, ψhat1 j = ∑ i, G i j * ψhat0 i := by
  sorry

/-- Backward equation for phase-compatible cluster points. -/
theorem sinkhorn_cluster_point_backward_equation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, ψhat1 j = ∑ i, G i j * ψhat0 i := by
  obtain ⟨subseq, halong⟩ := hcluster.exists_subseq
  exact sinkhorn_cluster_point_along_backward_equation p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 hiter halong

/-- Left marginal normalization for an explicit phase-compatible cluster subsequence. -/
theorem sinkhorn_cluster_point_along_normalize_left {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, ψ0 i * ψhat0 i = p i := by
  sorry

/-- Left marginal normalization for phase-compatible cluster points. -/
theorem sinkhorn_cluster_point_normalize_left {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, ψ0 i * ψhat0 i = p i := by
  obtain ⟨subseq, halong⟩ := hcluster.exists_subseq
  exact sinkhorn_cluster_point_along_normalize_left p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 hiter halong

/-- Right marginal normalization for an explicit phase-compatible cluster subsequence. -/
theorem sinkhorn_cluster_point_along_normalize_right {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, ψ1 j * ψhat1 j = q j := by
  sorry

/-- Right marginal normalization for phase-compatible cluster points. -/
theorem sinkhorn_cluster_point_normalize_right {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, ψ1 j * ψhat1 j = q j := by
  obtain ⟨subseq, halong⟩ := hcluster.exists_subseq
  exact sinkhorn_cluster_point_along_normalize_right p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 hiter halong

/-- Limit-passage seam for the equations satisfied by a phase-compatible cluster point.

The remaining analytic/topological content is now split into the four equation-specific lemmas above:
finite-sum continuity for the forward/backward equations and product continuity for the two mixed
normalization equations. -/
theorem sinkhorn_cluster_point_equations {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hp : ∀ i, 0 < p i) (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    (∀ i, ψ0 i = ∑ j, G i j * ψ1 j) ∧
    (∀ j, ψhat1 j = ∑ i, G i j * ψhat0 i) ∧
    (∀ i, ψ0 i * ψhat0 i = p i) ∧
    (∀ j, ψ1 j * ψhat1 j = q j) := by
  exact ⟨
    sinkhorn_cluster_point_forward_equation p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter ψ0 ψhat0 ψ1 ψhat1 hiter hcluster,
    sinkhorn_cluster_point_backward_equation p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter ψ0 ψhat0 ψ1 ψhat1 hiter hcluster,
    sinkhorn_cluster_point_normalize_left p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter ψ0 ψhat0 ψ1 ψhat1 hiter hcluster,
    sinkhorn_cluster_point_normalize_right p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter ψ0 ψhat0 ψ1 ψhat1 hiter hcluster⟩

/-- Cluster-point fixed-point theorem for finite Sinkhorn iterates.

With phase compatibility and strict positivity recorded in the cluster predicate, the fixed-point
wrapper is now purely packaging: positivity is projected from the cluster datum and the four equations
come from the finite-dimensional limit-passage seams. -/
theorem sinkhorn_cluster_point_is_potential {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨hψ0_pos, hψhat0_pos, hψ1_pos, hψhat1_pos⟩ := hcluster.positive
  obtain ⟨hforward, hbackward, hnormalize_left, hnormalize_right⟩ :=
    sinkhorn_cluster_point_equations p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter ψ0 ψhat0 ψ1 ψhat1
      hp hq hG hiter hcluster
  exact {
    φ0_pos := hψ0_pos
    φhat0_pos := hψhat0_pos
    φ1_pos := hψ1_pos
    φhat1_pos := hψhat1_pos
    forward := hforward
    backward := hbackward
    normalize_left := hnormalize_left
    normalize_right := hnormalize_right
  }


end ChenGeorgiouPavon2021
