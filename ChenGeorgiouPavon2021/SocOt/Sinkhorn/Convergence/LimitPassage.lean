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
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, ψ0 i = ∑ j, G i j * ψ1 j := by
  intro i
  have hleft :
      Filter.Tendsto (fun n => φ0Iter (subseq n) i)
        Filter.atTop (nhds (ψ0 i)) :=
    ((continuous_apply i).tendsto ψ0).comp halong.tendsto_φ0
  have hright :
      Filter.Tendsto (fun n => ∑ j, G i j * φ1Iter (subseq n) j)
        Filter.atTop (nhds (∑ j, G i j * ψ1 j)) := by
    have hcont : Continuous (fun y : ι → ℝ => ∑ j, G i j * y j) := by
      fun_prop
    change Filter.Tendsto
      ((fun y : ι → ℝ => ∑ j, G i j * y j) ∘ (fun n => φ1Iter (subseq n)))
        Filter.atTop (nhds (∑ j, G i j * ψ1 j))
    exact (hcont.tendsto ψ1).comp halong.tendsto_φ1
  have hleft_as_right :
      Filter.Tendsto (fun n => φ0Iter (subseq n) i)
        Filter.atTop (nhds (∑ j, G i j * ψ1 j)) := by
    have hseq_eq :
        (fun n => φ0Iter (subseq n) i) =
          (fun n => ∑ j, G i j * φ1Iter (subseq n) j) := by
      funext n
      exact hiter.forward (subseq n) i
    rw [hseq_eq]
    exact hright
  exact tendsto_nhds_unique hleft hleft_as_right

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
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, ψhat1 j = ∑ i, G i j * ψhat0 i := by
  intro j
  have hleft :
      Filter.Tendsto (fun n => φhat1Iter (subseq n) j)
        Filter.atTop (nhds (ψhat1 j)) :=
    ((continuous_apply j).tendsto ψhat1).comp halong.tendsto_φhat1
  have hright :
      Filter.Tendsto (fun n => ∑ i, G i j * φhat0Iter (subseq n) i)
        Filter.atTop (nhds (∑ i, G i j * ψhat0 i)) := by
    have hcont : Continuous (fun y : ι → ℝ => ∑ i, G i j * y i) := by
      fun_prop
    change Filter.Tendsto
      ((fun y : ι → ℝ => ∑ i, G i j * y i) ∘ (fun n => φhat0Iter (subseq n)))
        Filter.atTop (nhds (∑ i, G i j * ψhat0 i))
    exact (hcont.tendsto ψhat0).comp halong.tendsto_φhat0
  have hleft_as_right :
      Filter.Tendsto (fun n => φhat1Iter (subseq n) j)
        Filter.atTop (nhds (∑ i, G i j * ψhat0 i)) := by
    have hseq_eq :
        (fun n => φhat1Iter (subseq n) j) =
          (fun n => ∑ i, G i j * φhat0Iter (subseq n) i) := by
      funext n
      exact hiter.backward (subseq n) j
    rw [hseq_eq]
    exact hright
  exact tendsto_nhds_unique hleft hleft_as_right

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
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, ψ0 i * ψhat0 i = p i := by
  intro i
  have hφ0 :
      Filter.Tendsto (fun n => φ0Iter (subseq n) i)
        Filter.atTop (nhds (ψ0 i)) :=
    ((continuous_apply i).tendsto ψ0).comp halong.tendsto_φ0
  have hφhat0_succ :
      Filter.Tendsto (fun n => φhat0Iter (subseq n + 1) i)
        Filter.atTop (nhds (ψhat0 i)) :=
    ((continuous_apply i).tendsto ψhat0).comp halong.tendsto_φhat0_succ
  have hprod_cluster :
      Filter.Tendsto
        (fun n => φ0Iter (subseq n) i * φhat0Iter (subseq n + 1) i)
        Filter.atTop (nhds (ψ0 i * ψhat0 i)) := by
    exact hφ0.mul hφhat0_succ
  have hprod_target :
      Filter.Tendsto
        (fun n => φ0Iter (subseq n) i * φhat0Iter (subseq n + 1) i)
        Filter.atTop (nhds (p i)) := by
    have hseq_eq :
        (fun n => φ0Iter (subseq n) i * φhat0Iter (subseq n + 1) i) =
          (fun _ : ℕ => p i) := by
      funext n
      simpa [mul_comm] using hiter.normalize_left (subseq n) i
    rw [hseq_eq]
    exact (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => p i) Filter.atTop (nhds (p i)))
  exact tendsto_nhds_unique hprod_cluster hprod_target

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
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, ψ1 j * ψhat1 j = q j := by
  intro j
  have hφ1_succ :
      Filter.Tendsto (fun n => φ1Iter (subseq n + 1) j)
        Filter.atTop (nhds (ψ1 j)) :=
    ((continuous_apply j).tendsto ψ1).comp halong.tendsto_φ1_succ
  have hφhat1 :
      Filter.Tendsto (fun n => φhat1Iter (subseq n) j)
        Filter.atTop (nhds (ψhat1 j)) :=
    ((continuous_apply j).tendsto ψhat1).comp halong.tendsto_φhat1
  have hprod_cluster :
      Filter.Tendsto
        (fun n => φ1Iter (subseq n + 1) j * φhat1Iter (subseq n) j)
        Filter.atTop (nhds (ψ1 j * ψhat1 j)) := by
    exact hφ1_succ.mul hφhat1
  have hprod_target :
      Filter.Tendsto
        (fun n => φ1Iter (subseq n + 1) j * φhat1Iter (subseq n) j)
        Filter.atTop (nhds (q j)) := by
    have hseq_eq :
        (fun n => φ1Iter (subseq n + 1) j * φhat1Iter (subseq n) j) =
          (fun _ : ℕ => q j) := by
      funext n
      exact hiter.normalize_right (subseq n) j
    rw [hseq_eq]
    exact (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => q j) Filter.atTop (nhds (q j)))
  exact tendsto_nhds_unique hprod_cluster hprod_target

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
