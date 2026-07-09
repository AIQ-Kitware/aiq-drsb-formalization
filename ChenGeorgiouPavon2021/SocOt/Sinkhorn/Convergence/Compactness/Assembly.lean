/-
# Compactness assembly for finite Sinkhorn iterates

This file keeps the public compactness API.  It assembles raw preclusters, phase drift, successor-limit
compatibility, and gauge-normalized bounds into the cluster subsequence theorems used by `Gauge`.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.QuotientDrift

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Vanishing phase drift identifies the current and successor limits in a raw precluster.

This is a generic topology wrapper: if the successor-minus-current stream tends to zero and both
streams already have named limits, then those limits agree. -/
theorem sinkhorn_precluster_successor_limits_eq_of_phase_drift {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hφhat0_drift :
      Filter.Tendsto
        (fun n => fun i => φhat0Iter (subseq n + 1) i - φhat0Iter (subseq n) i)
        Filter.atTop (nhds 0))
    (hφ1_drift :
      Filter.Tendsto
        (fun n => fun j => φ1Iter (subseq n + 1) j - φ1Iter (subseq n) j)
        Filter.atTop (nhds 0)) :
    ψhat0Succ = ψhat0 ∧ ψ1Succ = ψ1 := by
  have hφhat0_limit : ψhat0Succ - ψhat0 = 0 :=
    tendsto_nhds_unique
      (hpre.tendsto_φhat0_succ.sub hpre.tendsto_φhat0)
      hφhat0_drift
  have hφ1_limit : ψ1Succ - ψ1 = 0 :=
    tendsto_nhds_unique
      (hpre.tendsto_φ1_succ.sub hpre.tendsto_φ1)
      hφ1_drift
  exact ⟨sub_eq_zero.mp hφhat0_limit, sub_eq_zero.mp hφ1_limit⟩

/-- Sinkhorn-specific compatibility seam for raw six-phase preclusters.

The hard content is now isolated as asymptotic regularity of the two phase drifts.  This wrapper only
turns that drift statement into equality of current and successor limits. -/
theorem sinkhorn_precluster_successor_limits_eq_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    ψhat0Succ = ψhat0 ∧ ψ1Succ = ψ1 := by
  obtain ⟨hφhat0_drift, hφ1_drift⟩ :=
    sinkhorn_phase_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_precluster_successor_limits_eq_of_phase_drift
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hpre hφhat0_drift hφ1_drift

/-- Upgrade a raw precluster to a phase-compatible cluster using gauge-normalized Sinkhorn iterate
structure. -/
theorem sinkhorn_cluster_along_of_precluster_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨hψhat0, hψ1⟩ :=
    sinkhorn_precluster_successor_limits_eq_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_cluster_along_of_precluster_successor_eq
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hpre hψhat0 hψ1

/-- Explicit subsequence form of bounded finite-dimensional compactness, upgraded to the
phase-compatible Sinkhorn cluster predicate using gauge-normalized iterate structure. -/
theorem sinkhorn_phase_compatible_subsequence_along_of_gauge_iterates_and_bounds {ι : Type*}
    [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
      IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨subseq, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, hpre⟩ :=
    sinkhorn_phase_precluster_subsequence_of_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds
  exact ⟨subseq, ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_along_of_precluster_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre⟩

/-- Bounded finite-dimensional sequences admit phase-compatible cluster subsequences after using the
gauge-normalized Sinkhorn iterate structure to identify current and successor limits. -/
theorem sinkhorn_phase_compatible_subsequence_of_gauge_iterates_and_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨subseq, ψ0, ψhat0, ψ1, ψhat1, halong⟩ :=
    sinkhorn_phase_compatible_subsequence_along_of_gauge_iterates_and_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hiter hgauge hbounds
  exact ⟨ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_point_of_along
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 halong⟩

/-- Bounded phase-compatible compactness for every outer subsequence, upgraded from a raw precluster
by the Sinkhorn iterate equations. -/
theorem sinkhorn_outer_subsequence_cluster_from_gauge_iterates_and_bounds {ι : Type*}
    [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 := by
  intro subseq hsubseq
  obtain ⟨subsub, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, hpre⟩ :=
    sinkhorn_outer_phase_precluster_subsequence_from_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds subseq hsubseq
  exact ⟨subsub, ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_along_of_precluster_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      (fun n => subseq (subsub n)) ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1
      hiter hgauge hbounds hpre⟩

/-- Every outer subsequence has a further phase-compatible cluster subsequence.

This is the sequential-compactness form needed for the final convergence theorem.  The compactness
part now produces only a raw six-phase precluster; gauge-normalized Sinkhorn iterate structure supplies the separate
successor-limit compatibility seam. -/
theorem sinkhorn_gauge_normalized_every_subsequence_has_cluster {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 := by
  have hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter :=
    sinkhorn_gauge_normalized_uniform_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hp hq hG hiter hgauge
  exact sinkhorn_outer_subsequence_cluster_from_gauge_iterates_and_bounds p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hiter hgauge hbounds

/-- Compactness/subsequence seam for gauge-normalized finite Sinkhorn iterates.

This target-facing theorem is the one-cluster corollary of the uniform-bounds, raw compactness, and
successor-limit compatibility seams. -/
theorem sinkhorn_gauge_normalized_subsequence_exists {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∃ ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 := by
  have hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter :=
    sinkhorn_gauge_normalized_uniform_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hp hq hG hiter hgauge
  exact sinkhorn_phase_compatible_subsequence_of_gauge_iterates_and_bounds p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hiter hgauge hbounds

end ChenGeorgiouPavon2021
