/-
# Gauge uniqueness and full-convergence assembly for finite Sinkhorn iterates

This file starts after cluster points are known to satisfy the finite Sinkhorn equations.  It contains
gauge inheritance, gauge-fixed uniqueness, and the final unique-cluster convergence wrapper.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.LimitPassage

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Gauge uniqueness seam for cluster points.

Once a cluster point is known to solve the Sinkhorn equations, uniqueness up to common scaling plus
the chosen gauge identifies it with the selected representative. -/
theorem sinkhorn_gauge_fixed_point_unique {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (hgauge : ∑ i, ψ0 i = ∑ i, φ0 i) :
    ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1 := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> exact isEmptyElim i
  · obtain ⟨c, hc, hψ0, hψhat0, hψ1, hψhat1⟩ :=
      sinkhorn_potentials_unique_up_to_scaling p q G
        φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys
    have hsumφ0_pos : 0 < ∑ i, φ0 i := by
      exact Finset.sum_pos (fun i _ => hφsys.φ0_pos i) (by
        rcases hne with ⟨i⟩
        exact ⟨i, Finset.mem_univ i⟩)
    have hsumφ0_ne : (∑ i, φ0 i) ≠ 0 := ne_of_gt hsumφ0_pos
    have hsumψ0 : ∑ i, ψ0 i = c * ∑ i, φ0 i := by
      calc
        ∑ i, ψ0 i = ∑ i, c * φ0 i := by
          exact Finset.sum_congr rfl (fun i _ => hψ0 i)
        _ = c * ∑ i, φ0 i := by rw [Finset.mul_sum]
    have hc_eq_one : c = 1 := by
      apply mul_right_cancel₀ hsumφ0_ne
      calc
        c * (∑ i, φ0 i) = ∑ i, ψ0 i := hsumψ0.symm
        _ = ∑ i, φ0 i := hgauge
        _ = 1 * (∑ i, φ0 i) := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext i
      simpa [hc_eq_one] using hψ0 i
    · funext i
      simpa [hc_eq_one] using hψhat0 i
    · funext j
      simpa [hc_eq_one] using hψ1 j
    · funext j
      simpa [hc_eq_one] using hψhat1 j

/-- Finite-sum continuity for function-valued sequences.

This is the only generic ingredient needed for gauge inheritance: convergence of a finite-vector
sequence implies convergence of the coordinate sum.  It is deliberately local to the convergence
module because Agent C uses it only to pass the fixed gauge through a cluster subsequence. -/
theorem finite_sum_tendsto_of_function_tendsto {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (h : Filter.Tendsto x Filter.atTop (nhds xLim)) :
    Filter.Tendsto (fun n => ∑ i, x n i) Filter.atTop (nhds (∑ i, xLim i)) := by
  have hcont : Continuous (fun y : ι → ℝ => ∑ i, y i) := by
    fun_prop
  change Filter.Tendsto ((fun y : ι → ℝ => ∑ i, y i) ∘ x)
    Filter.atTop (nhds (∑ i, xLim i))
  exact (hcont.tendsto xLim).comp h

/-- Gauge inheritance for an explicit phase-compatible cluster subsequence.

The proof is now just finite-sum continuity plus uniqueness of limits: the gauge identity holds for
each iterate index `subseq n`, while the cluster data says those left-forward vectors converge to
`ψ0`. -/
theorem sinkhorn_cluster_point_along_inherits_gauge {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    ∑ i, ψ0 i = ∑ i, φ0 i := by
  have hsum_cluster :
      Filter.Tendsto (fun n => ∑ i, φ0Iter (subseq n) i)
        Filter.atTop (nhds (∑ i, ψ0 i)) :=
    finite_sum_tendsto_of_function_tendsto
      (fun n => φ0Iter (subseq n)) ψ0 halong.tendsto_φ0
  have hsum_target :
      Filter.Tendsto (fun n => ∑ i, φ0Iter (subseq n) i)
        Filter.atTop (nhds (∑ i, φ0 i)) := by
    have hseq_eq :
        (fun n => ∑ i, φ0Iter (subseq n) i) = (fun _ : ℕ => ∑ i, φ0 i) := by
      funext n
      exact hgauge.left_total (subseq n)
    rw [hseq_eq]
    exact (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => ∑ i, φ0 i) Filter.atTop (nhds (∑ i, φ0 i)))
  exact tendsto_nhds_unique hsum_cluster hsum_target

/-- Gauge inheritance for cluster points.

If every iterate has the selected left-total gauge, then every phase-compatible cluster point has the
same gauge.  This wrapper now only opens the existential cluster subsequence and delegates to the
explicit-along lemma. -/
theorem sinkhorn_cluster_point_inherits_gauge {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∑ i, ψ0 i = ∑ i, φ0 i := by
  obtain ⟨subseq, halong⟩ := hcluster.exists_subseq
  exact sinkhorn_cluster_point_along_inherits_gauge
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
    ψ0 ψhat0 ψ1 ψhat1 subseq hgauge halong

/-- Every cluster point is the selected gauge representative. -/
theorem sinkhorn_gauge_normalized_cluster_point_unique {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hpotentials : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1 := by
  have hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1 :=
    sinkhorn_cluster_point_is_potential p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter ψ0 ψhat0 ψ1 ψhat1
      hp hq hG hiter hcluster
  have hψgauge : ∑ i, ψ0 i = ∑ i, φ0 i :=
    sinkhorn_cluster_point_inherits_gauge
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      ψ0 ψhat0 ψ1 ψhat1 hgauge hcluster
  exact sinkhorn_gauge_fixed_point_unique p q G
    φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hpotentials hψsys hψgauge


/-- Unique-along topology wrapper for the forward-left iterate family.

All Sinkhorn-specific content has now been pushed into the production of phase-compatible cluster
subsequences and the proof that every such cluster has the selected `φ0` component. -/
theorem sinkhorn_unique_along_cluster_points_imply_φ0_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 _φhat0 _φ1 _φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (halong_unique : ∀ subseq ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψ1 ψhat1 →
      ψ0 = φ0) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) := by
  refine finite_function_tendsto_of_unique_subseq_cluster φ0Iter φ0 ?_
  intro subseq hsubseq
  obtain ⟨subsub, ψ0, ψhat0, ψ1, ψhat1, halong⟩ := hsubseq_compact subseq hsubseq
  refine ⟨subsub, ?_, ?_⟩
  · exact sinkhorn_subsub_tendsto_atTop_of_strictMono_comp subseq subsub hsubseq halong.strict_mono
  · have hψ0 : ψ0 = φ0 := halong_unique (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 halong
    simpa [hψ0] using halong.tendsto_φ0

/-- Unique-along topology wrapper for the hatted-left iterate family. -/
theorem sinkhorn_unique_along_cluster_points_imply_φhat0_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_φ0 φhat0 _φ1 _φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (halong_unique : ∀ subseq ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψ1 ψhat1 →
      ψhat0 = φhat0) :
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) := by
  refine finite_function_tendsto_of_unique_subseq_cluster φhat0Iter φhat0 ?_
  intro subseq hsubseq
  obtain ⟨subsub, ψ0, ψhat0, ψ1, ψhat1, halong⟩ := hsubseq_compact subseq hsubseq
  refine ⟨subsub, ?_, ?_⟩
  · exact sinkhorn_subsub_tendsto_atTop_of_strictMono_comp subseq subsub hsubseq halong.strict_mono
  · have hψhat0 : ψhat0 = φhat0 :=
      halong_unique (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 halong
    simpa [hψhat0] using halong.tendsto_φhat0

/-- Unique-along topology wrapper for the forward-right iterate family. -/
theorem sinkhorn_unique_along_cluster_points_imply_φ1_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_φ0 _φhat0 φ1 _φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (halong_unique : ∀ subseq ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψ1 ψhat1 →
      ψ1 = φ1) :
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) := by
  refine finite_function_tendsto_of_unique_subseq_cluster φ1Iter φ1 ?_
  intro subseq hsubseq
  obtain ⟨subsub, ψ0, ψhat0, ψ1, ψhat1, halong⟩ := hsubseq_compact subseq hsubseq
  refine ⟨subsub, ?_, ?_⟩
  · exact sinkhorn_subsub_tendsto_atTop_of_strictMono_comp subseq subsub hsubseq halong.strict_mono
  · have hψ1 : ψ1 = φ1 :=
      halong_unique (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 halong
    simpa [hψ1] using halong.tendsto_φ1

/-- Unique-along topology wrapper for the hatted-right iterate family. -/
theorem sinkhorn_unique_along_cluster_points_imply_φhat1_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_φ0 _φhat0 _φ1 φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (halong_unique : ∀ subseq ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψ1 ψhat1 →
      ψhat1 = φhat1) :
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  refine finite_function_tendsto_of_unique_subseq_cluster φhat1Iter φhat1 ?_
  intro subseq hsubseq
  obtain ⟨subsub, ψ0, ψhat0, ψ1, ψhat1, halong⟩ := hsubseq_compact subseq hsubseq
  refine ⟨subsub, ?_, ?_⟩
  · exact sinkhorn_subsub_tendsto_atTop_of_strictMono_comp subseq subsub hsubseq halong.strict_mono
  · have hψhat1 : ψhat1 = φhat1 :=
      halong_unique (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 halong
    simpa [hψhat1] using halong.tendsto_φhat1

/-- Unique-cluster topology seam for the forward-left iterate family.

This wrapper contains only the bridge from explicit cluster points to the existential cluster
predicate used by the Sinkhorn fixed-point uniqueness theorem. -/
theorem sinkhorn_unique_cluster_points_imply_φ0_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (hcluster_unique : ∀ ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 →
      ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) := by
  refine sinkhorn_unique_along_cluster_points_imply_φ0_convergence
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hsubseq_compact ?_
  intro subseq ψ0 ψhat0 ψ1 ψhat1 halong
  exact (hcluster_unique ψ0 ψhat0 ψ1 ψhat1
    (sinkhorn_cluster_point_of_along
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 halong)).1

/-- Unique-cluster topology seam for the hatted-left iterate family. -/
theorem sinkhorn_unique_cluster_points_imply_φhat0_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (hcluster_unique : ∀ ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 →
      ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1) :
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) := by
  refine sinkhorn_unique_along_cluster_points_imply_φhat0_convergence
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hsubseq_compact ?_
  intro subseq ψ0 ψhat0 ψ1 ψhat1 halong
  exact (hcluster_unique ψ0 ψhat0 ψ1 ψhat1
    (sinkhorn_cluster_point_of_along
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 halong)).2.1

/-- Unique-cluster topology seam for the forward-right iterate family. -/
theorem sinkhorn_unique_cluster_points_imply_φ1_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (hcluster_unique : ∀ ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 →
      ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1) :
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) := by
  refine sinkhorn_unique_along_cluster_points_imply_φ1_convergence
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hsubseq_compact ?_
  intro subseq ψ0 ψhat0 ψ1 ψhat1 halong
  exact (hcluster_unique ψ0 ψhat0 ψ1 ψhat1
    (sinkhorn_cluster_point_of_along
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 halong)).2.2.1

/-- Unique-cluster topology seam for the hatted-right iterate family. -/
theorem sinkhorn_unique_cluster_points_imply_φhat1_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (hcluster_unique : ∀ ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 →
      ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1) :
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  refine sinkhorn_unique_along_cluster_points_imply_φhat1_convergence
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hsubseq_compact ?_
  intro subseq ψ0 ψhat0 ψ1 ψhat1 halong
  exact (hcluster_unique ψ0 ψhat0 ψ1 ψhat1
    (sinkhorn_cluster_point_of_along
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 halong)).2.2.2

/-- Unique cluster points imply full finite-dimensional convergence.

The hard general topology theorem is now reduced to the four family-wise convergence seams above.
Each component can be attacked independently by the same bad-subsequence/cluster-subsequence
argument. -/
theorem sinkhorn_unique_cluster_points_imply_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1)
    (hcluster_unique : ∀ ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 →
      ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) ∧
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) ∧
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) ∧
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  exact ⟨
    sinkhorn_unique_cluster_points_imply_φ0_convergence
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hsubseq_compact hcluster_unique,
    sinkhorn_unique_cluster_points_imply_φhat0_convergence
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hsubseq_compact hcluster_unique,
    sinkhorn_unique_cluster_points_imply_φ1_convergence
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hsubseq_compact hcluster_unique,
    sinkhorn_unique_cluster_points_imply_φhat1_convergence
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hsubseq_compact hcluster_unique⟩

/-- Finite-dimensional convergence seam after gauge normalization.

This is now explicitly a composition of: subsequential compactness for every outer subsequence,
cluster-point equations, gauge inheritance, uniqueness of gauge-fixed fixed points, and the general
unique-cluster-point convergence principle. -/
theorem sinkhorn_gauge_normalized_convergence_core {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hpotentials : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) ∧
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) ∧
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) ∧
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  have hsubseq_compact : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 :=
    sinkhorn_gauge_normalized_every_subsequence_has_cluster p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hp hq hG hiter hgauge
  have hcluster_unique : ∀ ψ0 ψhat0 ψ1 ψhat1,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 →
      ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1 := by
    intro ψ0 ψhat0 ψ1 ψhat1 hcluster
    exact sinkhorn_gauge_normalized_cluster_point_unique p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      ψ0 ψhat0 ψ1 ψhat1 hp hq hG hiter hgauge hpotentials hcluster
  exact sinkhorn_unique_cluster_points_imply_convergence
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
    hsubseq_compact hcluster_unique

/-- Algorithmic convergence target for Fortet-IPF/Sinkhorn iterates.

The old scaffold was overstrong: arbitrary sequences do not converge to arbitrary named potentials,
and even genuine finite Sinkhorn iterates only converge to a selected representative after fixing the
multiplicative gauge.  The repaired target states convergence for positive finite Sinkhorn update
sequences that satisfy an explicit gauge normalization, against positive marginals and a strictly
positive kernel, and toward an actual finite Sinkhorn potential system.  No convergence hypothesis is
assumed. -/
theorem sinkhorn_iterates_converge_to_potentials {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hpotentials : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) ∧
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) ∧
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) ∧
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  exact sinkhorn_gauge_normalized_convergence_core p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
    hp hq hG hiter hgauge hpotentials

end ChenGeorgiouPavon2021
