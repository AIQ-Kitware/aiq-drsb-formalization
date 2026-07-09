/-
# Finite Sinkhorn convergence scaffold

This module contains the finite iterative-convergence half of the Sinkhorn target.  Unlike the
finite uniqueness theorem, this is a genuine compactness / cluster-point capstone.  The old single
convergence sorry is split into boundedness, subsequence extraction, limit-passage equations, gauge
inheritance, and the unique-cluster-point convergence principle.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Ratio

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

/-- Explicit subsequence form of bounded finite-dimensional compactness.

This is the true topology/compactness input.  It should be proved from compactness of finite
products of closed intervals in `ι → ℝ`, plus a diagonal extraction that also controls the
successor phases appearing in the Sinkhorn normalization equations. -/
theorem sinkhorn_phase_compatible_subsequence_along_of_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hbounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
      (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B)) :
    ∃ (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
      IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψ1 ψhat1 := by
  sorry

/-- Bounded finite-dimensional sequences admit phase-compatible cluster subsequences.

This target-facing wrapper hides the explicit subsequence only after the compactness theorem has
produced it. -/
theorem sinkhorn_phase_compatible_subsequence_of_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hbounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
      (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B)) :
    ∃ ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨subseq, ψ0, ψhat0, ψ1, ψhat1, halong⟩ :=
    sinkhorn_phase_compatible_subsequence_along_of_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds
  exact ⟨ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_point_of_along
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 halong⟩

/-- Bounded phase-compatible compactness for every outer subsequence.

This is the hard diagonal compactness theorem in the form used by the final convergence argument:
first choose any outer subsequence, then extract a further subsequence whose absolute indices are
`subseq (subsub n)` and whose successor phases also converge. -/
theorem sinkhorn_outer_subsequence_cluster_from_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hbounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
      (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B)) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 := by
  sorry

/-- Every outer subsequence has a further phase-compatible cluster subsequence.

This is the sequential-compactness form needed for the final convergence theorem, not merely for
existence of one cluster point of the original sequence.  The remaining work is now split between
uniform gauge bounds and the pure bounded-subsequence compactness theorem above. -/
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
  have hbounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
      (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B) :=
    sinkhorn_gauge_normalized_uniform_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hp hq hG hiter hgauge
  exact sinkhorn_outer_subsequence_cluster_from_bounds
    φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds

/-- Compactness/subsequence seam for gauge-normalized finite Sinkhorn iterates.

This target-facing theorem is kept as the one-cluster corollary, while the real convergence proof
should use `sinkhorn_gauge_normalized_every_subsequence_has_cluster`. -/
theorem sinkhorn_gauge_normalized_subsequence_exists {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (_hp : ∀ i, 0 < p i) (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∃ ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 := by
  sorry

/-- Forward equation for phase-compatible cluster points. -/
theorem sinkhorn_cluster_point_forward_equation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, ψ0 i = ∑ j, G i j * ψ1 j := by
  sorry

/-- Backward equation for phase-compatible cluster points. -/
theorem sinkhorn_cluster_point_backward_equation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, ψhat1 j = ∑ i, G i j * ψhat0 i := by
  sorry

/-- Left marginal normalization for phase-compatible cluster points. -/
theorem sinkhorn_cluster_point_normalize_left {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, ψ0 i * ψhat0 i = p i := by
  sorry

/-- Right marginal normalization for phase-compatible cluster points. -/
theorem sinkhorn_cluster_point_normalize_right {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, ψ1 j * ψhat1 j = q j := by
  sorry

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

/-- Gauge inheritance for cluster points.

If every iterate has the selected left-total gauge, then every phase-compatible cluster point has the
same gauge.  This is a finite-sum continuity lemma separate from the Sinkhorn equations themselves. -/
theorem sinkhorn_cluster_point_inherits_gauge {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    ∑ i, ψ0 i = ∑ i, φ0 i := by
  sorry

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


/-- If the absolute composed subsequence `subseq (subsub n)` is strictly increasing, then the
inner index selector `subsub` is cofinal.  This is the small order-theoretic bridge needed by the
bad-subsequence compactness argument: a bad outer subsequence remains bad after passing to a
cofinal further subsequence. -/
theorem sinkhorn_subsub_tendsto_atTop_of_strictMono_comp
    (subseq subsub : ℕ → ℕ)
    (_hsubseq : StrictMono subseq)
    (_hcomp : StrictMono (fun n => subseq (subsub n))) :
    Filter.Tendsto subsub Filter.atTop Filter.atTop := by
  sorry

/-- Coordinatewise convergence implies convergence in the finite function space.

This is the product-topology bridge behind the bad-coordinate extraction.  For finite `ι`, a sequence
in `ι → ℝ` converges exactly when all scalar coordinate projections converge. -/
theorem finite_function_tendsto_of_coordinate_tendsto {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (_hcoord : ∀ i : ι, Filter.Tendsto (fun n => x n i) Filter.atTop (nhds (xLim i))) :
    Filter.Tendsto x Filter.atTop (nhds xLim) := by
  sorry

/-- Scalar nonconvergence at `atTop` produces a frequently bad epsilon-neighborhood.

This is the one-dimensional sequential-topology core used by the finite-product bad-coordinate
argument. -/
theorem scalar_not_tendsto_has_frequently_bad_epsilon
    (x : ℕ → ℝ) (xLim : ℝ)
    (_hnot : ¬ Filter.Tendsto x Filter.atTop (nhds xLim)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |x n - xLim| := by
  sorry

/-- If a finite-function sequence does not converge, then some coordinate is frequently
separated from the candidate limit.

This is now a wrapper around two purer topology seams: finite product convergence is coordinatewise,
and scalar nonconvergence produces a frequently bad epsilon-neighborhood. -/
theorem finite_function_not_tendsto_has_frequently_bad_coordinate {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hnot : ¬ Filter.Tendsto x Filter.atTop (nhds xLim)) :
    ∃ i : ι, ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |x n i - xLim i| := by
  by_contra hnone
  have hcoord : ∀ i : ι, Filter.Tendsto (fun n => x n i) Filter.atTop (nhds (xLim i)) := by
    intro i
    by_contra hnot_i
    obtain ⟨ε, hε, hfreq⟩ :=
      scalar_not_tendsto_has_frequently_bad_epsilon (fun n => x n i) (xLim i) hnot_i
    exact hnone ⟨i, ε, hε, hfreq⟩
  exact hnot (finite_function_tendsto_of_coordinate_tendsto x xLim hcoord)

/-- A scalar coordinate that is frequently bad admits a strictly increasing bad subsequence. -/
theorem finite_function_frequently_bad_coordinate_subsequence {ι : Type*}
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ) (i : ι) (ε : ℝ)
    (_hε : 0 < ε)
    (_hfreq : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |x n i - xLim i|) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∀ k : ℕ, ε ≤ |x (subseq k) i - xLim i| := by
  sorry

/-- A bad coordinate subsequence stays nonconvergent after every cofinal further subsequence. -/
theorem finite_function_bad_coordinate_blocks_cofinal_convergence {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ) (i : ι) (ε : ℝ)
    (_hε : 0 < ε) (subseq : ℕ → ℕ)
    (_hbad : ∀ k : ℕ, ε ≤ |x (subseq k) i - xLim i|)
    (subsub : ℕ → ℕ) (_hsubsub : Filter.Tendsto subsub Filter.atTop Filter.atTop) :
    ¬ Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim) := by
  sorry

/-- A nonconvergent finite-function sequence has a bad subsequence that no cofinal further
subsequence can make converge to the candidate limit.

This packages the standard contradiction setup used by the unique-cluster convergence theorem. -/
theorem finite_function_not_tendsto_produces_bad_subsequence {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hnot : ¬ Filter.Tendsto x Filter.atTop (nhds xLim)) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∀ subsub : ℕ → ℕ, Filter.Tendsto subsub Filter.atTop Filter.atTop →
        ¬ Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim) := by
  obtain ⟨i, ε, hε, hfreq⟩ := finite_function_not_tendsto_has_frequently_bad_coordinate x xLim hnot
  obtain ⟨subseq, hsubseq_mono, hbad⟩ :=
    finite_function_frequently_bad_coordinate_subsequence x xLim i ε hε hfreq
  refine ⟨subseq, hsubseq_mono, ?_⟩
  intro subsub hsubsub
  exact finite_function_bad_coordinate_blocks_cofinal_convergence
    x xLim i ε hε subseq hbad subsub hsubsub

/-- Generic finite-function topology seam: if every subsequence has a cofinal further subsequence
converging to the same candidate limit, then the original finite-dimensional sequence converges.

This theorem is now only the final contradiction wrapper.  The genuinely hard topology has been split
into the bad-coordinate extraction, bad-subsequence construction, and cofinal-obstruction lemmas above. -/
theorem finite_function_tendsto_of_unique_subseq_cluster {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hsubseq_cluster : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ subsub : ℕ → ℕ,
        Filter.Tendsto subsub Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim)) :
    Filter.Tendsto x Filter.atTop (nhds xLim) := by
  by_contra hnot
  obtain ⟨subseq, hsubseq_mono, hbad⟩ :=
    finite_function_not_tendsto_produces_bad_subsequence x xLim hnot
  obtain ⟨subsub, hsubsub, hconv⟩ := hsubseq_cluster subseq hsubseq_mono
  exact hbad subsub hsubsub hconv

/-- Unique-along topology wrapper for the forward-left iterate family.

All Sinkhorn-specific content has now been pushed into the production of phase-compatible cluster
subsequences and the proof that every such cluster has the selected `φ0` component. -/
theorem sinkhorn_unique_along_cluster_points_imply_φ0_convergence {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
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
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
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
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
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
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
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
