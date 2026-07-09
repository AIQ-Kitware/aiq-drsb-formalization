/-
# Phase-compatible compactness seams for finite Sinkhorn convergence

This file isolates bounded finite-dimensional subsequence extraction.  Follow-on compactness agents
can work here without touching the Sinkhorn limit-passage or uniqueness assembly.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Bounds

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

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

This target-facing theorem is the one-cluster corollary of the uniform-bounds and phase-compatible
subsequence-extraction seams.  The harder every-outer-subsequence form remains available as
`sinkhorn_gauge_normalized_every_subsequence_has_cluster` for the final convergence proof. -/
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
  have hbounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
      (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B) :=
    sinkhorn_gauge_normalized_uniform_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hp hq hG hiter hgauge
  exact sinkhorn_phase_compatible_subsequence_of_bounds
    φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds


end ChenGeorgiouPavon2021
