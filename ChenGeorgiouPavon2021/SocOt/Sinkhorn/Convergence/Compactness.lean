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

/-- Shared box-bounds hypothesis for the four finite Sinkhorn phase sequences. -/
def SinkhornPhaseBoxBounds {ι : Type*}
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ) : Prop :=
  ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
    (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
    (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
    (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
    (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B)

/-- Tuple-valued finite-dimensional compactness for the six phase streams needed by the update
relations.

This is the true topology/diagonal-extraction input for the one-cluster theorem.  The conclusion is
kept as raw tendsto fields rather than `IsFiniteSinkhornClusterPointAlong` so future compactness work
can focus on extraction without also opening the Sinkhorn cluster-point structure. -/
theorem sinkhorn_phase_limit_tuple_subsequence_of_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
      StrictMono subseq ∧
      Filter.Tendsto (fun n => φ0Iter (subseq n)) Filter.atTop (nhds ψ0) ∧
      Filter.Tendsto (fun n => φhat0Iter (subseq n)) Filter.atTop (nhds ψhat0) ∧
      Filter.Tendsto (fun n => φhat0Iter (subseq n + 1)) Filter.atTop (nhds ψhat0) ∧
      Filter.Tendsto (fun n => φ1Iter (subseq n)) Filter.atTop (nhds ψ1) ∧
      Filter.Tendsto (fun n => φ1Iter (subseq n + 1)) Filter.atTop (nhds ψ1) ∧
      Filter.Tendsto (fun n => φhat1Iter (subseq n)) Filter.atTop (nhds ψhat1) ∧
      ((∀ i, 0 < ψ0 i) ∧
       (∀ i, 0 < ψhat0 i) ∧
       (∀ j, 0 < ψ1 j) ∧
       (∀ j, 0 < ψhat1 j)) := by
  sorry

/-- Package the raw six-phase limit tuple as a phase-compatible Sinkhorn cluster point. -/
theorem sinkhorn_cluster_along_of_phase_limit_tuple {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hmono : StrictMono subseq)
    (hφ0 : Filter.Tendsto (fun n => φ0Iter (subseq n)) Filter.atTop (nhds ψ0))
    (hφhat0 : Filter.Tendsto (fun n => φhat0Iter (subseq n)) Filter.atTop (nhds ψhat0))
    (hφhat0_succ : Filter.Tendsto (fun n => φhat0Iter (subseq n + 1)) Filter.atTop (nhds ψhat0))
    (hφ1 : Filter.Tendsto (fun n => φ1Iter (subseq n)) Filter.atTop (nhds ψ1))
    (hφ1_succ : Filter.Tendsto (fun n => φ1Iter (subseq n + 1)) Filter.atTop (nhds ψ1))
    (hφhat1 : Filter.Tendsto (fun n => φhat1Iter (subseq n)) Filter.atTop (nhds ψhat1))
    (hpos : (∀ i, 0 < ψ0 i) ∧
       (∀ i, 0 < ψhat0 i) ∧
       (∀ j, 0 < ψ1 j) ∧
       (∀ j, 0 < ψhat1 j)) :
    IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1 := by
  exact {
    strict_mono := hmono
    tendsto_φ0 := hφ0
    tendsto_φhat0 := hφhat0
    tendsto_φhat0_succ := hφhat0_succ
    tendsto_φ1 := hφ1
    tendsto_φ1_succ := hφ1_succ
    tendsto_φhat1 := hφhat1
    positive := hpos }

/-- Explicit subsequence form of bounded finite-dimensional compactness.

This target-facing wrapper should stay stable for downstream agents.  Its hard extraction work is
isolated in `sinkhorn_phase_limit_tuple_subsequence_of_bounds`. -/
theorem sinkhorn_phase_compatible_subsequence_along_of_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
      IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨subseq, ψ0, ψhat0, ψ1, ψhat1,
      hmono, hφ0, hφhat0, hφhat0_succ, hφ1, hφ1_succ, hφhat1, hpos⟩ :=
    sinkhorn_phase_limit_tuple_subsequence_of_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds
  exact ⟨subseq, ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_along_of_phase_limit_tuple
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1
      hmono hφ0 hφhat0 hφhat0_succ hφ1 hφ1_succ hφhat1 hpos⟩

/-- Bounded finite-dimensional sequences admit phase-compatible cluster subsequences.

This target-facing wrapper hides the explicit subsequence only after the compactness theorem has
produced it. -/
theorem sinkhorn_phase_compatible_subsequence_of_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨subseq, ψ0, ψhat0, ψ1, ψhat1, halong⟩ :=
    sinkhorn_phase_compatible_subsequence_along_of_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds
  exact ⟨ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_point_of_along
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 halong⟩

/-- Outer-subsequence version of the raw six-phase limit tuple.

The important distinction from simply applying the one-cluster theorem to reindexed streams is the
successor phase: the needed terms are `φhat0Iter (subseq (subsub n) + 1)` and
`φ1Iter (subseq (subsub n) + 1)`, not the next value of the outer subsequence.  This theorem is
therefore the genuine C2 diagonal surface for the final convergence proof. -/
theorem sinkhorn_outer_phase_limit_tuple_subsequence_from_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        StrictMono (fun n => subseq (subsub n)) ∧
        Filter.Tendsto (fun n => φ0Iter (subseq (subsub n))) Filter.atTop (nhds ψ0) ∧
        Filter.Tendsto (fun n => φhat0Iter (subseq (subsub n))) Filter.atTop (nhds ψhat0) ∧
        Filter.Tendsto (fun n => φhat0Iter (subseq (subsub n) + 1)) Filter.atTop (nhds ψhat0) ∧
        Filter.Tendsto (fun n => φ1Iter (subseq (subsub n))) Filter.atTop (nhds ψ1) ∧
        Filter.Tendsto (fun n => φ1Iter (subseq (subsub n) + 1)) Filter.atTop (nhds ψ1) ∧
        Filter.Tendsto (fun n => φhat1Iter (subseq (subsub n))) Filter.atTop (nhds ψhat1) ∧
        ((∀ i, 0 < ψ0 i) ∧
         (∀ i, 0 < ψhat0 i) ∧
         (∀ j, 0 < ψ1 j) ∧
         (∀ j, 0 < ψhat1 j)) := by
  sorry

/-- Bounded phase-compatible compactness for every outer subsequence.

This is the hard diagonal compactness theorem in the form used by the final convergence argument:
first choose any outer subsequence, then extract a further subsequence whose absolute indices are
`subseq (subsub n)` and whose successor phases also converge. -/
theorem sinkhorn_outer_subsequence_cluster_from_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 := by
  intro subseq hsubseq
  obtain ⟨subsub, ψ0, ψhat0, ψ1, ψhat1,
      hmono, hφ0, hφhat0, hφhat0_succ, hφ1, hφ1_succ, hφhat1, hpos⟩ :=
    sinkhorn_outer_phase_limit_tuple_subsequence_from_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds subseq hsubseq
  exact ⟨subsub, ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_along_of_phase_limit_tuple
      φ0Iter φhat0Iter φ1Iter φhat1Iter (fun n => subseq (subsub n))
      ψ0 ψhat0 ψ1 ψhat1 hmono hφ0 hφhat0 hφhat0_succ hφ1 hφ1_succ hφhat1 hpos⟩

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
  have hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter :=
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
  have hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter :=
    sinkhorn_gauge_normalized_uniform_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hp hq hG hiter hgauge
  exact sinkhorn_phase_compatible_subsequence_of_bounds
    φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds

end ChenGeorgiouPavon2021
