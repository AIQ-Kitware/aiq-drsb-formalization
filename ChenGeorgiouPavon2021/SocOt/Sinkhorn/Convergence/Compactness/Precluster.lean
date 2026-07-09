/-
# Raw bounded finite-dimensional precluster extraction

This file owns the pure compactness/diagonal-subsequence surface.  It deliberately produces six
possibly distinct limits, so agents working here do not need to reason about Sinkhorn dynamics or
successor-limit compatibility.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Pure bounded finite-dimensional extraction for every outer subsequence.

This is the true C2 compactness theorem.  It is pure topology/diagonal extraction: after choosing
any outer subsequence, one can pass to a further subsequence where all six bounded phase streams have
limits.  It deliberately does **not** assert phase compatibility of successor limits. -/
theorem sinkhorn_outer_phase_precluster_subsequence_from_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ),
        IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 := by
  sorry

/-- One-cluster corollary of the outer-subsequence raw compactness theorem. -/
theorem sinkhorn_phase_precluster_subsequence_of_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ),
      IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 := by
  have hid : StrictMono (fun n : ℕ => n) := by
    intro a b hab
    exact hab
  obtain ⟨subseq, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, hpre⟩ :=
    sinkhorn_outer_phase_precluster_subsequence_from_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds (fun n : ℕ => n) hid
  exact ⟨subseq, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, hpre⟩

/-- Convert a raw six-phase precluster into the phase-compatible cluster predicate once the two
successor limits are known to agree with their current-phase limits. -/
theorem sinkhorn_cluster_along_of_precluster_successor_eq {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hψhat0 : ψhat0Succ = ψhat0) (hψ1 : ψ1Succ = ψ1) :
    IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1 := by
  exact {
    strict_mono := hpre.strict_mono
    tendsto_φ0 := hpre.tendsto_φ0
    tendsto_φhat0 := hpre.tendsto_φhat0
    tendsto_φhat0_succ := by
      simpa [hψhat0] using hpre.tendsto_φhat0_succ
    tendsto_φ1 := hpre.tendsto_φ1
    tendsto_φ1_succ := by
      simpa [hψ1] using hpre.tendsto_φ1_succ
    tendsto_φhat1 := hpre.tendsto_φhat1
    positive := ⟨hpre.positive.1, hpre.positive.2.1,
      hpre.positive.2.2.2.1, hpre.positive.2.2.2.2.2⟩ }


end ChenGeorgiouPavon2021
