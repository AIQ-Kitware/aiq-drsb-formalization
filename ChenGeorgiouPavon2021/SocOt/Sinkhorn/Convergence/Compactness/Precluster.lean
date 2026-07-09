/-
# Raw bounded finite-dimensional precluster extraction

This file owns the pure compactness/diagonal-subsequence surface.  It deliberately produces six
possibly distinct limits, so agents working here do not need to reason about Sinkhorn dynamics or
successor-limit compatibility.
-/

import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021


/-- Pure finite-dimensional six-stream compactness seam.

Given six uniformly boxed finite-function streams, every outer subsequence has a further absolute
subsequence along which all six streams converge, with strictly positive limiting coordinates.
This is intentionally Sinkhorn-free: the C2-1 target below only instantiates `x₂` and `x₄` with the
absolute-successor streams needed by the raw precluster predicate.

The proof packs the six streams into the compact finite product of closed intervals, extracts a
convergent subsequence there, and projects the resulting limit back to the six phase functions. -/
private theorem finite_six_stream_box_precluster_subsequence {ι : Type*} [Fintype ι]
    (x0 x1 x2 x3 x4 x5 : ℕ → ι → ℝ)
    (_hbox : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ x0 n i ∧ x0 n i ≤ B) ∧
      (∀ n i, ε ≤ x1 n i ∧ x1 n i ≤ B) ∧
      (∀ n i, ε ≤ x2 n i ∧ x2 n i ≤ B) ∧
      (∀ n i, ε ≤ x3 n i ∧ x3 n i ≤ B) ∧
      (∀ n i, ε ≤ x4 n i ∧ x4 n i ≤ B) ∧
      (∀ n i, ε ≤ x5 n i ∧ x5 n i ≤ B)) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψ1 ψ2 ψ3 ψ4 ψ5 : ι → ℝ),
        StrictMono (fun n => subseq (subsub n)) ∧
        Filter.Tendsto (fun n => x0 (subseq (subsub n))) Filter.atTop (nhds ψ0) ∧
        Filter.Tendsto (fun n => x1 (subseq (subsub n))) Filter.atTop (nhds ψ1) ∧
        Filter.Tendsto (fun n => x2 (subseq (subsub n))) Filter.atTop (nhds ψ2) ∧
        Filter.Tendsto (fun n => x3 (subseq (subsub n))) Filter.atTop (nhds ψ3) ∧
        Filter.Tendsto (fun n => x4 (subseq (subsub n))) Filter.atTop (nhds ψ4) ∧
        Filter.Tendsto (fun n => x5 (subseq (subsub n))) Filter.atTop (nhds ψ5) ∧
        (∀ i, 0 < ψ0 i) ∧
        (∀ i, 0 < ψ1 i) ∧
        (∀ i, 0 < ψ2 i) ∧
        (∀ i, 0 < ψ3 i) ∧
        (∀ i, 0 < ψ4 i) ∧
        (∀ i, 0 < ψ5 i) := by
  classical
  rcases _hbox with ⟨ε, B, hε, _hB, h0, h1, h2, h3, h4, h5⟩
  intro subseq hsubseq
  let Cell : Type _ := ι → Set.Icc ε B
  let Box : Type _ := Cell × Cell × Cell × Cell × Cell × Cell
  let packed : ℕ → Box := fun n =>
    ( (fun i => ⟨x0 (subseq n) i, h0 (subseq n) i⟩)
    , (fun i => ⟨x1 (subseq n) i, h1 (subseq n) i⟩)
    , (fun i => ⟨x2 (subseq n) i, h2 (subseq n) i⟩)
    , (fun i => ⟨x3 (subseq n) i, h3 (subseq n) i⟩)
    , (fun i => ⟨x4 (subseq n) i, h4 (subseq n) i⟩)
    , (fun i => ⟨x5 (subseq n) i, h5 (subseq n) i⟩) )
  obtain ⟨z, subsub, hsubsub, hz⟩ := CompactSpace.tendsto_subseq packed
  let ψ0 : ι → ℝ := fun i => (z.1 i : ℝ)
  let ψ1 : ι → ℝ := fun i => (z.2.1 i : ℝ)
  let ψ2 : ι → ℝ := fun i => (z.2.2.1 i : ℝ)
  let ψ3 : ι → ℝ := fun i => (z.2.2.2.1 i : ℝ)
  let ψ4 : ι → ℝ := fun i => (z.2.2.2.2.1 i : ℝ)
  let ψ5 : ι → ℝ := fun i => (z.2.2.2.2.2 i : ℝ)
  have hmono : StrictMono (fun n => subseq (subsub n)) := hsubseq.comp hsubsub
  have ht0 : Filter.Tendsto (fun n => x0 (subseq (subsub n))) Filter.atTop (nhds ψ0) := by
    have hcont : Continuous (fun y : Box => fun i => ((y.1 i : Set.Icc ε B) : ℝ)) := by
      refine continuous_pi ?_
      intro i
      exact continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
    simpa [packed, ψ0, Function.comp_def] using (hcont.tendsto z).comp hz
  have ht1 : Filter.Tendsto (fun n => x1 (subseq (subsub n))) Filter.atTop (nhds ψ1) := by
    have hproj : Continuous (fun y : Box => y.2.1) := by
      exact continuous_fst.comp continuous_snd
    have hcont : Continuous (fun y : Box => fun i => ((y.2.1 i : Set.Icc ε B) : ℝ)) := by
      refine continuous_pi ?_
      intro i
      exact continuous_subtype_val.comp ((continuous_apply i).comp hproj)
    simpa [packed, ψ1, Function.comp_def] using (hcont.tendsto z).comp hz
  have ht2 : Filter.Tendsto (fun n => x2 (subseq (subsub n))) Filter.atTop (nhds ψ2) := by
    have hproj : Continuous (fun y : Box => y.2.2.1) := by
      exact continuous_fst.comp (continuous_snd.comp continuous_snd)
    have hcont : Continuous (fun y : Box => fun i => ((y.2.2.1 i : Set.Icc ε B) : ℝ)) := by
      refine continuous_pi ?_
      intro i
      exact continuous_subtype_val.comp ((continuous_apply i).comp hproj)
    simpa [packed, ψ2, Function.comp_def] using (hcont.tendsto z).comp hz
  have ht3 : Filter.Tendsto (fun n => x3 (subseq (subsub n))) Filter.atTop (nhds ψ3) := by
    have hproj : Continuous (fun y : Box => y.2.2.2.1) := by
      exact continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
    have hcont : Continuous (fun y : Box => fun i => ((y.2.2.2.1 i : Set.Icc ε B) : ℝ)) := by
      refine continuous_pi ?_
      intro i
      exact continuous_subtype_val.comp ((continuous_apply i).comp hproj)
    simpa [packed, ψ3, Function.comp_def] using (hcont.tendsto z).comp hz
  have ht4 : Filter.Tendsto (fun n => x4 (subseq (subsub n))) Filter.atTop (nhds ψ4) := by
    have hproj : Continuous (fun y : Box => y.2.2.2.2.1) := by
      exact continuous_fst.comp
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
    have hcont : Continuous (fun y : Box => fun i => ((y.2.2.2.2.1 i : Set.Icc ε B) : ℝ)) := by
      refine continuous_pi ?_
      intro i
      exact continuous_subtype_val.comp ((continuous_apply i).comp hproj)
    simpa [packed, ψ4, Function.comp_def] using (hcont.tendsto z).comp hz
  have ht5 : Filter.Tendsto (fun n => x5 (subseq (subsub n))) Filter.atTop (nhds ψ5) := by
    have hproj : Continuous (fun y : Box => y.2.2.2.2.2) := by
      exact continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
    have hcont : Continuous (fun y : Box => fun i => ((y.2.2.2.2.2 i : Set.Icc ε B) : ℝ)) := by
      refine continuous_pi ?_
      intro i
      exact continuous_subtype_val.comp ((continuous_apply i).comp hproj)
    simpa [packed, ψ5, Function.comp_def] using (hcont.tendsto z).comp hz
  have hp0 : ∀ i, 0 < ψ0 i := by
    intro i
    exact lt_of_lt_of_le hε (z.1 i).2.1
  have hp1 : ∀ i, 0 < ψ1 i := by
    intro i
    exact lt_of_lt_of_le hε (z.2.1 i).2.1
  have hp2 : ∀ i, 0 < ψ2 i := by
    intro i
    exact lt_of_lt_of_le hε (z.2.2.1 i).2.1
  have hp3 : ∀ i, 0 < ψ3 i := by
    intro i
    exact lt_of_lt_of_le hε (z.2.2.2.1 i).2.1
  have hp4 : ∀ i, 0 < ψ4 i := by
    intro i
    exact lt_of_lt_of_le hε (z.2.2.2.2.1 i).2.1
  have hp5 : ∀ i, 0 < ψ5 i := by
    intro i
    exact lt_of_lt_of_le hε (z.2.2.2.2.2 i).2.1
  exact ⟨subsub, ψ0, ψ1, ψ2, ψ3, ψ4, ψ5,
    hmono, ht0, ht1, ht2, ht3, ht4, ht5, hp0, hp1, hp2, hp3, hp4, hp5⟩

/-- Pure bounded finite-dimensional extraction for every outer subsequence.

This is the true C2 compactness theorem.  It is pure topology/diagonal extraction: after choosing
any outer subsequence, one can pass to a further subsequence where all six bounded phase streams have
limits.  It deliberately does **not** assert phase compatibility of successor limits. -/
theorem sinkhorn_outer_phase_precluster_subsequence_from_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ),
        IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 := by
  rcases hbounds with ⟨ε, B, hε, hB, hφ0, hφhat0, hφ1, hφhat1⟩
  have hbox : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter (n + 1) i ∧ φhat0Iter (n + 1) i ≤ B) ∧
      (∀ n i, ε ≤ φ1Iter n i ∧ φ1Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φ1Iter (n + 1) i ∧ φ1Iter (n + 1) i ≤ B) ∧
      (∀ n i, ε ≤ φhat1Iter n i ∧ φhat1Iter n i ≤ B) := by
    exact ⟨ε, B, hε, hB, hφ0, hφhat0,
      (fun n i => hφhat0 (n + 1) i), hφ1,
      (fun n i => hφ1 (n + 1) i), hφhat1⟩
  intro subseq hsubseq
  obtain ⟨subsub, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1,
      hmono, htφ0, htφhat0, htφhat0Succ, htφ1, htφ1Succ, htφhat1,
      hposφ0, hposφhat0, hposφhat0Succ, hposφ1, hposφ1Succ, hposφhat1⟩ :=
    finite_six_stream_box_precluster_subsequence
      φ0Iter φhat0Iter (fun n i => φhat0Iter (n + 1) i)
      φ1Iter (fun n i => φ1Iter (n + 1) i) φhat1Iter hbox subseq hsubseq
  refine ⟨subsub, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, ?_⟩
  exact {
    strict_mono := hmono
    tendsto_φ0 := htφ0
    tendsto_φhat0 := htφhat0
    tendsto_φhat0_succ := htφhat0Succ
    tendsto_φ1 := htφ1
    tendsto_φ1_succ := htφ1Succ
    tendsto_φhat1 := htφhat1
    positive := ⟨hposφ0, hposφhat0, hposφhat0Succ, hposφ1, hposφ1Succ, hposφhat1⟩ }

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
