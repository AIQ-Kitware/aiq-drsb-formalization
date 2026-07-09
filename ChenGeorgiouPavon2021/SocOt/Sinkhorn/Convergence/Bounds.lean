/-
# Uniform-bounds front end for finite Sinkhorn convergence

This file contains the explicit-cluster packaging lemma and the gauge-normalized boundedness seam.
The old monolithic boundedness obligation is split into directional estimates that can be proved
independently: the fixed-gauge forward potential box, hatted-left bounds from normalization,
hatted-right bounds from the backward equation, and right-potential bounds from normalization.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Topology

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- A uniform positive finite box for one finite family of Sinkhorn phases. -/
def SinkhornPhaseInUniformBox {ι : Type*} (u : ℕ → ι → ℝ) (ε B : ℝ) : Prop :=
  ∀ n i, ε ≤ u n i ∧ u n i ≤ B

/-- A common uniform positive finite box for all four finite Sinkhorn iterate phases. -/
def SinkhornIteratesInUniformBox {ι : Type*}
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ) (ε B : ℝ) : Prop :=
  SinkhornPhaseInUniformBox φ0Iter ε B ∧
  SinkhornPhaseInUniformBox φhat0Iter ε B ∧
  SinkhornPhaseInUniformBox φ1Iter ε B ∧
  SinkhornPhaseInUniformBox φhat1Iter ε B

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

/-- Fixed-gauge bounds for the forward left potentials.

Mathematical content: positivity of `G` and the forward equations give a uniform projective-diameter
bound on each vector `φ0Iter n`; the gauge `∑ i, φ0Iter n i = ∑ i, φ0 i` then turns that ratio bound
and positivity into a single positive lower and upper bound for all coordinates of `φ0Iter`.

This is the only part of the uniform-bounds argument that uses the gauge in an essential way. -/
theorem sinkhorn_gauge_normalized_left_forward_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (_hp : ∀ i, 0 < p i) (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ0Iter ε B := by
  sorry

/-- Hatted-left bounds from left-forward bounds and the left marginal normalization.

For successor phases this is the algebraic estimate
`φhat0Iter (n + 1) i = p i / φ0Iter n i`; the finitely many initial values
`φhat0Iter 0 i` are absorbed into the final finite box using positivity. -/
theorem sinkhorn_hatted_left_bounds_from_left_forward_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hp : ∀ i, 0 < p i)
    (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hφ0bounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ0Iter ε B) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat0Iter ε B := by
  sorry

/-- Hatted-right bounds from hatted-left bounds and the backward equation.

The backward equation writes each `φhat1Iter n j` as a positive finite weighted sum of the already
bounded hatted-left phase.  Positivity of `G` supplies a positive lower bound, and finiteness supplies
an upper bound. -/
theorem sinkhorn_hatted_right_bounds_from_hatted_left_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hp : ∀ i, 0 < p i)
    (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hφhat0bounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat0Iter ε B) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat1Iter ε B := by
  sorry

/-- Right-forward bounds from hatted-right bounds and the right marginal normalization.

For successor phases this is the algebraic estimate
`φ1Iter (n + 1) j = q j / φhat1Iter n j`; the finitely many initial values `φ1Iter 0 j` are
absorbed into the final finite box using positivity. -/
theorem sinkhorn_right_forward_bounds_from_hatted_right_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hp : ∀ i, 0 < p i)
    (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hφhat1bounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat1Iter ε B) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ1Iter ε B := by
  sorry

/-- Combine four positive finite boxes into one common box.

This is a bookkeeping lemma: take the minimum of the four positive lower bounds and the maximum of
the four positive upper bounds.  Keeping this separate prevents the main Sinkhorn estimate from being
cluttered by lattice arithmetic over `min` and `max`. -/
theorem sinkhorn_common_box_of_phase_boxes {ι : Type*}
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hφ0 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ0Iter ε B)
    (hφhat0 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat0Iter ε B)
    (hφ1 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ1Iter ε B)
    (hφhat1 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat1Iter ε B) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      SinkhornIteratesInUniformBox φ0Iter φhat0Iter φ1Iter φhat1Iter ε B := by
  obtain ⟨ε0, B0, hε0, hB0, hbox0⟩ := hφ0
  obtain ⟨εhat0, Bhat0, hεhat0, hBhat0, hboxhat0⟩ := hφhat0
  obtain ⟨ε1, B1, hε1, hB1, hbox1⟩ := hφ1
  obtain ⟨εhat1, Bhat1, hεhat1, hBhat1, hboxhat1⟩ := hφhat1
  let ε : ℝ := min (min ε0 εhat0) (min ε1 εhat1)
  let B : ℝ := max (max B0 Bhat0) (max B1 Bhat1)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min (lt_min hε0 hεhat0) (lt_min hε1 hεhat1)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le hB0
      (le_trans (le_max_left B0 Bhat0) (le_max_left (max B0 Bhat0) (max B1 Bhat1)))
  have hε_le_ε0 : ε ≤ ε0 := by
    dsimp [ε]
    exact le_trans (min_le_left (min ε0 εhat0) (min ε1 εhat1)) (min_le_left ε0 εhat0)
  have hε_le_εhat0 : ε ≤ εhat0 := by
    dsimp [ε]
    exact le_trans (min_le_left (min ε0 εhat0) (min ε1 εhat1)) (min_le_right ε0 εhat0)
  have hε_le_ε1 : ε ≤ ε1 := by
    dsimp [ε]
    exact le_trans (min_le_right (min ε0 εhat0) (min ε1 εhat1)) (min_le_left ε1 εhat1)
  have hε_le_εhat1 : ε ≤ εhat1 := by
    dsimp [ε]
    exact le_trans (min_le_right (min ε0 εhat0) (min ε1 εhat1)) (min_le_right ε1 εhat1)
  have hB0_le_B : B0 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left B0 Bhat0) (le_max_left (max B0 Bhat0) (max B1 Bhat1))
  have hBhat0_le_B : Bhat0 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right B0 Bhat0) (le_max_left (max B0 Bhat0) (max B1 Bhat1))
  have hB1_le_B : B1 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left B1 Bhat1) (le_max_right (max B0 Bhat0) (max B1 Bhat1))
  have hBhat1_le_B : Bhat1 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right B1 Bhat1) (le_max_right (max B0 Bhat0) (max B1 Bhat1))
  refine ⟨ε, B, hε_pos, hB_pos, ?_⟩
  dsimp [SinkhornIteratesInUniformBox]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    exact ⟨le_trans hε_le_ε0 (hbox0 n i).1, le_trans (hbox0 n i).2 hB0_le_B⟩
  · intro n i
    exact ⟨le_trans hε_le_εhat0 (hboxhat0 n i).1, le_trans (hboxhat0 n i).2 hBhat0_le_B⟩
  · intro n i
    exact ⟨le_trans hε_le_ε1 (hbox1 n i).1, le_trans (hbox1 n i).2 hB1_le_B⟩
  · intro n i
    exact ⟨le_trans hε_le_εhat1 (hboxhat1 n i).1, le_trans (hboxhat1 n i).2 hBhat1_le_B⟩

/-- Uniform upper/lower bounds for gauge-normalized finite Sinkhorn iterates.

This is the first compactness input.  Strict positivity of the data and the gauge give a single
finite box containing all four iterate families.  The proof is factored through four directional
estimates so follow-on agents can attack the estimates independently. -/
theorem sinkhorn_gauge_normalized_uniform_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
      (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B) := by
  have hφ0 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ0Iter ε B :=
    sinkhorn_gauge_normalized_left_forward_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hp hq hG hiter hgauge
  have hφhat0 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat0Iter ε B :=
    sinkhorn_hatted_left_bounds_from_left_forward_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter hp hq hG hiter hφ0
  have hφhat1 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat1Iter ε B :=
    sinkhorn_hatted_right_bounds_from_hatted_left_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter hp hq hG hiter hφhat0
  have hφ1 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ1Iter ε B :=
    sinkhorn_right_forward_bounds_from_hatted_right_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter hp hq hG hiter hφhat1
  obtain ⟨ε, B, hε, hB, hbox⟩ :=
    sinkhorn_common_box_of_phase_boxes φ0Iter φhat0Iter φ1Iter φhat1Iter
      hφ0 hφhat0 hφ1 hφhat1
  exact ⟨ε, B, hε, hB, hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2⟩

end ChenGeorgiouPavon2021
