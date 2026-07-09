/-
# Projective lag collapse for Sinkhorn denominator phases

This file owns the hardest projective-shape asymptotic-regularity seam.  It should be attacked with a
Hilbert-projective contraction, monotone-diameter decay, or equivalent positive-kernel energy argument.
It does not need to prove any scale/total-mass facts.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.Precluster

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- If two finite-vector streams converge to projectively parallel limits, then their coordinate
cross-products converge to zero.

This is the topology/algebra packaging used by the denominator lag proof.  It contains no Sinkhorn
dynamics: the real C2-projective work is to show that the current denominator cluster and the
absolute-predecessor denominator cluster are projectively parallel. -/
theorem finite_projective_cross_tendsto_zero_of_tendsto_pair {ι : Type*} [Fintype ι]
    (x y : ℕ → ι → ℝ) (xLim yLim : ι → ℝ)
    (hx : Filter.Tendsto x Filter.atTop (nhds xLim))
    (hy : Filter.Tendsto y Filter.atTop (nhds yLim))
    (hprojective : ∀ i j, xLim i * yLim j - xLim j * yLim i = 0) :
    Filter.Tendsto
      (fun n => fun ij : ι × ι => x n ij.1 * y n ij.2 - x n ij.2 * y n ij.1)
      Filter.atTop (nhds (0 : ι × ι → ℝ)) := by
  apply finite_function_tendsto_of_coordinate_tendsto
  intro ij
  have hx_left : Filter.Tendsto (fun n => x n ij.1) Filter.atTop (nhds (xLim ij.1)) :=
    ((continuous_apply ij.1).tendsto xLim).comp hx
  have hx_right : Filter.Tendsto (fun n => x n ij.2) Filter.atTop (nhds (xLim ij.2)) :=
    ((continuous_apply ij.2).tendsto xLim).comp hx
  have hy_left : Filter.Tendsto (fun n => y n ij.1) Filter.atTop (nhds (yLim ij.1)) :=
    ((continuous_apply ij.1).tendsto yLim).comp hy
  have hy_right : Filter.Tendsto (fun n => y n ij.2) Filter.atTop (nhds (yLim ij.2)) :=
    ((continuous_apply ij.2).tendsto yLim).comp hy
  have hscalar := (hx_left.mul hy_right).sub (hx_right.mul hy_left)
  have hlim : xLim ij.1 * yLim ij.2 - xLim ij.2 * yLim ij.1 = 0 :=
    hprojective ij.1 ij.2
  simpa [hlim] using hscalar

/-- One-phase denominator lag packaging from a current cluster, an absolute-predecessor cluster,
and projective alignment of the two limits. -/
theorem sinkhorn_phase_projective_lag_zero_of_predecessor_projective_limit {ι : Type*}
    [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ) (ψ ψPred : ι → ℝ)
    (hcurrent : Filter.Tendsto (fun n => u (subseq n)) Filter.atTop (nhds ψ))
    (hpred : Filter.Tendsto (fun n => u ((subseq n).pred)) Filter.atTop (nhds ψPred))
    (hprojective : ∀ i j, ψ i * ψPred j - ψ j * ψPred i = 0) :
    SinkhornPhaseProjectiveLagZeroAlong u subseq := by
  exact finite_projective_cross_tendsto_zero_of_tendsto_pair
    (fun n => u (subseq n)) (fun n => u ((subseq n).pred))
    ψ ψPred hcurrent hpred hprojective

/-- Two-denominator packaging from predecessor-limit projective alignment to the public projective
lag predicate.  The hypotheses are intentionally limit-level, not sequence-level conclusions. -/
theorem sinkhorn_denominator_projective_lag_zero_of_predecessor_projective_limits {ι : Type*}
    [Fintype ι]
    (φ0Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat1 : ι → ℝ)
    (hφ0 : Filter.Tendsto (fun n => φ0Iter (subseq n)) Filter.atTop (nhds ψ0))
    (hφhat1 : Filter.Tendsto (fun n => φhat1Iter (subseq n)) Filter.atTop (nhds ψhat1))
    (hφ0Pred : ∃ ψ0Pred : ι → ℝ,
      Filter.Tendsto (fun n => φ0Iter ((subseq n).pred)) Filter.atTop (nhds ψ0Pred) ∧
      ∀ i j, ψ0 i * ψ0Pred j - ψ0 j * ψ0Pred i = 0)
    (hφhat1Pred : ∃ ψhat1Pred : ι → ℝ,
      Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred)) Filter.atTop (nhds ψhat1Pred) ∧
      ∀ i j, ψhat1 i * ψhat1Pred j - ψhat1 j * ψhat1Pred i = 0) :
    SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq := by
  obtain ⟨ψ0Pred, hφ0Pred_tendsto, hφ0Pred_projective⟩ := hφ0Pred
  obtain ⟨ψhat1Pred, hφhat1Pred_tendsto, hφhat1Pred_projective⟩ := hφhat1Pred
  exact ⟨
    sinkhorn_phase_projective_lag_zero_of_predecessor_projective_limit
      φ0Iter subseq ψ0 ψ0Pred hφ0 hφ0Pred_tendsto hφ0Pred_projective,
    sinkhorn_phase_projective_lag_zero_of_predecessor_projective_limit
      φhat1Iter subseq ψhat1 ψhat1Pred hφhat1 hφhat1Pred_tendsto
      hφhat1Pred_projective⟩


/-- Quotient-form projective alignment for the absolute-predecessor denominator limits.

The predecessor denominators are forced by the mixed normalization equations to have the quotient
limits `p / ψhat0` and `q / ψ1`.  After that elementary quotient-limit passage, the only genuinely
projective content left is to show that those quotient limits are projectively parallel to the
current denominator limits `ψ0` and `ψhat1`. -/
abbrev SinkhornDenominatorQuotientPredecessorProjectiveAlignment {ι : Type*}
    (p q : ι → ℝ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ) : Prop :=
  (∀ i j, ψ0 i * (p j / ψhat0 j) - ψ0 j * (p i / ψhat0 i) = 0) ∧
    (∀ i j, ψhat1 i * (q j / ψ1 j) - ψhat1 j * (q i / ψ1 i) = 0)

/-- The left denominator predecessor subsequence has the quotient limit forced by
`φhat0Iter (k + 1) * φ0Iter k = p`.

This is only quotient-update algebra and finite-product topology; it contains no projective
contraction argument. -/
theorem sinkhorn_phi0_predecessor_tendsto_quotient_from_precluster {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    Filter.Tendsto (fun n => φ0Iter ((subseq n).pred))
      Filter.atTop (nhds (fun i => p i / ψhat0 i)) := by
  apply finite_function_tendsto_of_coordinate_tendsto
  intro i
  have hhat0 :
      Filter.Tendsto (fun n => φhat0Iter (subseq n) i)
        Filter.atTop (nhds (ψhat0 i)) :=
    ((continuous_apply i).tendsto ψhat0).comp hpre.tendsto_φhat0
  have hquot :
      Filter.Tendsto (fun n => p i / φhat0Iter (subseq n) i)
        Filter.atTop (nhds (p i / ψhat0 i)) := by
    have hp_const : Filter.Tendsto (fun _ : ℕ => p i) Filter.atTop (nhds (p i)) :=
      tendsto_const_nhds
    exact hp_const.div hhat0 (ne_of_gt (hpre.positive.2.1 i))
  have hsubseq_pos_event : ∀ᶠ n in Filter.atTop, 0 < subseq n := by
    have hgt0 : ∀ᶠ m : ℕ in Filter.atTop, 0 < m := by
      exact Filter.mem_atTop_sets.mpr ⟨1, fun m hm => hm⟩
    exact hpre.strict_mono.tendsto_atTop.eventually hgt0
  have heq_eventually :
      (fun n => φ0Iter ((subseq n).pred) i) =ᶠ[Filter.atTop]
        (fun n => p i / φhat0Iter (subseq n) i) := by
    filter_upwards [hsubseq_pos_event] with n hsubseq_pos
    have hpred_succ : (subseq n).pred + 1 = subseq n :=
      Nat.succ_pred_eq_of_pos hsubseq_pos
    have hnorm := hiter.normalize_left ((subseq n).pred) i
    rw [hpred_succ] at hnorm
    have hdenom_ne : φhat0Iter (subseq n) i ≠ 0 :=
      ne_of_gt (hiter.φhat0_pos (subseq n) i)
    field_simp [hdenom_ne]
    simpa [mul_comm] using hnorm
  exact hquot.congr' heq_eventually.symm

/-- The right denominator predecessor subsequence has the quotient limit forced by
`φ1Iter (k + 1) * φhat1Iter k = q`.

This is only quotient-update algebra and finite-product topology; it contains no projective
contraction argument. -/
theorem sinkhorn_phihat1_predecessor_tendsto_quotient_from_precluster {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred))
      Filter.atTop (nhds (fun j => q j / ψ1 j)) := by
  apply finite_function_tendsto_of_coordinate_tendsto
  intro j
  have hφ1 :
      Filter.Tendsto (fun n => φ1Iter (subseq n) j)
        Filter.atTop (nhds (ψ1 j)) :=
    ((continuous_apply j).tendsto ψ1).comp hpre.tendsto_φ1
  have hquot :
      Filter.Tendsto (fun n => q j / φ1Iter (subseq n) j)
        Filter.atTop (nhds (q j / ψ1 j)) := by
    have hq_const : Filter.Tendsto (fun _ : ℕ => q j) Filter.atTop (nhds (q j)) :=
      tendsto_const_nhds
    exact hq_const.div hφ1 (ne_of_gt (hpre.positive.2.2.2.1 j))
  have hsubseq_pos_event : ∀ᶠ n in Filter.atTop, 0 < subseq n := by
    have hgt0 : ∀ᶠ m : ℕ in Filter.atTop, 0 < m := by
      exact Filter.mem_atTop_sets.mpr ⟨1, fun m hm => hm⟩
    exact hpre.strict_mono.tendsto_atTop.eventually hgt0
  have heq_eventually :
      (fun n => φhat1Iter ((subseq n).pred) j) =ᶠ[Filter.atTop]
        (fun n => q j / φ1Iter (subseq n) j) := by
    filter_upwards [hsubseq_pos_event] with n hsubseq_pos
    have hpred_succ : (subseq n).pred + 1 = subseq n :=
      Nat.succ_pred_eq_of_pos hsubseq_pos
    have hnorm := hiter.normalize_right ((subseq n).pred) j
    rw [hpred_succ] at hnorm
    have hdenom_ne : φ1Iter (subseq n) j ≠ 0 :=
      ne_of_gt (hiter.φ1_pos (subseq n) j)
    field_simp [hdenom_ne]
    simpa [mul_comm] using hnorm
  exact hquot.congr' heq_eventually.symm

/-- Quotient-limit packaging for the two predecessor denominator phases. -/
theorem sinkhorn_denominator_predecessor_quotient_limits_from_precluster {ι : Type*}
    [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    Filter.Tendsto (fun n => φ0Iter ((subseq n).pred))
        Filter.atTop (nhds (fun i => p i / ψhat0 i)) ∧
      Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred))
        Filter.atTop (nhds (fun j => q j / ψ1 j)) := by
  exact ⟨
    sinkhorn_phi0_predecessor_tendsto_quotient_from_precluster p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre,
    sinkhorn_phihat1_predecessor_tendsto_quotient_from_precluster p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre⟩


/-- Remaining C2-projective dynamical seam, now stated after quotient-limit passage.

The normalization equations identify the absolute-predecessor denominator limits as `p / ψhat0` and
`q / ψ1`; this theorem is exactly the leftover projective dynamics.  It should come from a Hilbert
projective contraction, a monotone projective-diameter argument, or an equivalent positive-kernel
oscillation/energy estimate. -/
theorem sinkhorn_denominator_quotient_predecessor_projective_alignment_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    SinkhornDenominatorQuotientPredecessorProjectiveAlignment p q ψ0 ψhat0 ψ1 ψhat1 := by
  sorry

/-- Package quotient predecessor limits plus the remaining quotient-form projective alignment into
predecessor-limit projective alignment.

Compared with the earlier seam, this theorem proves the elementary quotient-limit part using the
Sinkhorn normalization equations.  The only remaining unproved input is the quotient-form projective
alignment above. -/
theorem sinkhorn_denominator_predecessor_projective_limits_from_gauge_iterates {ι : Type*}
    [Fintype ι]
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
    (∃ ψ0Pred : ι → ℝ,
      Filter.Tendsto (fun n => φ0Iter ((subseq n).pred)) Filter.atTop (nhds ψ0Pred) ∧
      ∀ i j, ψ0 i * ψ0Pred j - ψ0 j * ψ0Pred i = 0) ∧
    (∃ ψhat1Pred : ι → ℝ,
      Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred)) Filter.atTop (nhds ψhat1Pred) ∧
      ∀ i j, ψhat1 i * ψhat1Pred j - ψhat1 j * ψhat1Pred i = 0) := by
  obtain ⟨hφ0Pred, hφhat1Pred⟩ :=
    sinkhorn_denominator_predecessor_quotient_limits_from_precluster p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre
  obtain ⟨hφ0_projective, hφhat1_projective⟩ :=
    sinkhorn_denominator_quotient_predecessor_projective_alignment_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact ⟨
    ⟨fun i => p i / ψhat0 i, hφ0Pred, hφ0_projective⟩,
    ⟨fun j => q j / ψ1 j, hφhat1Pred, hφhat1_projective⟩⟩


/-- Projective/asymptotic-regularity core for the denominator phases.

This is the first genuinely hard Sinkhorn-dynamical seam.  It should be proved using the positive
kernel, the finite box bounds, and the two alternating positive linear maps, for example via
Hilbert-projective contraction, monotone-diameter decay, or an equivalent energy argument.  It only
controls projective shape; scale control is separated below. -/
theorem sinkhorn_denominator_projective_lag_tendsto_zero_from_gauge_iterates {ι : Type*}
    [Fintype ι]
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
    SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq := by
  obtain ⟨hφ0Pred, hφhat1Pred⟩ :=
    sinkhorn_denominator_predecessor_projective_limits_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_denominator_projective_lag_zero_of_predecessor_projective_limits
    φ0Iter φhat1Iter subseq ψ0 ψhat1 hpre.tendsto_φ0 hpre.tendsto_φhat1
    hφ0Pred hφhat1Pred


end ChenGeorgiouPavon2021
