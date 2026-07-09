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


/-- Projective alignment of the current and successor mixed phases in a raw precluster.

This is a cleaner Hilbert-contraction target than denominator lag itself.  The denominator
predecessor limits are quotients through the normalization equations, so projective alignment of
`ψhat0Succ` with `ψhat0` and of `ψ1Succ` with `ψ1` is exactly the ratio-collapse input needed to
make those quotient predecessor limits projectively parallel to `ψ0` and `ψhat1`. -/
abbrev SinkhornMixedSuccessorProjectiveAlignment {ι : Type*}
    (ψhat0 ψhat0Succ ψ1 ψ1Succ : ι → ℝ) : Prop :=
  (∀ i j, ψhat0Succ i * ψhat0 j - ψhat0Succ j * ψhat0 i = 0) ∧
    (∀ i j, ψ1Succ i * ψ1 j - ψ1Succ j * ψ1 i = 0)

/-- Left normalization passed to a raw six-stream precluster.

This is the limit form of `φhat0Iter (k + 1) * φ0Iter k = p` along `k = subseq n`.
It uses the successor mixed-phase limit `ψhat0Succ`, so it is valid before successor compatibility
has been proved. -/
theorem projective_lag_precluster_normalize_left_successor {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    ∀ i, ψ0 i * ψhat0Succ i = p i := by
  intro i
  have hφ0 :
      Filter.Tendsto (fun n => φ0Iter (subseq n) i)
        Filter.atTop (nhds (ψ0 i)) :=
    ((continuous_apply i).tendsto ψ0).comp hpre.tendsto_φ0
  have hφhat0_succ :
      Filter.Tendsto (fun n => φhat0Iter (subseq n + 1) i)
        Filter.atTop (nhds (ψhat0Succ i)) :=
    ((continuous_apply i).tendsto ψhat0Succ).comp hpre.tendsto_φhat0_succ
  have hprod_cluster :
      Filter.Tendsto
        (fun n => φ0Iter (subseq n) i * φhat0Iter (subseq n + 1) i)
        Filter.atTop (nhds (ψ0 i * ψhat0Succ i)) := by
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

/-- Right normalization passed to a raw six-stream precluster.

This is the limit form of `φ1Iter (k + 1) * φhat1Iter k = q` along `k = subseq n`.
It is duplicated here under a projective-specific name to avoid an import cycle with `ScaleLag`. -/
theorem projective_lag_precluster_normalize_right_successor {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    ∀ j, ψ1Succ j * ψhat1 j = q j := by
  intro j
  have hφ1_succ :
      Filter.Tendsto (fun n => φ1Iter (subseq n + 1) j)
        Filter.atTop (nhds (ψ1Succ j)) :=
    ((continuous_apply j).tendsto ψ1Succ).comp hpre.tendsto_φ1_succ
  have hφhat1 :
      Filter.Tendsto (fun n => φhat1Iter (subseq n) j)
        Filter.atTop (nhds (ψhat1 j)) :=
    ((continuous_apply j).tendsto ψhat1).comp hpre.tendsto_φhat1
  have hprod_cluster :
      Filter.Tendsto
        (fun n => φ1Iter (subseq n + 1) j * φhat1Iter (subseq n) j)
        Filter.atTop (nhds (ψ1Succ j * ψhat1 j)) := by
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

/-- Quotient-predecessor denominator alignment follows algebraically from successor/current
projective alignment of the mixed phases.

The proof uses only the two mixed normalization equations at the raw-precluster limit.  It does not
use Hilbert contraction directly; that is isolated in
`sinkhorn_mixed_successor_projective_alignment_from_gauge_iterates`. -/
theorem sinkhorn_denominator_quotient_predecessor_projective_alignment_of_mixed_successor_alignment
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hmixed : SinkhornMixedSuccessorProjectiveAlignment ψhat0 ψhat0Succ ψ1 ψ1Succ) :
    SinkhornDenominatorQuotientPredecessorProjectiveAlignment p q ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨hmix_hat0, hmix_φ1⟩ := hmixed
  have hnorm_left := projective_lag_precluster_normalize_left_successor p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre
  have hnorm_right := projective_lag_precluster_normalize_right_successor p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre
  refine ⟨?_, ?_⟩
  · intro i j
    have hi_ne : ψhat0 i ≠ 0 := ne_of_gt (hpre.positive.2.1 i)
    have hj_ne : ψhat0 j ≠ 0 := ne_of_gt (hpre.positive.2.1 j)
    have hcross : ψhat0Succ i * ψhat0 j = ψhat0Succ j * ψhat0 i :=
      sub_eq_zero.mp (hmix_hat0 i j)
    have hratio : ψhat0Succ j / ψhat0 j = ψhat0Succ i / ψhat0 i := by
      field_simp [hi_ne, hj_ne]
      nlinarith [hcross]
    rw [← hnorm_left i, ← hnorm_left j]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      ψ0 i * ((ψ0 j * ψhat0Succ j) * (ψhat0 j)⁻¹) -
          ψ0 j * ((ψ0 i * ψhat0Succ i) * (ψhat0 i)⁻¹)
          = ψ0 i * ψ0 j * (ψhat0Succ j * (ψhat0 j)⁻¹) -
            ψ0 j * ψ0 i * (ψhat0Succ i * (ψhat0 i)⁻¹) := by ring
      _ = ψ0 i * ψ0 j * (ψhat0Succ i * (ψhat0 i)⁻¹) -
            ψ0 j * ψ0 i * (ψhat0Succ i * (ψhat0 i)⁻¹) := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, hratio]
      _ = 0 := by ring
  · intro i j
    have hi_ne : ψ1 i ≠ 0 := ne_of_gt (hpre.positive.2.2.2.1 i)
    have hj_ne : ψ1 j ≠ 0 := ne_of_gt (hpre.positive.2.2.2.1 j)
    have hcross : ψ1Succ i * ψ1 j = ψ1Succ j * ψ1 i :=
      sub_eq_zero.mp (hmix_φ1 i j)
    have hratio : ψ1Succ j / ψ1 j = ψ1Succ i / ψ1 i := by
      field_simp [hi_ne, hj_ne]
      nlinarith [hcross]
    rw [← hnorm_right i, ← hnorm_right j]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      ψhat1 i * ((ψ1Succ j * ψhat1 j) * (ψ1 j)⁻¹) -
          ψhat1 j * ((ψ1Succ i * ψhat1 i) * (ψ1 i)⁻¹)
          = ψhat1 i * ψhat1 j * (ψ1Succ j * (ψ1 j)⁻¹) -
            ψhat1 j * ψhat1 i * (ψ1Succ i * (ψ1 i)⁻¹) := by ring
      _ = ψhat1 i * ψhat1 j * (ψ1Succ i * (ψ1 i)⁻¹) -
            ψhat1 j * ψhat1 i * (ψ1Succ i * (ψ1 i)⁻¹) := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, hratio]
      _ = 0 := by ring

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


/-- Sequence-level mixed-phase projective drift along the selected absolute subsequence.

This is the clean Hilbert-contraction/asymptotic-regularity target before any cluster-limit
packaging: each mixed phase should become projectively parallel to its absolute successor. -/
abbrev SinkhornMixedProjectiveDriftZeroAlong {ι : Type*} [Fintype ι]
    (φhat0Iter φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
      (fun n => fun ij : ι × ι =>
        φhat0Iter (subseq n + 1) ij.1 * φhat0Iter (subseq n) ij.2 -
          φhat0Iter (subseq n + 1) ij.2 * φhat0Iter (subseq n) ij.1)
      Filter.atTop (nhds (0 : ι × ι → ℝ)) ∧
    Filter.Tendsto
      (fun n => fun ij : ι × ι =>
        φ1Iter (subseq n + 1) ij.1 * φ1Iter (subseq n) ij.2 -
          φ1Iter (subseq n + 1) ij.2 * φ1Iter (subseq n) ij.1)
      Filter.atTop (nhds (0 : ι × ι → ℝ))

/-- Pass sequence-level mixed projective drift through a raw precluster.

This is only topology: the same cross-product sequence has limit zero by the drift hypothesis and
has the displayed successor/current cluster-limit cross-product by finite-function convergence, so
uniqueness of limits gives projective alignment of the two mixed cluster limits. -/
theorem sinkhorn_mixed_successor_projective_alignment_of_projective_drift {ι : Type*}
    [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hdrift : SinkhornMixedProjectiveDriftZeroAlong φhat0Iter φ1Iter subseq) :
    SinkhornMixedSuccessorProjectiveAlignment ψhat0 ψhat0Succ ψ1 ψ1Succ := by
  obtain ⟨hhat0_drift, hφ1_drift⟩ := hdrift
  refine ⟨?_, ?_⟩
  · intro i j
    have hsucc_i :
        Filter.Tendsto (fun n => φhat0Iter (subseq n + 1) i)
          Filter.atTop (nhds (ψhat0Succ i)) :=
      ((continuous_apply i).tendsto ψhat0Succ).comp hpre.tendsto_φhat0_succ
    have hcurr_j :
        Filter.Tendsto (fun n => φhat0Iter (subseq n) j)
          Filter.atTop (nhds (ψhat0 j)) :=
      ((continuous_apply j).tendsto ψhat0).comp hpre.tendsto_φhat0
    have hsucc_j :
        Filter.Tendsto (fun n => φhat0Iter (subseq n + 1) j)
          Filter.atTop (nhds (ψhat0Succ j)) :=
      ((continuous_apply j).tendsto ψhat0Succ).comp hpre.tendsto_φhat0_succ
    have hcurr_i :
        Filter.Tendsto (fun n => φhat0Iter (subseq n) i)
          Filter.atTop (nhds (ψhat0 i)) :=
      ((continuous_apply i).tendsto ψhat0).comp hpre.tendsto_φhat0
    have hcluster :
        Filter.Tendsto
          (fun n => φhat0Iter (subseq n + 1) i * φhat0Iter (subseq n) j -
            φhat0Iter (subseq n + 1) j * φhat0Iter (subseq n) i)
          Filter.atTop (nhds (ψhat0Succ i * ψhat0 j - ψhat0Succ j * ψhat0 i)) :=
      (hsucc_i.mul hcurr_j).sub (hsucc_j.mul hcurr_i)
    have hzero :
        Filter.Tendsto
          (fun n => φhat0Iter (subseq n + 1) i * φhat0Iter (subseq n) j -
            φhat0Iter (subseq n + 1) j * φhat0Iter (subseq n) i)
          Filter.atTop (nhds (0 : ℝ)) := by
      have hcoord := (tendsto_pi_nhds.mp hhat0_drift) (i, j)
      simpa using hcoord
    exact tendsto_nhds_unique hcluster hzero
  · intro i j
    have hsucc_i :
        Filter.Tendsto (fun n => φ1Iter (subseq n + 1) i)
          Filter.atTop (nhds (ψ1Succ i)) :=
      ((continuous_apply i).tendsto ψ1Succ).comp hpre.tendsto_φ1_succ
    have hcurr_j :
        Filter.Tendsto (fun n => φ1Iter (subseq n) j)
          Filter.atTop (nhds (ψ1 j)) :=
      ((continuous_apply j).tendsto ψ1).comp hpre.tendsto_φ1
    have hsucc_j :
        Filter.Tendsto (fun n => φ1Iter (subseq n + 1) j)
          Filter.atTop (nhds (ψ1Succ j)) :=
      ((continuous_apply j).tendsto ψ1Succ).comp hpre.tendsto_φ1_succ
    have hcurr_i :
        Filter.Tendsto (fun n => φ1Iter (subseq n) i)
          Filter.atTop (nhds (ψ1 i)) :=
      ((continuous_apply i).tendsto ψ1).comp hpre.tendsto_φ1
    have hcluster :
        Filter.Tendsto
          (fun n => φ1Iter (subseq n + 1) i * φ1Iter (subseq n) j -
            φ1Iter (subseq n + 1) j * φ1Iter (subseq n) i)
          Filter.atTop (nhds (ψ1Succ i * ψ1 j - ψ1Succ j * ψ1 i)) :=
      (hsucc_i.mul hcurr_j).sub (hsucc_j.mul hcurr_i)
    have hzero :
        Filter.Tendsto
          (fun n => φ1Iter (subseq n + 1) i * φ1Iter (subseq n) j -
            φ1Iter (subseq n + 1) j * φ1Iter (subseq n) i)
          Filter.atTop (nhds (0 : ℝ)) := by
      have hcoord := (tendsto_pi_nhds.mp hφ1_drift) (i, j)
      simpa using hcoord
    exact tendsto_nhds_unique hcluster hzero

/-- Remaining C2-projective dynamical seam, now moved before cluster-limit packaging.

This is the true projective/Hilbert-contraction residue after the elementary normalization algebra
has been extracted.  It is stated directly as asymptotic projective regularity of the mixed phases
along the selected absolute subsequence; the following wrapper passes it to the raw-precluster
successor/current limit alignment. -/
theorem sinkhorn_mixed_successor_projective_drift_tendsto_zero_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornMixedProjectiveDriftZeroAlong φhat0Iter φ1Iter subseq := by
  sorry

/-- Limit-level mixed successor/current projective alignment, obtained from the sequence-level
projective-drift seam and the raw precluster. -/
theorem sinkhorn_mixed_successor_projective_alignment_from_gauge_iterates
    {ι : Type*} [Fintype ι]
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
    SinkhornMixedSuccessorProjectiveAlignment ψhat0 ψhat0Succ ψ1 ψ1Succ := by
  have hdrift : SinkhornMixedProjectiveDriftZeroAlong φhat0Iter φ1Iter subseq :=
    sinkhorn_mixed_successor_projective_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hiter hgauge hbounds
  exact sinkhorn_mixed_successor_projective_alignment_of_projective_drift
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hpre hdrift

/-- Package the remaining mixed-phase projective alignment seam into quotient-predecessor
denominator projective alignment.

After the previous theorem supplies projective alignment of `ψhat0Succ` with `ψhat0` and `ψ1Succ`
with `ψ1`, the rest is algebra from the two precluster normalization equations. -/
theorem sinkhorn_denominator_quotient_predecessor_projective_alignment_from_gauge_iterates
    {ι : Type*} [Fintype ι]
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
    SinkhornDenominatorQuotientPredecessorProjectiveAlignment p q ψ0 ψhat0 ψ1 ψhat1 := by
  have hmixed : SinkhornMixedSuccessorProjectiveAlignment ψhat0 ψhat0Succ ψ1 ψ1Succ :=
    sinkhorn_mixed_successor_projective_alignment_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_denominator_quotient_predecessor_projective_alignment_of_mixed_successor_alignment
    p q G φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre hmixed

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
