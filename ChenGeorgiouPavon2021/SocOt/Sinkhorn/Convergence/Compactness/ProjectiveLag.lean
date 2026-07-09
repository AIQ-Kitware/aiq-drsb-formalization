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


/-- Sequence-level projective drift for the left hatted mixed phase along the selected
absolute subsequence.

This is the first of the two clean Hilbert-contraction/asymptotic-regularity subproblems: the
successor vector `φhat0Iter (subseq n + 1)` should become projectively parallel to the current
vector `φhat0Iter (subseq n)`. -/
abbrev SinkhornHattedLeftProjectiveDriftZeroAlong {ι : Type*} [Fintype ι]
    (φhat0Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
    (fun n => fun ij : ι × ι =>
      φhat0Iter (subseq n + 1) ij.1 * φhat0Iter (subseq n) ij.2 -
        φhat0Iter (subseq n + 1) ij.2 * φhat0Iter (subseq n) ij.1)
    Filter.atTop (nhds (0 : ι × ι → ℝ))

/-- Sequence-level projective drift for the right mixed phase along the selected absolute
subsequence.

This is the second Hilbert-contraction/asymptotic-regularity subproblem: the successor vector
`φ1Iter (subseq n + 1)` should become projectively parallel to the current vector
`φ1Iter (subseq n)`. -/
abbrev SinkhornRightProjectiveDriftZeroAlong {ι : Type*} [Fintype ι]
    (φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
    (fun n => fun ij : ι × ι =>
      φ1Iter (subseq n + 1) ij.1 * φ1Iter (subseq n) ij.2 -
        φ1Iter (subseq n + 1) ij.2 * φ1Iter (subseq n) ij.1)
    Filter.atTop (nhds (0 : ι × ι → ℝ))

/-- Sequence-level mixed-phase projective drift along the selected absolute subsequence.

This is now explicitly the conjunction of the two one-sided mixed-phase subproblems. -/
abbrev SinkhornMixedProjectiveDriftZeroAlong {ι : Type*} [Fintype ι]
    (φhat0Iter φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  SinkhornHattedLeftProjectiveDriftZeroAlong φhat0Iter subseq ∧
    SinkhornRightProjectiveDriftZeroAlong φ1Iter subseq

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


/-- Ratio-form projective drift for the left hatted mixed phase.

This is the Hilbert/projective displacement written before clearing denominators.  Under a uniform
positive box it implies the cross-product drift predicate above, but it is the more natural output
of a Birkhoff/Hilbert contraction proof. -/
abbrev SinkhornHattedLeftProjectiveRatioDriftZeroAlong {ι : Type*} [Fintype ι]
    (φhat0Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
    (fun n => fun ij : ι × ι =>
      φhat0Iter (subseq n + 1) ij.1 / φhat0Iter (subseq n) ij.1 -
        φhat0Iter (subseq n + 1) ij.2 / φhat0Iter (subseq n) ij.2)
    Filter.atTop (nhds (0 : ι × ι → ℝ))

/-- Ratio-form projective drift for the right mixed phase. -/
abbrev SinkhornRightProjectiveRatioDriftZeroAlong {ι : Type*} [Fintype ι]
    (φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
    (fun n => fun ij : ι × ι =>
      φ1Iter (subseq n + 1) ij.1 / φ1Iter (subseq n) ij.1 -
        φ1Iter (subseq n + 1) ij.2 / φ1Iter (subseq n) ij.2)
    Filter.atTop (nhds (0 : ι × ι → ℝ))

/-- Mixed ratio-form projective drift, split into the two mixed phases. -/
abbrev SinkhornMixedProjectiveRatioDriftZeroAlong {ι : Type*} [Fintype ι]
    (φhat0Iter φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  SinkhornHattedLeftProjectiveRatioDriftZeroAlong φhat0Iter subseq ∧
    SinkhornRightProjectiveRatioDriftZeroAlong φ1Iter subseq

/-- A scalar envelope for the left hatted mixed ratio-displacement family.

This is the first genuinely dynamical projective-contraction subproblem: construct a vanishing
one-dimensional modulus that bounds every coordinate ratio displacement of
`φhat0Iter (k + 1) / φhat0Iter k`. -/
abbrev SinkhornHattedLeftProjectiveRatioDriftEnvelopeAlong {ι : Type*} [Fintype ι]
    (φhat0Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  ∃ η : ℕ → ℝ,
    Filter.Tendsto η Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ᶠ n in Filter.atTop, ∀ i j,
        |φhat0Iter (subseq n + 1) i / φhat0Iter (subseq n) i -
          φhat0Iter (subseq n + 1) j / φhat0Iter (subseq n) j| ≤ η n

/-- A scalar envelope for the right mixed ratio-displacement family.

This is the second genuinely dynamical projective-contraction subproblem: construct a vanishing
one-dimensional modulus that bounds every coordinate ratio displacement of
`φ1Iter (k + 1) / φ1Iter k`. -/
abbrev SinkhornRightProjectiveRatioDriftEnvelopeAlong {ι : Type*} [Fintype ι]
    (φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  ∃ η : ℕ → ℝ,
    Filter.Tendsto η Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ᶠ n in Filter.atTop, ∀ i j,
        |φ1Iter (subseq n + 1) i / φ1Iter (subseq n) i -
          φ1Iter (subseq n + 1) j / φ1Iter (subseq n) j| ≤ η n

/-- Mixed scalar envelopes for the two ratio-displacement families.

This is deliberately a conjunction of the left and right envelopes, rather than a single shared
modulus.  That makes the remaining proof debt visible: there are two symmetric Hilbert/Birkhoff
asymptotic-regularity arguments left, one for each mixed phase. -/
abbrev SinkhornMixedProjectiveRatioDriftEnvelopeAlong {ι : Type*} [Fintype ι]
    (φhat0Iter φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  SinkhornHattedLeftProjectiveRatioDriftEnvelopeAlong φhat0Iter subseq ∧
    SinkhornRightProjectiveRatioDriftEnvelopeAlong φ1Iter subseq

/-- Backward denominator ratio envelope for one positive phase along an absolute subsequence.

This is the denominator-side target naturally equivalent to the hatted-left and right-forward
successor/current ratio envelopes after the Sinkhorn normalization equations.  The envelope is a
tail bound (`∀ᶠ`) rather than a global bound because the predecessor expression is only dynamically
meaningful once the selected absolute index is positive. -/
abbrev SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAlong {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  ∃ η : ℕ → ℝ,
    Filter.Tendsto η Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ᶠ n in Filter.atTop, ∀ i j,
        |u ((subseq n).pred) i / u (subseq n) i -
          u ((subseq n).pred) j / u (subseq n) j| ≤ η n

/-- Full-orbit backward denominator ratio envelope for one positive phase.

This is stronger than the along-subsequence envelope above and is the natural target for the
Hilbert/Birkhoff engine: the projective oscillation decay is a property of the whole Sinkhorn orbit,
not of the particular compactness subsequence selected later. -/
abbrev SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAtTop {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) : Prop :=
  ∃ η : ℕ → ℝ,
    Filter.Tendsto η Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ᶠ k in Filter.atTop, ∀ i j,
        |u k.pred i / u k i - u k.pred j / u k j| ≤ η k

/-- Full-orbit coupled backward ratio envelopes for the two denominator phases. -/
abbrev SinkhornBackwardDenominatorProjectiveRatioDriftEnvelopesAtTop {ι : Type*} [Fintype ι]
    (φ0Iter φhat1Iter : ℕ → ι → ℝ) : Prop :=
  SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAtTop φ0Iter ∧
    SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAtTop φhat1Iter

/-- Restrict a full-orbit backward ratio envelope to a strict absolute subsequence. -/
theorem sinkhorn_phase_backward_projective_ratio_drift_envelope_along_of_atTop
    {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hglobal : SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAtTop u) :
    SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAlong u subseq := by
  obtain ⟨η, hη, hbound⟩ := hglobal
  refine ⟨fun n => η (subseq n), hη.comp hsubseq.tendsto_atTop, ?_⟩
  exact hsubseq.tendsto_atTop.eventually hbound

/-- Restrict the coupled full-orbit denominator envelopes to a strict absolute subsequence. -/
theorem sinkhorn_backward_denominator_projective_ratio_drift_envelopes_along_of_atTop
    {ι : Type*} [Fintype ι]
    (φ0Iter φhat1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hglobal : SinkhornBackwardDenominatorProjectiveRatioDriftEnvelopesAtTop
      φ0Iter φhat1Iter) :
    SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAlong φ0Iter subseq ∧
      SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAlong φhat1Iter subseq := by
  exact ⟨
    sinkhorn_phase_backward_projective_ratio_drift_envelope_along_of_atTop
      φ0Iter subseq hsubseq hglobal.1,
    sinkhorn_phase_backward_projective_ratio_drift_envelope_along_of_atTop
      φhat1Iter subseq hsubseq hglobal.2⟩

/-- A strictly increasing natural subsequence is eventually positive.

This small fact is what permits the projective engine to use predecessor update equations without
polluting the final envelope statements with finitely many initial-index exceptions. -/
theorem strictMono_nat_eventually_pos (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq) :
    ∀ᶠ n in Filter.atTop, 0 < subseq n := by
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro n hn
  have h0n : 0 < n := lt_of_lt_of_le zero_lt_one hn
  exact lt_of_le_of_lt (Nat.zero_le (subseq 0)) (hsubseq h0n)

/-- A finite-function sequence tends to zero if all coordinates are bounded by a scalar envelope
that tends to zero. -/
theorem finite_function_tendsto_zero_of_abs_le_vanishing_envelope {ι : Type*} [Fintype ι]
    (f : ℕ → ι → ℝ) (η : ℕ → ℝ)
    (hη : Filter.Tendsto η Filter.atTop (nhds (0 : ℝ)))
    (hbound : ∀ᶠ n in Filter.atTop, ∀ i, |f n i| ≤ η n) :
    Filter.Tendsto f Filter.atTop (nhds (0 : ι → ℝ)) := by
  apply finite_function_tendsto_of_coordinate_tendsto
  intro i
  rw [Metric.tendsto_atTop]
  rw [Metric.tendsto_atTop] at hη
  rw [Filter.eventually_atTop] at hbound
  intro δ hδ
  obtain ⟨Nη, hNη⟩ := hη δ hδ
  obtain ⟨Nb, hNb⟩ := hbound
  refine ⟨max Nη Nb, fun n hn => ?_⟩
  have hnη : Nη ≤ n := le_trans (Nat.le_max_left Nη Nb) hn
  have hnb : Nb ≤ n := le_trans (Nat.le_max_right Nη Nb) hn
  have hη_small : |η n| < δ := by
    simpa [Real.dist_eq, sub_zero] using hNη n hnη
  have hfi_le_absη : |f n i| ≤ |η n| :=
    le_trans ((hNb n hnb) i) (le_abs_self (η n))
  have hdist : |f n i - 0| < δ := by
    simpa [sub_zero] using lt_of_le_of_lt hfi_le_absη hη_small
  simpa [Real.dist_eq] using hdist

/-- Convert the split scalar projective-oscillation envelopes into the mixed ratio-drift
predicate. -/
theorem sinkhorn_mixed_projective_ratio_drift_zero_of_envelope {ι : Type*} [Fintype ι]
    (φhat0Iter φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ)
    (henv : SinkhornMixedProjectiveRatioDriftEnvelopeAlong φhat0Iter φ1Iter subseq) :
    SinkhornMixedProjectiveRatioDriftZeroAlong φhat0Iter φ1Iter subseq := by
  rcases henv with ⟨hleft, hright⟩
  rcases hleft with ⟨ηL, hηL, hleft_bound⟩
  rcases hright with ⟨ηR, hηR, hright_bound⟩
  constructor
  · exact finite_function_tendsto_zero_of_abs_le_vanishing_envelope
      (fun n => fun ij : ι × ι =>
        φhat0Iter (subseq n + 1) ij.1 / φhat0Iter (subseq n) ij.1 -
          φhat0Iter (subseq n + 1) ij.2 / φhat0Iter (subseq n) ij.2)
      ηL hηL (by
        filter_upwards [hleft_bound] with n hn ij
        exact hn ij.1 ij.2)
  · exact finite_function_tendsto_zero_of_abs_le_vanishing_envelope
      (fun n => fun ij : ι × ι =>
        φ1Iter (subseq n + 1) ij.1 / φ1Iter (subseq n) ij.1 -
          φ1Iter (subseq n + 1) ij.2 / φ1Iter (subseq n) ij.2)
      ηR hηR (by
        filter_upwards [hright_bound] with n hn ij
        exact hn ij.1 ij.2)

/-- Multiplying a real sequence that tends to zero by an eventually bounded real sequence still
tends to zero.  This local at-top form is enough for the finite ratio-to-cross-product conversion
below, and avoids importing asymptotic notation just for this elementary estimate. -/
theorem real_tendsto_zero_mul_of_eventually_abs_le_atTop
    (f g : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hg : ∀ᶠ n in Filter.atTop, |g n| ≤ C)
    (hf : Filter.Tendsto f Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto (fun n => f n * g n) Filter.atTop (nhds (0 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  rw [Metric.tendsto_atTop] at hf
  intro δ hδ
  have hC1_pos : 0 < C + 1 := by linarith
  have hδ_scaled : 0 < δ / (C + 1) := div_pos hδ hC1_pos
  obtain ⟨Nf, hNf⟩ := hf (δ / (C + 1)) hδ_scaled
  rw [Filter.eventually_atTop] at hg
  obtain ⟨Ng, hNg⟩ := hg
  refine ⟨max Nf Ng, fun n hn => ?_⟩
  have hn_f : Nf ≤ n := le_trans (Nat.le_max_left Nf Ng) hn
  have hn_g : Ng ≤ n := le_trans (Nat.le_max_right Nf Ng) hn
  have hf_small : |f n| < δ / (C + 1) := by
    simpa [Real.dist_eq] using hNf n hn_f
  have hg_bound : |g n| ≤ C := hNg n hn_g
  have hf_nonneg : 0 ≤ |f n| := abs_nonneg (f n)
  have hmul_le_C : |f n| * |g n| ≤ |f n| * C :=
    mul_le_mul_of_nonneg_left hg_bound hf_nonneg
  have hC_le_C1 : C ≤ C + 1 := by linarith
  have hmul_le_C1 : |f n| * C ≤ |f n| * (C + 1) :=
    mul_le_mul_of_nonneg_left hC_le_C1 hf_nonneg
  have hmul_lt : |f n| * (C + 1) < δ := by
    have htmp := mul_lt_mul_of_pos_right hf_small hC1_pos
    have hcancel : δ / (C + 1) * (C + 1) = δ := by
      field_simp [ne_of_gt hC1_pos]
    simpa [hcancel] using htmp
  have habs : |f n * g n - 0| = |f n| * |g n| := by
    rw [sub_zero, abs_mul]
  have hlt : |f n * g n - 0| < δ := by
    rw [habs]
    exact lt_of_le_of_lt (le_trans hmul_le_C hmul_le_C1) hmul_lt
  simpa [Real.dist_eq] using hlt

/-- Pure finite positive-box conversion from ratio-form projective drift to cross-product
projective drift.

This is the finite algebra seam below Hilbert contraction.  For positive bounded vectors,
vanishing coordinate differences of the ratios
`u (k + 1) i / u k i` imply vanishing cleared-denominator cross-products
`u (k + 1) i * u k j - u (k + 1) j * u k i`.  It contains no Sinkhorn-specific dynamics. -/
theorem finite_mixed_projective_cross_drift_zero_of_ratio_drift_and_bounds {ι : Type*}
    [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hratio : SinkhornMixedProjectiveRatioDriftZeroAlong φhat0Iter φ1Iter subseq) :
    SinkhornMixedProjectiveDriftZeroAlong φhat0Iter φ1Iter subseq := by
  rcases hbounds with ⟨ε, B, hε, hB, _hφ0, hφhat0, hφ1, _hφhat1⟩
  have hB2_nonneg : 0 ≤ B * B := mul_nonneg (le_of_lt hB) (le_of_lt hB)
  constructor
  · apply finite_function_tendsto_of_coordinate_tendsto
    intro ij
    rcases ij with ⟨i, j⟩
    let ratio : ℕ → ℝ := fun n =>
      φhat0Iter (subseq n + 1) i / φhat0Iter (subseq n) i -
        φhat0Iter (subseq n + 1) j / φhat0Iter (subseq n) j
    let denom : ℕ → ℝ := fun n =>
      φhat0Iter (subseq n) i * φhat0Iter (subseq n) j
    have hratio_coord : Filter.Tendsto ratio Filter.atTop (nhds (0 : ℝ)) := by
      have hcoord := (tendsto_pi_nhds.mp hratio.1) (i, j)
      simpa [ratio] using hcoord
    have hdenom_bound_all : ∀ n, |denom n| ≤ B * B := by
      intro n
      have hi_box := hφhat0 (subseq n) i
      have hj_box := hφhat0 (subseq n) j
      have hi_nonneg : 0 ≤ φhat0Iter (subseq n) i :=
        le_trans (le_of_lt hε) hi_box.1
      have hj_nonneg : 0 ≤ φhat0Iter (subseq n) j :=
        le_trans (le_of_lt hε) hj_box.1
      have hprod_nonneg : 0 ≤ φhat0Iter (subseq n) i * φhat0Iter (subseq n) j :=
        mul_nonneg hi_nonneg hj_nonneg
      have hprod_le : φhat0Iter (subseq n) i * φhat0Iter (subseq n) j ≤ B * B :=
        mul_le_mul hi_box.2 hj_box.2 hj_nonneg (le_of_lt hB)
      simpa [denom, abs_of_nonneg hprod_nonneg] using hprod_le
    have hdenom_bound : ∀ᶠ n in Filter.atTop, |denom n| ≤ B * B := by
      filter_upwards [] with n
      exact hdenom_bound_all n
    have hmul : Filter.Tendsto (fun n => ratio n * denom n) Filter.atTop (nhds (0 : ℝ)) :=
      real_tendsto_zero_mul_of_eventually_abs_le_atTop ratio denom (B * B)
        hB2_nonneg hdenom_bound hratio_coord
    have heq :
        (fun n =>
          φhat0Iter (subseq n + 1) i * φhat0Iter (subseq n) j -
            φhat0Iter (subseq n + 1) j * φhat0Iter (subseq n) i) =
          (fun n => ratio n * denom n) := by
      funext n
      have hi_pos : 0 < φhat0Iter (subseq n) i :=
        lt_of_lt_of_le hε (hφhat0 (subseq n) i).1
      have hj_pos : 0 < φhat0Iter (subseq n) j :=
        lt_of_lt_of_le hε (hφhat0 (subseq n) j).1
      dsimp [ratio, denom]
      field_simp [ne_of_gt hi_pos, ne_of_gt hj_pos]
    rw [heq]
    exact hmul
  · apply finite_function_tendsto_of_coordinate_tendsto
    intro ij
    rcases ij with ⟨i, j⟩
    let ratio : ℕ → ℝ := fun n =>
      φ1Iter (subseq n + 1) i / φ1Iter (subseq n) i -
        φ1Iter (subseq n + 1) j / φ1Iter (subseq n) j
    let denom : ℕ → ℝ := fun n =>
      φ1Iter (subseq n) i * φ1Iter (subseq n) j
    have hratio_coord : Filter.Tendsto ratio Filter.atTop (nhds (0 : ℝ)) := by
      have hcoord := (tendsto_pi_nhds.mp hratio.2) (i, j)
      simpa [ratio] using hcoord
    have hdenom_bound_all : ∀ n, |denom n| ≤ B * B := by
      intro n
      have hi_box := hφ1 (subseq n) i
      have hj_box := hφ1 (subseq n) j
      have hi_nonneg : 0 ≤ φ1Iter (subseq n) i :=
        le_trans (le_of_lt hε) hi_box.1
      have hj_nonneg : 0 ≤ φ1Iter (subseq n) j :=
        le_trans (le_of_lt hε) hj_box.1
      have hprod_nonneg : 0 ≤ φ1Iter (subseq n) i * φ1Iter (subseq n) j :=
        mul_nonneg hi_nonneg hj_nonneg
      have hprod_le : φ1Iter (subseq n) i * φ1Iter (subseq n) j ≤ B * B :=
        mul_le_mul hi_box.2 hj_box.2 hj_nonneg (le_of_lt hB)
      simpa [denom, abs_of_nonneg hprod_nonneg] using hprod_le
    have hdenom_bound : ∀ᶠ n in Filter.atTop, |denom n| ≤ B * B := by
      filter_upwards [] with n
      exact hdenom_bound_all n
    have hmul : Filter.Tendsto (fun n => ratio n * denom n) Filter.atTop (nhds (0 : ℝ)) :=
      real_tendsto_zero_mul_of_eventually_abs_le_atTop ratio denom (B * B)
        hB2_nonneg hdenom_bound hratio_coord
    have heq :
        (fun n =>
          φ1Iter (subseq n + 1) i * φ1Iter (subseq n) j -
            φ1Iter (subseq n + 1) j * φ1Iter (subseq n) i) =
          (fun n => ratio n * denom n) := by
      funext n
      have hi_pos : 0 < φ1Iter (subseq n) i :=
        lt_of_lt_of_le hε (hφ1 (subseq n) i).1
      have hj_pos : 0 < φ1Iter (subseq n) j :=
        lt_of_lt_of_le hε (hφ1 (subseq n) j).1
      dsimp [ratio, denom]
      field_simp [ne_of_gt hi_pos, ne_of_gt hj_pos]
    rw [heq]
    exact hmul

/-- Normalization converts the hatted-left successor/current ratio into a backward ratio of the
left denominator phase, eventually along any strict absolute subsequence.

For `k > 0`, the identities
`φhat0Iter (k + 1) i * φ0Iter k i = p i` and
`φhat0Iter k i * φ0Iter (k.pred) i = p i` imply
`φhat0Iter (k + 1) i / φhat0Iter k i = φ0Iter k.pred i / φ0Iter k i`.
This is an algebraic seam, not a Hilbert-contraction seam. -/
theorem sinkhorn_hatted_left_ratio_eventually_eq_phi0_backward_ratio
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ᶠ n in Filter.atTop, ∀ i,
      φhat0Iter (subseq n + 1) i / φhat0Iter (subseq n) i =
        φ0Iter ((subseq n).pred) i / φ0Iter (subseq n) i := by
  filter_upwards [strictMono_nat_eventually_pos subseq hsubseq] with n hsubseq_pos i
  have hpred_succ : (subseq n).pred + 1 = subseq n :=
    Nat.succ_pred_eq_of_pos hsubseq_pos
  have hnorm_succ := hiter.normalize_left (subseq n) i
  have hnorm_pred := hiter.normalize_left ((subseq n).pred) i
  rw [hpred_succ] at hnorm_pred
  have hhat0_ne : φhat0Iter (subseq n) i ≠ 0 :=
    ne_of_gt (hiter.φhat0_pos (subseq n) i)
  have hφ0_ne : φ0Iter (subseq n) i ≠ 0 :=
    ne_of_gt (hiter.φ0_pos (subseq n) i)
  field_simp [hhat0_ne, hφ0_ne]
  nlinarith [hnorm_succ, hnorm_pred]

/-- Normalization converts the right successor/current ratio into a backward ratio of the
hatted-right denominator phase, eventually along any strict absolute subsequence. -/
theorem sinkhorn_right_ratio_eventually_eq_phihat1_backward_ratio
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ᶠ n in Filter.atTop, ∀ j,
      φ1Iter (subseq n + 1) j / φ1Iter (subseq n) j =
        φhat1Iter ((subseq n).pred) j / φhat1Iter (subseq n) j := by
  filter_upwards [strictMono_nat_eventually_pos subseq hsubseq] with n hsubseq_pos j
  have hpred_succ : (subseq n).pred + 1 = subseq n :=
    Nat.succ_pred_eq_of_pos hsubseq_pos
  have hnorm_succ := hiter.normalize_right (subseq n) j
  have hnorm_pred := hiter.normalize_right ((subseq n).pred) j
  rw [hpred_succ] at hnorm_pred
  have hφ1_ne : φ1Iter (subseq n) j ≠ 0 :=
    ne_of_gt (hiter.φ1_pos (subseq n) j)
  have hφhat1_ne : φhat1Iter (subseq n) j ≠ 0 :=
    ne_of_gt (hiter.φhat1_pos (subseq n) j)
  field_simp [hφ1_ne, hφhat1_ne]
  nlinarith [hnorm_succ, hnorm_pred]

/-- Finite scalar spread of the backward ratio vector `u (k.pred) / u k`.

This is a concrete progress metric for the last projective theorem: it is zero exactly when all
backward coordinate ratios agree, and it bounds every coordinatewise ratio displacement.  The final
Hilbert/Birkhoff engine should prove that this scalar spread tends to zero for the two denominator
phases. -/
noncomputable def finiteBackwardRatioSpread {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (k : ℕ) : ℝ :=
  ∑ ij : ι × ι,
    |u k.pred ij.1 / u k ij.1 - u k.pred ij.2 / u k ij.2|

/-- The finite scalar spread bounds each individual backward-ratio displacement. -/
theorem abs_backward_ratio_le_finiteBackwardRatioSpread {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (k : ℕ) (i j : ι) :
    |u k.pred i / u k i - u k.pred j / u k j| ≤
      finiteBackwardRatioSpread u k := by
  classical
  unfold finiteBackwardRatioSpread
  exact Finset.single_le_sum
    (fun ij _hij => abs_nonneg
      (u k.pred ij.1 / u k ij.1 - u k.pred ij.2 / u k ij.2))
    (Finset.mem_univ (i, j))

/-- A vanishing finite backward-ratio spread gives the full-orbit scalar envelope predicate. -/
theorem sinkhorn_phase_backward_projective_ratio_drift_envelope_atTop_of_spread_tendsto_zero
    {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ)
    (hspread : Filter.Tendsto (fun k => finiteBackwardRatioSpread u k)
      Filter.atTop (nhds (0 : ℝ))) :
    SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAtTop u := by
  refine ⟨fun k => finiteBackwardRatioSpread u k, hspread, ?_⟩
  filter_upwards [] with k i j
  exact abs_backward_ratio_le_finiteBackwardRatioSpread u k i j

/-- General nonnegative-sequence criterion used by the last projective engine.

To prove two nonnegative scalar spreads tend to zero, it is enough to rule out every strictly
monotone subsequence on which at least one of the spreads stays above a fixed positive threshold.
This is the compactness/limsup bookkeeping layer, separated from the Sinkhorn-specific
Hilbert/Fortet argument below. -/
private theorem eventually_lt_left_of_no_positive_subsequence
    (s₀ s₁ : ℕ → ℝ)
    (hno_pos_subseq : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧
          ∀ n, ε ≤ s₀ (subseq n) ∨ ε ≤ s₁ (subseq n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, s₀ k < ε := by
  rw [Filter.eventually_atTop]
  by_contra hbad
  push Not at hbad
  have hfreq : ∃ᶠ k in Filter.atTop, ε ≤ s₀ k := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨k, hNk, hkbad⟩ := hbad N
    exact ⟨k, hNk, hkbad⟩
  obtain ⟨subseq, hsubseq, hsubseq_prop⟩ :=
    Filter.extraction_of_frequently_atTop hfreq
  exact hno_pos_subseq ε hε ⟨subseq, hsubseq, fun n => Or.inl (hsubseq_prop n)⟩

private theorem eventually_lt_right_of_no_positive_subsequence
    (s₀ s₁ : ℕ → ℝ)
    (hno_pos_subseq : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧
          ∀ n, ε ≤ s₀ (subseq n) ∨ ε ≤ s₁ (subseq n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, s₁ k < ε := by
  rw [Filter.eventually_atTop]
  by_contra hbad
  push Not at hbad
  have hfreq : ∃ᶠ k in Filter.atTop, ε ≤ s₁ k := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨k, hNk, hkbad⟩ := hbad N
    exact ⟨k, hNk, hkbad⟩
  obtain ⟨subseq, hsubseq, hsubseq_prop⟩ :=
    Filter.extraction_of_frequently_atTop hfreq
  exact hno_pos_subseq ε hε ⟨subseq, hsubseq, fun n => Or.inr (hsubseq_prop n)⟩

private theorem tendsto_nonnegative_atTop_zero_of_eventually_lt
    (s : ℕ → ℝ)
    (hs_nonneg : ∀ k, 0 ≤ s k)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, s k < ε) :
    Filter.Tendsto s Filter.atTop (nhds (0 : ℝ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hsmall ε hε] with k hk
  have hsabs : |s k| = s k := abs_of_nonneg (hs_nonneg k)
  simpa [dist_eq_norm, Real.norm_eq_abs, sub_zero, hsabs] using hk

theorem tendsto_pair_nonnegative_atTop_zero_of_no_positive_subsequence
    (s₀ s₁ : ℕ → ℝ)
    (hs₀_nonneg : ∀ k, 0 ≤ s₀ k)
    (hs₁_nonneg : ∀ k, 0 ≤ s₁ k)
    (hno_pos_subseq : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧
          ∀ n, ε ≤ s₀ (subseq n) ∨ ε ≤ s₁ (subseq n)) :
    Filter.Tendsto s₀ Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto s₁ Filter.atTop (nhds (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · exact tendsto_nonnegative_atTop_zero_of_eventually_lt s₀ hs₀_nonneg
      (fun ε hε => eventually_lt_left_of_no_positive_subsequence s₀ s₁ hno_pos_subseq hε)
  · exact tendsto_nonnegative_atTop_zero_of_eventually_lt s₁ hs₁_nonneg
      (fun ε hε => eventually_lt_right_of_no_positive_subsequence s₀ s₁ hno_pos_subseq hε)


/-- Franklin--Lorenz/Birkhoff-Hopf projective engine for the coupled backward denominator spreads.

This is the remaining paper-level theorem.  Franklin--Lorenz, Section 3, prove geometric Sinkhorn
convergence for strictly positive finite matrices by combining Hilbert's projective metric with
Birkhoff's contraction theorem: Lemma 2 contracts the row/column marginal Hilbert errors by
`κ(G)^2`, and Theorem 4 sums those increments in the diagonal-equivalence metric.  In the current
phase-only formalization, this theorem is the port of that argument to the denominator ratio-spread
quantities monitored below.

The useful source anchors are Franklin--Lorenz (1989), Section 3: Hilbert metric setup and
Birkhoff contraction on pp. 726--728, Lemma 2 on pp. 728--729, and Theorem 4 on pp. 729--731. -/
theorem sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_franklin_lorenz
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    Filter.Tendsto (fun k => finiteBackwardRatioSpread φ0Iter k)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto (fun k => finiteBackwardRatioSpread φhat1Iter k)
        Filter.atTop (nhds (0 : ℝ)) := by
  sorry

private theorem eventually_lt_of_tendsto_zero
    (s : ℕ → ℝ) (hs : Filter.Tendsto s Filter.atTop (nhds (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, s k < ε := by
  have hdist := (Metric.tendsto_nhds.mp hs) ε hε
  filter_upwards [hdist] with k hk
  have habs : |s k - 0| < ε := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hk
  have hle_abs : s k ≤ |s k - 0| := by
    simpa using (le_abs_self (s k))
  exact lt_of_le_of_lt hle_abs habs

/-- A pair of scalar spreads tending to zero rules out a bad positive-spread subsequence. -/
theorem no_positive_subsequence_of_pair_tendsto_zero
    (s₀ s₁ : ℕ → ℝ)
    (hs₀ : Filter.Tendsto s₀ Filter.atTop (nhds (0 : ℝ)))
    (hs₁ : Filter.Tendsto s₁ Filter.atTop (nhds (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ¬ ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧
          ∀ n, ε ≤ s₀ (subseq n) ∨ ε ≤ s₁ (subseq n) := by
  intro ε hε hbad
  obtain ⟨subseq, hsubseq, hsubseq_bad⟩ := hbad
  have hsmall₀ : ∀ᶠ n in Filter.atTop, s₀ (subseq n) < ε :=
    hsubseq.tendsto_atTop.eventually (eventually_lt_of_tendsto_zero s₀ hs₀ hε)
  have hsmall₁ : ∀ᶠ n in Filter.atTop, s₁ (subseq n) < ε :=
    hsubseq.tendsto_atTop.eventually (eventually_lt_of_tendsto_zero s₁ hs₁ hε)
  rw [Filter.eventually_atTop] at hsmall₀ hsmall₁
  obtain ⟨N₀, hN₀⟩ := hsmall₀
  obtain ⟨N₁, hN₁⟩ := hsmall₁
  let n : ℕ := max N₀ N₁
  have hn₀ : N₀ ≤ n := by
    dsimp [n]
    exact le_max_left N₀ N₁
  have hn₁ : N₁ ≤ n := by
    dsimp [n]
    exact le_max_right N₀ N₁
  have h0lt : s₀ (subseq n) < ε := hN₀ n hn₀
  have h1lt : s₁ (subseq n) < ε := hN₁ n hn₁
  cases hsubseq_bad n with
  | inl h0 => exact (not_le_of_gt h0lt) h0
  | inr h1 => exact (not_le_of_gt h1lt) h1

/-- No positive-limsup subsequence for the coupled backward denominator spread.

This is now the single Sinkhorn-specific hard theorem.  The uploaded distillations identify the
intended route as Franklin--Lorenz matrix-scaling convergence plus the Carroll / Birkhoff--Hopf
positive-matrix contraction principle: assume a bad subsequence with spread bounded below, extract a
phase-compatible finite cluster using the uniform box bounds, pass the alternating positive-kernel
update equations to the limit, and use strict positivity of `G` to force the two backward-ratio
vectors to be projectively constant, contradicting the positive spread. -/
theorem sinkhorn_backward_denominator_projective_ratio_spreads_no_positive_subsequence_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ ε : ℝ, 0 < ε →
      ¬ ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧
          ∀ n,
            ε ≤ finiteBackwardRatioSpread φ0Iter (subseq n) ∨
              ε ≤ finiteBackwardRatioSpread φhat1Iter (subseq n) := by
  exact no_positive_subsequence_of_pair_tendsto_zero
    (fun k => finiteBackwardRatioSpread φ0Iter k)
    (fun k => finiteBackwardRatioSpread φhat1Iter k)
    (sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_franklin_lorenz
      p q G φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hG hiter hgauge hbounds).1
    (sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_franklin_lorenz
      p q G φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hG hiter hgauge hbounds).2

/-- Full-orbit coupled positive-kernel scalar spread collapse for both backward denominator ratios.

The theorem now factors into two pieces:

* a pure order/topology lemma excluding positive-limsup subsequences;
* the Sinkhorn-specific Fortet/Hilbert argument that proves such bad subsequences cannot exist.

The concrete scalar quantities monitored are:

* `finiteBackwardRatioSpread φ0Iter k`;
* `finiteBackwardRatioSpread φhat1Iter k`. -/
theorem sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    Filter.Tendsto (fun k => finiteBackwardRatioSpread φ0Iter k)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto (fun k => finiteBackwardRatioSpread φhat1Iter k)
        Filter.atTop (nhds (0 : ℝ)) := by
  have hφ0_nonneg : ∀ k, 0 ≤ finiteBackwardRatioSpread φ0Iter k := by
    intro k
    unfold finiteBackwardRatioSpread
    exact Finset.sum_nonneg (fun ij _hij => abs_nonneg
      (φ0Iter k.pred ij.1 / φ0Iter k ij.1 - φ0Iter k.pred ij.2 / φ0Iter k ij.2))
  have hφhat1_nonneg : ∀ k, 0 ≤ finiteBackwardRatioSpread φhat1Iter k := by
    intro k
    unfold finiteBackwardRatioSpread
    exact Finset.sum_nonneg (fun ij _hij => abs_nonneg
      (φhat1Iter k.pred ij.1 / φhat1Iter k ij.1 -
        φhat1Iter k.pred ij.2 / φhat1Iter k ij.2))
  exact tendsto_pair_nonnegative_atTop_zero_of_no_positive_subsequence
    (fun k => finiteBackwardRatioSpread φ0Iter k)
    (fun k => finiteBackwardRatioSpread φhat1Iter k)
    hφ0_nonneg hφhat1_nonneg
    (sinkhorn_backward_denominator_projective_ratio_spreads_no_positive_subsequence_from_gauge_iterates
      p q G φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hG hiter hgauge hbounds)

/-- Full-orbit coupled positive-kernel oscillation envelope for both backward denominator ratios.

The hard work is the scalar-spread theorem above.  This wrapper turns the two scalar spreads into
the envelope predicate used by the downstream ratio-to-cross and compactness wrappers. -/
theorem sinkhorn_backward_denominator_projective_ratio_drift_envelopes_atTop_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornBackwardDenominatorProjectiveRatioDriftEnvelopesAtTop φ0Iter φhat1Iter := by
  obtain ⟨hφ0_spread, hφhat1_spread⟩ :=
    sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_gauge_iterates
      p q G φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hG hiter hgauge hbounds
  exact ⟨
    sinkhorn_phase_backward_projective_ratio_drift_envelope_atTop_of_spread_tendsto_zero
      φ0Iter hφ0_spread,
    sinkhorn_phase_backward_projective_ratio_drift_envelope_atTop_of_spread_tendsto_zero
      φhat1Iter hφhat1_spread⟩

/-- Coupled positive-kernel oscillation envelope for both backward denominator ratios along a
strict absolute subsequence.

The hard work is the full-orbit theorem above.  This wrapper only restricts that full-orbit
envelope to the subsequence selected by compactness. -/
theorem sinkhorn_backward_denominator_projective_ratio_drift_envelopes_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAlong φ0Iter subseq ∧
      SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAlong φhat1Iter subseq := by
  exact sinkhorn_backward_denominator_projective_ratio_drift_envelopes_along_of_atTop
    φ0Iter φhat1Iter subseq hsubseq
    (sinkhorn_backward_denominator_projective_ratio_drift_envelopes_atTop_from_gauge_iterates
      p q G φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hG hiter hgauge hbounds)

/-- Positive-kernel oscillation envelope for the backward ratios of the left denominator phase.

This projection is kept as the public one-sided seam used by the hatted-left mixed ratio wrapper.
The actual coupled Hilbert/Birkhoff proof lives in
`sinkhorn_backward_denominator_projective_ratio_drift_envelopes_from_gauge_iterates`. -/
theorem sinkhorn_phi0_backward_projective_ratio_drift_envelope_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAlong φ0Iter subseq := by
  exact (sinkhorn_backward_denominator_projective_ratio_drift_envelopes_from_gauge_iterates p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
    hsubseq hG hiter hgauge hbounds).1

/-- Positive-kernel oscillation envelope for the backward ratios of the hatted-right denominator
phase.  This is the right projection of the same coupled positive-kernel oscillation engine. -/
theorem sinkhorn_phihat1_backward_projective_ratio_drift_envelope_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornPhaseBackwardProjectiveRatioDriftEnvelopeAlong φhat1Iter subseq := by
  exact (sinkhorn_backward_denominator_projective_ratio_drift_envelopes_from_gauge_iterates p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
    hsubseq hG hiter hgauge hbounds).2

/-- Vanishing scalar envelope for the left hatted mixed ratio drift from the
positive-kernel Sinkhorn dynamics.

The proof now factors into an algebraic normalization identity and the actual positive-kernel
oscillation envelope for the left denominator phase. -/
theorem sinkhorn_hatted_left_projective_ratio_drift_envelope_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornHattedLeftProjectiveRatioDriftEnvelopeAlong φhat0Iter subseq := by
  obtain ⟨η, hη, hdenom⟩ :=
    sinkhorn_phi0_backward_projective_ratio_drift_envelope_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds
  refine ⟨η, hη, ?_⟩
  have heq := sinkhorn_hatted_left_ratio_eventually_eq_phi0_backward_ratio p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hsubseq hiter
  filter_upwards [heq, hdenom] with n hn_eq hn_denom i j
  simpa [hn_eq i, hn_eq j] using hn_denom i j

/-- Vanishing scalar envelope for the right mixed ratio drift from the positive-kernel Sinkhorn
dynamics.

The proof now factors into an algebraic normalization identity and the actual positive-kernel
oscillation envelope for the hatted-right denominator phase. -/
theorem sinkhorn_right_projective_ratio_drift_envelope_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornRightProjectiveRatioDriftEnvelopeAlong φ1Iter subseq := by
  obtain ⟨η, hη, hdenom⟩ :=
    sinkhorn_phihat1_backward_projective_ratio_drift_envelope_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds
  refine ⟨η, hη, ?_⟩
  have heq := sinkhorn_right_ratio_eventually_eq_phihat1_backward_ratio p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hsubseq hiter
  filter_upwards [heq, hdenom] with n hn_eq hn_denom i j
  simpa [hn_eq i, hn_eq j] using hn_denom i j

/-- Vanishing scalar envelopes for mixed projective ratio drift from the positive-kernel Sinkhorn
dynamics.

The remaining proof debt is deliberately split into the two one-sided Hilbert/Birkhoff envelope
lemmas above.  This wrapper only packages those envelopes back into the mixed predicate expected by
the downstream finite-topological conversion. -/
theorem sinkhorn_mixed_projective_ratio_drift_envelope_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornMixedProjectiveRatioDriftEnvelopeAlong φhat0Iter φ1Iter subseq := by
  exact ⟨
    sinkhorn_hatted_left_projective_ratio_drift_envelope_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds,
    sinkhorn_right_projective_ratio_drift_envelope_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds⟩

/-- Ratio-form mixed projective drift from the positive-kernel Sinkhorn dynamics.

The dynamical content is isolated in the scalar-envelope theorem above; this wrapper is only the
finite-topological conversion from a vanishing projective-oscillation envelope to product-space
ratio drift. -/
theorem sinkhorn_mixed_projective_ratio_drift_tendsto_zero_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornMixedProjectiveRatioDriftZeroAlong φhat0Iter φ1Iter subseq := by
  exact sinkhorn_mixed_projective_ratio_drift_zero_of_envelope φhat0Iter φ1Iter subseq
    (sinkhorn_mixed_projective_ratio_drift_envelope_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds)

/-- Left mixed-phase projective drift from the Sinkhorn dynamics.

The Sinkhorn-specific proof now factors through the ratio-form Hilbert displacement and the pure
finite positive-box conversion from ratio drift to cleared cross-products. -/
theorem sinkhorn_hatted_left_projective_drift_tendsto_zero_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornHattedLeftProjectiveDriftZeroAlong φhat0Iter subseq := by
  have hratio : SinkhornMixedProjectiveRatioDriftZeroAlong φhat0Iter φ1Iter subseq :=
    sinkhorn_mixed_projective_ratio_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds
  exact (finite_mixed_projective_cross_drift_zero_of_ratio_drift_and_bounds
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hbounds hratio).1

/-- Right mixed-phase projective drift from the Sinkhorn dynamics.

This is the right projection of the same ratio-form Hilbert displacement plus the finite
positive-box clearing-denominators conversion. -/
theorem sinkhorn_right_projective_drift_tendsto_zero_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornRightProjectiveDriftZeroAlong φ1Iter subseq := by
  have hratio : SinkhornMixedProjectiveRatioDriftZeroAlong φhat0Iter φ1Iter subseq :=
    sinkhorn_mixed_projective_ratio_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds
  exact (finite_mixed_projective_cross_drift_zero_of_ratio_drift_and_bounds
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hbounds hratio).2

/-- Remaining C2-projective dynamical seam, now factored into the two one-sided mixed-phase
subproblems above. -/
theorem sinkhorn_mixed_successor_projective_drift_tendsto_zero_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    SinkhornMixedProjectiveDriftZeroAlong φhat0Iter φ1Iter subseq := by
  exact ⟨
    sinkhorn_hatted_left_projective_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds,
    sinkhorn_right_projective_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      hsubseq hG hiter hgauge hbounds⟩

/-- Limit-level mixed successor/current projective alignment, obtained from the sequence-level
projective-drift seam and the raw precluster. -/
theorem sinkhorn_mixed_successor_projective_alignment_from_gauge_iterates
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
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
      hpre.strict_mono hG hiter hgauge hbounds
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
    (hG : ∀ i j, 0 < G i j)
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
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hG hiter hgauge hbounds hpre
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
    (hG : ∀ i j, 0 < G i j)
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
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hG hiter hgauge hbounds hpre
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
    (hG : ∀ i j, 0 < G i j)
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
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hG hiter hgauge hbounds hpre
  exact sinkhorn_denominator_projective_lag_zero_of_predecessor_projective_limits
    φ0Iter φhat1Iter subseq ψ0 ψhat1 hpre.tendsto_φ0 hpre.tendsto_φhat1
    hφ0Pred hφhat1Pred


end ChenGeorgiouPavon2021
