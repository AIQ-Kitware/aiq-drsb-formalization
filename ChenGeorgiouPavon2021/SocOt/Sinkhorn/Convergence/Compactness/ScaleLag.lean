/-
# Scale lag for Sinkhorn denominator phases

This file owns scalar/total-mass control after projective lag collapse.  The `φ0` scale lag is proved
from the gauge; the remaining hard seam is the `φhat1` total-mass lag.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.ProjectiveLag

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- The `φ0` denominator scale lag is fixed exactly by the gauge normalization. -/
theorem sinkhorn_phi0_scale_lag_zero_from_gauge {ι : Type*} [Fintype ι]
    (φ0Iter _φhat0Iter _φ1Iter _φhat1Iter : ℕ → ι → ℝ)
    (φ0 _φhat0 _φ1 _φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter _φhat0Iter _φ1Iter _φhat1Iter
      φ0 _φhat0 _φ1 _φhat1) :
    SinkhornPhaseScaleLagZeroAlong φ0Iter subseq := by
  change Filter.Tendsto
    (fun n => (∑ i, φ0Iter (subseq n) i) - ∑ i, φ0Iter ((subseq n).pred) i)
    Filter.atTop (nhds (0 : ℝ))
  have hzero :
      (fun n => (∑ i, φ0Iter (subseq n) i) - ∑ i, φ0Iter ((subseq n).pred) i) =
        fun _ : ℕ => (0 : ℝ) := by
    funext n
    rw [hgauge.left_total (subseq n), hgauge.left_total ((subseq n).pred), sub_self]
  rw [hzero]
  exact (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))


/-- Finite-sum continuity for function-valued sequences, kept local to the compactness fanout so the
scale file does not import the later convergence/gauge assembly modules. -/
theorem sinkhorn_compactness_finite_sum_tendsto_of_function_tendsto {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (h : Filter.Tendsto x Filter.atTop (nhds xLim)) :
    Filter.Tendsto (fun n => ∑ i, x n i) Filter.atTop (nhds (∑ i, xLim i)) := by
  have hcont : Continuous (fun y : ι → ℝ => ∑ i, y i) := by
    fun_prop
  change Filter.Tendsto ((fun y : ι → ℝ => ∑ i, y i) ∘ x)
    Filter.atTop (nhds (∑ i, xLim i))
  exact (hcont.tendsto xLim).comp h


/-- Right normalization passed to a raw six-stream precluster.

This is the quotient identity that fixes the product of the successor mixed phase and the current
`φhat1` denominator limit:
`ψ1Succ j * ψhat1 j = q j`.  The lagged-total core below uses this together with the lagged
normalization equation at `(subseq n).pred`; keeping this limit-passage lemma separate makes the
remaining scalar obstruction explicit. -/
theorem sinkhorn_precluster_normalize_right_successor {ι : Type*} [Fintype ι]
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


/-- The fixed left-total gauge passed to the current raw precluster. -/
theorem sinkhorn_precluster_left_gauge_current_sum {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    ∑ i, ψ0 i = ∑ i, φ0 i := by
  have hsum_cluster :
      Filter.Tendsto (fun n => ∑ i, φ0Iter (subseq n) i)
        Filter.atTop (nhds (∑ i, ψ0 i)) :=
    sinkhorn_compactness_finite_sum_tendsto_of_function_tendsto
      (fun n => φ0Iter (subseq n)) ψ0 hpre.tendsto_φ0
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

/-- The current forward equation passed to a raw precluster. -/
theorem sinkhorn_precluster_forward_current {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    ∀ i, ψ0 i = ∑ j, G i j * ψ1 j := by
  intro i
  have hφ0i :
      Filter.Tendsto (fun n => φ0Iter (subseq n) i) Filter.atTop (nhds (ψ0 i)) :=
    ((continuous_apply i).tendsto ψ0).comp hpre.tendsto_φ0
  have hforward_sum :
      Filter.Tendsto (fun n => ∑ j, G i j * φ1Iter (subseq n) j)
        Filter.atTop (nhds (∑ j, G i j * ψ1 j)) := by
    have hcont : Continuous (fun y : ι → ℝ => ∑ j, G i j * y j) := by
      fun_prop
    change Filter.Tendsto ((fun y : ι → ℝ => ∑ j, G i j * y j) ∘
        (fun n => φ1Iter (subseq n))) Filter.atTop (nhds (∑ j, G i j * ψ1 j))
    exact (hcont.tendsto ψ1).comp hpre.tendsto_φ1
  have hforward_as_φ0 :
      Filter.Tendsto (fun n => ∑ j, G i j * φ1Iter (subseq n) j)
        Filter.atTop (nhds (ψ0 i)) := by
    have hseq_eq :
        (fun n => ∑ j, G i j * φ1Iter (subseq n) j) =
          (fun n => φ0Iter (subseq n) i) := by
      funext n
      exact (hiter.forward (subseq n) i).symm
    rw [hseq_eq]
    exact hφ0i
  exact tendsto_nhds_unique hforward_as_φ0 hforward_sum

/-- The forward equation and fixed gauge passed to the successor right phase. -/
theorem sinkhorn_precluster_forward_successor_gauge_sum {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    (∑ i, ∑ j, G i j * ψ1Succ j) = ∑ i, φ0 i := by
  have hsum_limit :
      Filter.Tendsto (fun n => ∑ i, ∑ j, G i j * φ1Iter (subseq n + 1) j)
        Filter.atTop (nhds (∑ i, ∑ j, G i j * ψ1Succ j)) := by
    have hcont : Continuous (fun y : ι → ℝ => ∑ i, ∑ j, G i j * y j) := by
      fun_prop
    change Filter.Tendsto ((fun y : ι → ℝ => ∑ i, ∑ j, G i j * y j) ∘
        (fun n => φ1Iter (subseq n + 1))) Filter.atTop
        (nhds (∑ i, ∑ j, G i j * ψ1Succ j))
    exact (hcont.tendsto ψ1Succ).comp hpre.tendsto_φ1_succ
  have hsum_target :
      Filter.Tendsto (fun n => ∑ i, ∑ j, G i j * φ1Iter (subseq n + 1) j)
        Filter.atTop (nhds (∑ i, φ0 i)) := by
    have hseq_eq :
        (fun n => ∑ i, ∑ j, G i j * φ1Iter (subseq n + 1) j) =
          (fun n => ∑ i, φ0Iter (subseq n + 1) i) := by
      funext n
      apply Finset.sum_congr rfl
      intro i _hi
      exact (hiter.forward (subseq n + 1) i).symm
    rw [hseq_eq]
    have hconst :
        (fun n => ∑ i, φ0Iter (subseq n + 1) i) = (fun _ : ℕ => ∑ i, φ0 i) := by
      funext n
      exact hgauge.left_total (subseq n + 1)
    rw [hconst]
    exact (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => ∑ i, φ0 i) Filter.atTop (nhds (∑ i, φ0 i)))
  exact tendsto_nhds_unique hsum_limit hsum_target

/-- The current forward equation and fixed gauge, rewritten as the weighted right-phase total. -/
theorem sinkhorn_precluster_forward_current_gauge_sum {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    (∑ i, ∑ j, G i j * ψ1 j) = ∑ i, φ0 i := by
  have hforward : ∀ i, ψ0 i = ∑ j, G i j * ψ1 j :=
    sinkhorn_precluster_forward_current p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre
  have hgauge_current : ∑ i, ψ0 i = ∑ i, φ0 i :=
    sinkhorn_precluster_left_gauge_current_sum
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hgauge hpre
  calc
    (∑ i, ∑ j, G i j * ψ1 j) = ∑ i, ψ0 i := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (hforward i).symm
    _ = ∑ i, φ0 i := hgauge_current


/-- Lagged right normalization passed to the raw precluster, conditional on the current-phase limit
normalization identity `ψ1 j * ψhat1 j = q j`.

The remaining scale-specific mathematical task is now isolated to proving that current-phase
identity from the gauge and projective lag hypotheses.  Once it is known, the actual lagged
`φhat1` vector converges coordinatewise by dividing the lagged normalization equation at
`(subseq n).pred`, and finite-sum continuity gives total-mass convergence. -/
theorem sinkhorn_phihat1_lagged_tendsto_from_current_right_normalization {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hright_current : ∀ j, ψ1 j * ψhat1 j = q j) :
    Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred)) Filter.atTop (nhds ψhat1) := by
  apply pi_tendsto_of_coordinate_tendsto
  intro j
  have hφ1 :
      Filter.Tendsto (fun n => φ1Iter (subseq n) j)
        Filter.atTop (nhds (ψ1 j)) :=
    ((continuous_apply j).tendsto ψ1).comp hpre.tendsto_φ1
  have hψ1_pos : 0 < ψ1 j := hpre.positive.2.2.2.1 j
  have hψ1_ne : ψ1 j ≠ 0 := ne_of_gt hψ1_pos
  have hdiv :
      Filter.Tendsto (fun n => q j / φ1Iter (subseq n) j)
        Filter.atTop (nhds (q j / ψ1 j)) := by
    exact (tendsto_const_nhds.div hφ1 hψ1_ne)
  have hq_div : q j / ψ1 j = ψhat1 j := by
    rw [← hright_current j]
    field_simp [hψ1_ne]
  have hsubseq_pos_eventually : ∀ᶠ n in Filter.atTop, 0 < subseq n := by
    rw [Filter.eventually_atTop]
    refine ⟨1, ?_⟩
    intro n hn
    have h0n : 0 < n := by omega
    have hlt : subseq 0 < subseq n := hpre.strict_mono h0n
    exact lt_of_le_of_lt (Nat.zero_le (subseq 0)) hlt
  have hratio_eventually :
      (fun n => φhat1Iter ((subseq n).pred) j) =ᶠ[Filter.atTop]
        (fun n => q j / φ1Iter (subseq n) j) := by
    filter_upwards [hsubseq_pos_eventually] with n hnpos
    have hidx : (subseq n).pred + 1 = subseq n := by
      exact Nat.succ_pred_eq_of_pos hnpos
    have hnorm : φ1Iter (subseq n) j * φhat1Iter ((subseq n).pred) j = q j := by
      have hnorm0 := hiter.normalize_right ((subseq n).pred) j
      rw [hidx] at hnorm0
      exact hnorm0
    have hφ1_ne : φ1Iter (subseq n) j ≠ 0 := ne_of_gt (hiter.φ1_pos (subseq n) j)
    calc
      φhat1Iter ((subseq n).pred) j
          = (φ1Iter (subseq n) j * φhat1Iter ((subseq n).pred) j) /
              φ1Iter (subseq n) j := by
            field_simp [hφ1_ne]
      _ = q j / φ1Iter (subseq n) j := by rw [hnorm]
  simpa [hq_div] using hdiv.congr' hratio_eventually.symm


/-- Projective lag for `φhat1`, after quotient-limit passage for the absolute predecessor.

The sequence-level projective-lag hypothesis compares `φhat1Iter (subseq n)` with the absolute
predecessor `φhat1Iter ((subseq n).pred)`.  The right normalization equation identifies that
predecessor limit as `q / ψ1`; this helper turns the sequence-level lag into the finite quotient
projective identity needed by the remaining scalar algebra. -/
theorem sinkhorn_precluster_phihat1_quotient_projective_from_lag {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hprojective_hat1_lag : SinkhornPhaseProjectiveLagZeroAlong φhat1Iter subseq) :
    ∀ i j, ψhat1 i * (q j / ψ1 j) - ψhat1 j * (q i / ψ1 i) = 0 := by
  have hpred : Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred))
      Filter.atTop (nhds (fun j => q j / ψ1 j)) :=
    sinkhorn_phihat1_predecessor_tendsto_quotient_from_precluster p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre
  intro i j
  have hlag_coord :
      Filter.Tendsto
        (fun n => φhat1Iter (subseq n) i * φhat1Iter ((subseq n).pred) j -
          φhat1Iter (subseq n) j * φhat1Iter ((subseq n).pred) i)
        Filter.atTop (nhds (0 : ℝ)) := by
    have hcoord := ((continuous_apply (i, j)).tendsto (0 : ι × ι → ℝ)).comp
      hprojective_hat1_lag
    change Filter.Tendsto
        (fun n => (fun ij : ι × ι =>
          φhat1Iter (subseq n) ij.1 * φhat1Iter ((subseq n).pred) ij.2 -
            φhat1Iter (subseq n) ij.2 * φhat1Iter ((subseq n).pred) ij.1) (i, j))
        Filter.atTop (nhds (0 : ℝ)) at hcoord
    simpa using hcoord
  have hcur_i : Filter.Tendsto (fun n => φhat1Iter (subseq n) i)
      Filter.atTop (nhds (ψhat1 i)) :=
    ((continuous_apply i).tendsto ψhat1).comp hpre.tendsto_φhat1
  have hcur_j : Filter.Tendsto (fun n => φhat1Iter (subseq n) j)
      Filter.atTop (nhds (ψhat1 j)) :=
    ((continuous_apply j).tendsto ψhat1).comp hpre.tendsto_φhat1
  have hpred_i : Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred) i)
      Filter.atTop (nhds (q i / ψ1 i)) :=
    ((continuous_apply i).tendsto (fun j => q j / ψ1 j)).comp hpred
  have hpred_j : Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred) j)
      Filter.atTop (nhds (q j / ψ1 j)) :=
    ((continuous_apply j).tendsto (fun j => q j / ψ1 j)).comp hpred
  have hlimit :
      Filter.Tendsto
        (fun n => φhat1Iter (subseq n) i * φhat1Iter ((subseq n).pred) j -
          φhat1Iter (subseq n) j * φhat1Iter ((subseq n).pred) i)
        Filter.atTop (nhds (ψhat1 i * (q j / ψ1 j) - ψhat1 j * (q i / ψ1 i))) := by
    exact (hcur_i.mul hpred_j).sub (hcur_j.mul hpred_i)
  exact tendsto_nhds_unique hlimit hlag_coord

/-- Pure finite scalar spine for right-normalization of the current phase.

This is the remaining non-topological algebraic core of C2-scale.  The quotient-projective identity
says `q / ψ1` is projectively parallel to `ψhat1`; successor normalization identifies the same
quotient using `ψ1Succ`; and the equal forward/gauge weighted totals should force the projective
scalar between `ψ1` and `ψ1Succ` to be one. -/
theorem finite_right_normalize_current_of_quotient_projective_gauge_sum {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (G : ι → ι → ℝ)
    (ψ0 ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hψ0_pos : ∀ i, 0 < ψ0 i)
    (hψ1_pos : ∀ j, 0 < ψ1 j)
    (_hψ1Succ_pos : ∀ j, 0 < ψ1Succ j)
    (hψhat1_pos : ∀ j, 0 < ψhat1 j)
    (hforward_current : ∀ i, ψ0 i = ∑ j, G i j * ψ1 j)
    (hweighted_totals : (∑ i, ∑ j, G i j * ψ1Succ j) =
      (∑ i, ∑ j, G i j * ψ1 j))
    (hright_successor : ∀ j, ψ1Succ j * ψhat1 j = q j)
    (hquot_projective : ∀ i j,
      ψhat1 i * (q j / ψ1 j) - ψhat1 j * (q i / ψ1 i) = 0) :
    ∀ j, ψ1 j * ψhat1 j = q j := by
  classical
  intro j
  let r : ℝ := ψ1Succ j / ψ1 j
  have hratio_const : ∀ k, ψ1Succ k / ψ1 k = r := by
    intro k
    have hψhat1j_ne : ψhat1 j ≠ 0 := ne_of_gt (hψhat1_pos j)
    have hψhat1k_ne : ψhat1 k ≠ 0 := ne_of_gt (hψhat1_pos k)
    have hproj := hquot_projective j k
    have hproj' :
        ψhat1 j * (ψ1Succ k * ψhat1 k / ψ1 k) -
          ψhat1 k * (ψ1Succ j * ψhat1 j / ψ1 j) = 0 := by
      rw [← hright_successor k, ← hright_successor j] at hproj
      simpa using hproj
    have hscaled :
        ψhat1 j * ψhat1 k * (ψ1Succ k / ψ1 k - ψ1Succ j / ψ1 j) = 0 := by
      calc
        ψhat1 j * ψhat1 k * (ψ1Succ k / ψ1 k - ψ1Succ j / ψ1 j)
            = ψhat1 j * (ψ1Succ k * ψhat1 k / ψ1 k) -
                ψhat1 k * (ψ1Succ j * ψhat1 j / ψ1 j) := by
              ring
        _ = 0 := hproj'
    have hprod_ne : ψhat1 j * ψhat1 k ≠ 0 := mul_ne_zero hψhat1j_ne hψhat1k_ne
    have hdiff_zero : ψ1Succ k / ψ1 k - ψ1Succ j / ψ1 j = 0 := by
      rcases mul_eq_zero.mp hscaled with hprod_zero | hdiff_zero
      · exact False.elim (hprod_ne hprod_zero)
      · exact hdiff_zero
    dsimp [r]
    exact sub_eq_zero.mp hdiff_zero
  have hsucc_eq_scaled : ∀ k, ψ1Succ k = r * ψ1 k := by
    intro k
    have hψ1k_ne : ψ1 k ≠ 0 := ne_of_gt (hψ1_pos k)
    calc
      ψ1Succ k = (ψ1Succ k / ψ1 k) * ψ1 k := by
        rw [div_mul_cancel₀ (ψ1Succ k) hψ1k_ne]
      _ = r * ψ1 k := by
        rw [hratio_const k]
  let T : ℝ := ∑ i, ∑ k, G i k * ψ1 k
  have hleft_scaled : (∑ i, ∑ k, G i k * ψ1Succ k) = r * T := by
    dsimp [T]
    calc
      (∑ i, ∑ k, G i k * ψ1Succ k)
          = ∑ i, ∑ k, G i k * (r * ψ1 k) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [hsucc_eq_scaled k]
      _ = ∑ i, ∑ k, r * (G i k * ψ1 k) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro k _hk
            ring
      _ = r * (∑ i, ∑ k, G i k * ψ1 k) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Finset.mul_sum]
  have hT_current : T = ∑ i, ψ0 i := by
    dsimp [T]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (hforward_current i).symm
  have hT_pos : 0 < T := by
    rw [hT_current]
    exact Finset.sum_pos (fun i _hi => hψ0_pos i) ⟨j, Finset.mem_univ j⟩
  have hscalar_eq : r * T = T := by
    rw [← hleft_scaled]
    exact hweighted_totals
  have hr_one : r = 1 := by
    have hT_ne : T ≠ 0 := ne_of_gt hT_pos
    have hscalar_eq' : r * T = 1 * T := by
      simpa using hscalar_eq
    exact mul_right_cancel₀ hT_ne hscalar_eq'
  have hsucc_eq_current : ψ1Succ j = ψ1 j := by
    have h := hsucc_eq_scaled j
    rw [hr_one] at h
    simpa using h
  rw [← hright_successor j, hsucc_eq_current]


/-- Assemble the finite scalar spine from the already-proved limit-passage helpers.

All topology has now been discharged before the final finite algebra call: projective lag has been
converted to quotient-projective alignment, the current forward equation has been passed to the
precluster, and the current/successor forward-gauge totals are known equal. -/
theorem sinkhorn_precluster_normalize_right_current_from_successor_projective_gauge_sum
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hcurrent_gauge_sum : (∑ i, ∑ j, G i j * ψ1 j) = ∑ i, φ0 i)
    (hsuccessor_gauge_sum : (∑ i, ∑ j, G i j * ψ1Succ j) = ∑ i, φ0 i)
    (hright_successor : ∀ j, ψ1Succ j * ψhat1 j = q j)
    (hprojective_hat1_lag : SinkhornPhaseProjectiveLagZeroAlong φhat1Iter subseq) :
    ∀ j, ψ1 j * ψhat1 j = q j := by
  have hforward_current : ∀ i, ψ0 i = ∑ j, G i j * ψ1 j :=
    sinkhorn_precluster_forward_current p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre
  have hweighted_totals : (∑ i, ∑ j, G i j * ψ1Succ j) =
      (∑ i, ∑ j, G i j * ψ1 j) := by
    rw [hsuccessor_gauge_sum, hcurrent_gauge_sum]
  have hquot_projective : ∀ i j,
      ψhat1 i * (q j / ψ1 j) - ψhat1 j * (q i / ψ1 i) = 0 :=
    sinkhorn_precluster_phihat1_quotient_projective_from_lag p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre hprojective_hat1_lag
  exact finite_right_normalize_current_of_quotient_projective_gauge_sum q G
    ψ0 ψ1 ψ1Succ ψhat1 hpre.positive.1 hpre.positive.2.2.2.1
    hpre.positive.2.2.2.2.1 hpre.positive.2.2.2.2.2
    hforward_current hweighted_totals hright_successor hquot_projective

/-- The remaining scalar-normalization seam for `φhat1`.

All direct limit passages have now been pushed into proved helpers: current forward equations,
current and successor gauge-weighted sums, and successor right normalization.  The only remaining
mathematical content is the finite scalar spine isolated in
`sinkhorn_precluster_normalize_right_current_from_successor_projective_gauge_sum`. -/
theorem sinkhorn_precluster_normalize_right_current_from_gauge_projective {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hproj : SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq) :
    ∀ j, ψ1 j * ψhat1 j = q j := by
  have hcurrent_gauge_sum : (∑ i, ∑ j, G i j * ψ1 j) = ∑ i, φ0 i :=
    sinkhorn_precluster_forward_current_gauge_sum p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hpre
  have hsuccessor_gauge_sum : (∑ i, ∑ j, G i j * ψ1Succ j) = ∑ i, φ0 i :=
    sinkhorn_precluster_forward_successor_gauge_sum p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hpre
  have hright_successor : ∀ j, ψ1Succ j * ψhat1 j = q j :=
    sinkhorn_precluster_normalize_right_successor p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre
  exact sinkhorn_precluster_normalize_right_current_from_successor_projective_gauge_sum
    p q G φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre
    hcurrent_gauge_sum hsuccessor_gauge_sum hright_successor hproj.2

/-- The real scalar-lag seam for the non-gauge-fixed denominator `φhat1`.

Along a raw precluster, `φhat1Iter (subseq n)` already has total limit `∑ j, ψhat1 j`.  What remains
is to show that the lagged predecessor totals have the same limit.  Mathematically this is where the
Sinkhorn update equations, the fixed left gauge, positive box bounds, and denominator projective lag
collapse determine the otherwise-free scalar. -/
theorem sinkhorn_phihat1_lagged_total_tendsto_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hproj : SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq) :
    Filter.Tendsto (fun n => ∑ j, φhat1Iter ((subseq n).pred) j)
      Filter.atTop (nhds (∑ j, ψhat1 j)) := by
  have hright_current : ∀ j, ψ1 j * ψhat1 j = q j :=
    sinkhorn_precluster_normalize_right_current_from_gauge_projective p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre hproj
  have hlagged :
      Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred)) Filter.atTop (nhds ψhat1) :=
    sinkhorn_phihat1_lagged_tendsto_from_current_right_normalization p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hpre hright_current
  exact sinkhorn_compactness_finite_sum_tendsto_of_function_tendsto
    (fun n => φhat1Iter ((subseq n).pred)) ψhat1 hlagged

/-- Scale/asymptotic-regularity core for the `φhat1` denominator phase.

The `φ0` scale drift is exactly zero by the gauge.  The remaining scale work is the total-mass drift
for `φhat1`; this should follow from the Sinkhorn equations, projective lag collapse, and the fixed
left gauge. -/
theorem sinkhorn_phihat1_scale_lag_tendsto_zero_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (_hproj : SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq) :
    SinkhornPhaseScaleLagZeroAlong φhat1Iter subseq := by
  change Filter.Tendsto
    (fun n => (∑ j, φhat1Iter (subseq n) j) - ∑ j, φhat1Iter ((subseq n).pred) j)
    Filter.atTop (nhds (0 : ℝ))
  have hcurrent :
      Filter.Tendsto (fun n => ∑ j, φhat1Iter (subseq n) j)
        Filter.atTop (nhds (∑ j, ψhat1 j)) :=
    sinkhorn_compactness_finite_sum_tendsto_of_function_tendsto
      (fun n => φhat1Iter (subseq n)) ψhat1 _hpre.tendsto_φhat1
  have hlagged :
      Filter.Tendsto (fun n => ∑ j, φhat1Iter ((subseq n).pred) j)
        Filter.atTop (nhds (∑ j, ψhat1 j)) :=
    sinkhorn_phihat1_lagged_total_tendsto_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 _hiter _hgauge _hbounds _hpre _hproj
  have hdiff := hcurrent.sub hlagged
  simpa [sub_self] using hdiff

/-- Projective/asymptotic-regularity plus scale control for the denominator phases.

This wrapper preserves the earlier projective-scale theorem name while exposing the two real
subproblems: projective shape collapse for both denominator phases, and scale control for the
non-gauge-fixed `φhat1` denominator.  The `φ0` scale component is discharged directly by the gauge. -/
theorem sinkhorn_denominator_projective_scale_lag_tendsto_zero_from_gauge_iterates {ι : Type*}
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
    SinkhornDenominatorProjectiveScaleLagZeroAlong φ0Iter φhat1Iter subseq := by
  have hproj : SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq :=
    sinkhorn_denominator_projective_lag_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hG hiter hgauge hbounds hpre
  have hφ0scale : SinkhornPhaseScaleLagZeroAlong φ0Iter subseq :=
    sinkhorn_phi0_scale_lag_zero_from_gauge
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq hgauge
  have hφhat1scale : SinkhornPhaseScaleLagZeroAlong φhat1Iter subseq :=
    sinkhorn_phihat1_scale_lag_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre hproj
  exact ⟨⟨hproj.1, hφ0scale⟩, ⟨hproj.2, hφhat1scale⟩⟩


end ChenGeorgiouPavon2021
