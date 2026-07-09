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
  apply finite_function_tendsto_of_coordinate_tendsto
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

/-- The remaining scalar-normalization seam for `φhat1`.

Projective lag makes `φhat1Iter (subseq n)` and `φhat1Iter ((subseq n).pred)` asymptotically
parallel.  The only remaining non-gauge-fixed scalar is equivalently the current right-normalization
identity `ψ1 j * ψhat1 j = q j`; once this identity is known, lagged total-mass convergence follows
by `sinkhorn_phihat1_lagged_tendsto_from_current_right_normalization`. -/
theorem sinkhorn_precluster_normalize_right_current_from_gauge_projective {ι : Type*} [Fintype ι]
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
    ∀ j, ψ1 j * ψhat1 j = q j := by
  sorry

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
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  have hφ0scale : SinkhornPhaseScaleLagZeroAlong φ0Iter subseq :=
    sinkhorn_phi0_scale_lag_zero_from_gauge
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq hgauge
  have hφhat1scale : SinkhornPhaseScaleLagZeroAlong φhat1Iter subseq :=
    sinkhorn_phihat1_scale_lag_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre hproj
  exact ⟨⟨hproj.1, hφ0scale⟩, ⟨hproj.2, hφhat1scale⟩⟩


end ChenGeorgiouPavon2021
