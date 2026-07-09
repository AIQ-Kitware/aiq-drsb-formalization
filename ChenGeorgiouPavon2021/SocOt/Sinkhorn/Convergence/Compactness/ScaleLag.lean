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
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (_hproj : SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq) :
    Filter.Tendsto (fun n => ∑ j, φhat1Iter ((subseq n).pred) j)
      Filter.atTop (nhds (∑ j, ψhat1 j)) := by
  sorry

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
