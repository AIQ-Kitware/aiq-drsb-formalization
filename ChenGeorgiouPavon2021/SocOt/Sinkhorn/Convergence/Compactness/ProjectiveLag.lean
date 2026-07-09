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

/-- Remaining C2-projective dynamical seam.

For each denominator phase, show that the absolute predecessor subsequence has a cluster limit which
is projectively aligned with the current raw-precluster limit.  This is the precise place where the
positive Sinkhorn dynamics should enter: either via Hilbert-projective contraction, monotone
projective diameter, or an equivalent oscillation/energy argument. -/
theorem sinkhorn_denominator_predecessor_projective_limits_from_gauge_iterates {ι : Type*}
    [Fintype ι]
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
    (∃ ψ0Pred : ι → ℝ,
      Filter.Tendsto (fun n => φ0Iter ((subseq n).pred)) Filter.atTop (nhds ψ0Pred) ∧
      ∀ i j, ψ0 i * ψ0Pred j - ψ0 j * ψ0Pred i = 0) ∧
    (∃ ψhat1Pred : ι → ℝ,
      Filter.Tendsto (fun n => φhat1Iter ((subseq n).pred)) Filter.atTop (nhds ψhat1Pred) ∧
      ∀ i j, ψhat1 i * ψhat1Pred j - ψhat1 j * ψhat1Pred i = 0) := by
  sorry


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
