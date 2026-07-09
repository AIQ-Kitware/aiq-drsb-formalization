/-
# Finite positive-box conversion from projective/scale lag to coordinate lag

This file is intended to be mostly finite-dimensional algebra, independent of the Sinkhorn iterate
system except for the convenient denominator wrapper.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.Projective

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Local finite-sum continuity for finite lag algebra.

This duplicates the small finite-sum bridge used elsewhere without importing the downstream gauge
module, which would create a compactness/gauge import cycle. -/
private theorem finite_lag_sum_tendsto_of_function_tendsto {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (h : Filter.Tendsto x Filter.atTop (nhds xLim)) :
    Filter.Tendsto (fun n => ∑ i, x n i) Filter.atTop (nhds (∑ i, xLim i)) := by
  have hcont : Continuous (fun y : ι → ℝ => ∑ i, y i) := by
    fun_prop
  change Filter.Tendsto ((fun y : ι → ℝ => ∑ i, y i) ∘ x)
    Filter.atTop (nhds (∑ i, xLim i))
  exact (hcont.tendsto xLim).comp h

/-- Quantitative coordinate estimate behind the finite projective/scale lag conversion.

For two positive vectors `a = u (subseq n)` and `b = u ((subseq n).pred)`, the identity

`(∑ b) * (a i - b i) = ∑ j (a i * b j - a j * b i) + b i * ((∑ a) - ∑ b)`

shows that one coordinate lag is controlled by the projective cross-product residuals plus the
scale residual.  The uniform lower bound `ε` lets us divide by `∑ b`, and the upper bound `B`
controls the coefficient `b i`. -/
private theorem finite_phase_lag_coord_abs_bound_of_projective_scale {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ)
    {ε B : ℝ} (hε : 0 < ε)
    (hbox : ∀ n i, ε ≤ u n i ∧ u n i ≤ B)
    (n : ℕ) (i : ι) :
    |u (subseq n) i - u ((subseq n).pred) i| ≤
      ε⁻¹ *
        ((∑ j,
            |u (subseq n) i * u ((subseq n).pred) j -
              u (subseq n) j * u ((subseq n).pred) i|) +
          B * |(∑ j, u (subseq n) j) - ∑ j, u ((subseq n).pred) j|) := by
  classical
  let a : ι → ℝ := fun j => u (subseq n) j
  let b : ι → ℝ := fun j => u ((subseq n).pred) j
  let Sa : ℝ := ∑ j, a j
  let Sb : ℝ := ∑ j, b j
  let scale : ℝ := Sa - Sb
  let cross : ι → ℝ := fun j => a i * b j - a j * b i
  have hb_nonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ b j := by
    intro j _hj
    exact le_trans (le_of_lt hε) ((hbox ((subseq n).pred) j).1)
  have hb_i_le_sum : b i ≤ Sb := by
    change b i ≤ ∑ j, b j
    exact Finset.single_le_sum hb_nonneg (Finset.mem_univ i)
  have hSb_ge : ε ≤ Sb := by
    exact le_trans ((hbox ((subseq n).pred) i).1) hb_i_le_sum
  have hSb_pos : 0 < Sb := lt_of_lt_of_le hε hSb_ge
  have hb_i_abs_le_B : |b i| ≤ B := by
    have hb_i_nonneg : 0 ≤ b i := le_trans (le_of_lt hε) ((hbox ((subseq n).pred) i).1)
    have hb_i_le_B : b i ≤ B := (hbox ((subseq n).pred) i).2
    simpa [abs_of_nonneg hb_i_nonneg] using hb_i_le_B
  have hsum_cross :
      (∑ j, cross j) = a i * Sb - Sa * b i := by
    calc
      (∑ j, cross j)
          = (∑ j, a i * b j) - ∑ j, a j * b i := by
            simp only [cross]
            rw [Finset.sum_sub_distrib]
      _ = a i * Sb - Sa * b i := by
            rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hidentity :
      Sb * (a i - b i) = (∑ j, cross j) + b i * scale := by
    rw [hsum_cross]
    simp [scale]
    ring
  have htriangle :
      |(∑ j, cross j) + b i * scale| ≤ (∑ j, |cross j|) + B * |scale| := by
    calc
      |(∑ j, cross j) + b i * scale|
          ≤ |∑ j, cross j| + |b i * scale| := by
            simpa [Real.norm_eq_abs] using
              (norm_add_le (∑ j, cross j) (b i * scale))
      _ ≤ (∑ j, |cross j|) + B * |scale| := by
          apply add_le_add
          · simpa [Real.norm_eq_abs] using
              (norm_sum_le (s := (Finset.univ : Finset ι)) (f := cross))
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_right hb_i_abs_le_B (abs_nonneg scale)
  have hmul_bound : ε * |a i - b i| ≤ (∑ j, |cross j|) + B * |scale| := by
    calc
      ε * |a i - b i| ≤ Sb * |a i - b i| :=
        mul_le_mul_of_nonneg_right hSb_ge (abs_nonneg (a i - b i))
      _ = |Sb * (a i - b i)| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hSb_pos)]
      _ = |(∑ j, cross j) + b i * scale| := by rw [hidentity]
      _ ≤ (∑ j, |cross j|) + B * |scale| := htriangle
  have hdiv :
      |a i - b i| ≤ ((∑ j, |cross j|) + B * |scale|) / ε := by
    have hmul' : |a i - b i| * ε ≤ (∑ j, |cross j|) + B * |scale| := by
      simpa [mul_comm] using hmul_bound
    exact (le_div_iff₀ hε).2 hmul'
  simpa [a, b, Sa, Sb, scale, cross, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc]
    using hdiv

/-- One-phase finite positive-box conversion from projective-and-scale lag collapse to
coordinate lag drift.

This is the finite-dimensional algebra core: if two consecutive uniformly positive vectors have all
cross-products asymptotically flat and their totals asymptotically agree, then each coordinate
asymptotically agrees.  It is independent of the Sinkhorn equations. -/
theorem finite_phase_lag_drift_zero_of_projective_scale_lag {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ)
    (hbox : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ n i, ε ≤ u n i ∧ u n i ≤ B)
    (hprojscale : SinkhornPhaseProjectiveScaleLagZeroAlong u subseq) :
    Filter.Tendsto
      (fun n => fun i => u (subseq n) i - u ((subseq n).pred) i)
      Filter.atTop (nhds (0 : ι → ℝ)) := by
  classical
  rcases hbox with ⟨ε, B, hε, hB, hbox⟩
  rcases hprojscale with ⟨hproj, hscale⟩
  refine finite_function_tendsto_of_coordinate_tendsto
    (fun n => fun i => u (subseq n) i - u ((subseq n).pred) i) 0 ?_
  intro i
  let cross : ℕ → ι → ℝ := fun n j =>
    u (subseq n) i * u ((subseq n).pred) j -
      u (subseq n) j * u ((subseq n).pred) i
  let scale : ℕ → ℝ := fun n =>
    (∑ j, u (subseq n) j) - ∑ j, u ((subseq n).pred) j
  let bound : ℕ → ℝ := fun n =>
    ε⁻¹ * ((∑ j, |cross n j|) + B * |scale n|)
  have hcross_abs :
      Filter.Tendsto (fun n => fun j => |cross n j|) Filter.atTop
        (nhds (0 : ι → ℝ)) := by
    refine finite_function_tendsto_of_coordinate_tendsto
      (fun n => fun j => |cross n j|) 0 ?_
    intro j
    have hcross_coord :
        Filter.Tendsto (fun n => cross n j) Filter.atTop (nhds (0 : ℝ)) := by
      have hcoord := (tendsto_pi_nhds.mp hproj) (i, j)
      simpa [cross, Nat.pred_eq_sub_one] using hcoord
    simpa using hcross_coord.abs
  have hcross_sum_abs :
      Filter.Tendsto (fun n => ∑ j, |cross n j|) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using finite_lag_sum_tendsto_of_function_tendsto
      (fun n => fun j => |cross n j|) (0 : ι → ℝ) hcross_abs
  have hscale_abs :
      Filter.Tendsto (fun n => |scale n|) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [scale] using hscale.abs
  have hB_scale_abs :
      Filter.Tendsto (fun n => B * |scale n|) Filter.atTop (nhds (0 : ℝ)) := by
    have htmp := hscale_abs.const_mul B
    simpa using htmp
  have hinside :
      Filter.Tendsto (fun n => (∑ j, |cross n j|) + B * |scale n|)
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hcross_sum_abs.add hB_scale_abs
  have hbound_tendsto : Filter.Tendsto bound Filter.atTop (nhds (0 : ℝ)) := by
    have htmp := hinside.const_mul ε⁻¹
    simpa [bound] using htmp
  rw [Metric.tendsto_atTop]
  rw [Metric.tendsto_atTop] at hbound_tendsto
  intro δ hδ
  obtain ⟨N, hN⟩ := hbound_tendsto δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hle_abs : |u (subseq n) i - u ((subseq n).pred) i| ≤ bound n := by
    simpa [cross, scale, bound] using
      finite_phase_lag_coord_abs_bound_of_projective_scale u subseq hε hbox n i
  have hbound_nonneg : 0 ≤ bound n := by
    have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr (le_of_lt hε)
    have hsum_nonneg : 0 ≤ ∑ j, |cross n j| := by
      exact Finset.sum_nonneg (fun j _hj => abs_nonneg (cross n j))
    have hB_nonneg : 0 ≤ B := le_of_lt hB
    have hscale_nonneg : 0 ≤ B * |scale n| := mul_nonneg hB_nonneg (abs_nonneg (scale n))
    exact mul_nonneg hεinv_nonneg (add_nonneg hsum_nonneg hscale_nonneg)
  have hsmall : |bound n - 0| < δ := by
    simpa [Real.dist_eq] using hN n hn
  have hdiff_abs_lt : |(u (subseq n) i - u ((subseq n).pred) i) - 0| < δ := by
    have hbound_abs : |bound n - 0| = bound n := by
      simpa using abs_of_nonneg hbound_nonneg
    have hle' : |(u (subseq n) i - u ((subseq n).pred) i) - 0| ≤ |bound n - 0| := by
      rw [hbound_abs]
      simpa using hle_abs
    exact lt_of_le_of_lt hle' hsmall
  simpa [Real.dist_eq] using hdiff_abs_lt

/-- Finite positive-box conversion from projective-and-scale lag collapse to coordinate lag drift.

This Sinkhorn-denominator wrapper is now just two applications of the one-phase finite-dimensional
conversion above, one for `φ0` and one for `φhat1`. -/
theorem sinkhorn_denominator_lag_drift_zero_of_projective_scale_lag {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hprojscale : SinkhornDenominatorProjectiveScaleLagZeroAlong φ0Iter φhat1Iter subseq) :
    SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq := by
  rcases hbounds with ⟨ε, B, hε, hB, hφ0, _hφhat0, _hφ1, hφhat1⟩
  have hφ0box : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B :=
    ⟨ε, B, hε, hB, hφ0⟩
  have hφhat1box : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ n i, ε ≤ φhat1Iter n i ∧ φhat1Iter n i ≤ B :=
    ⟨ε, B, hε, hB, hφhat1⟩
  exact ⟨
    finite_phase_lag_drift_zero_of_projective_scale_lag φ0Iter subseq hφ0box hprojscale.1,
    finite_phase_lag_drift_zero_of_projective_scale_lag φhat1Iter subseq hφhat1box hprojscale.2⟩


end ChenGeorgiouPavon2021
