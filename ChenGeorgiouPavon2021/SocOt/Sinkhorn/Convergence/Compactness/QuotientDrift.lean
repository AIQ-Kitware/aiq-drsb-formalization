/-
# Quotient-update transfer from denominator lag to mixed-phase drift

This file converts denominator-phase asymptotic regularity into the mixed phase drift needed for
successor-limit compatibility.  It is the boundary between the denominator lag fanout and the final
cluster assembly.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.FiniteLag

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- A scalar continuity estimate for reciprocals on a positive half-line.

If two denominator streams have vanishing difference and are eventually bounded below by a fixed
positive number, then their fixed numerators divided by those denominators also have vanishing
difference.  This is the analytic core of the quotient-update transfer below. -/
theorem tendsto_const_div_sub_const_div_of_sub_tendsto_zero_of_eventually_lower
    (c : ℝ) (a b : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε)
    (ha : ∀ n, ε ≤ a n)
    (hb : ∀ n, ε ≤ b n)
    (hdiff : Filter.Tendsto (fun n => a n - b n) Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto (fun n => c / a n - c / b n) Filter.atTop (nhds (0 : ℝ)) := by
  rw [Metric.tendsto_atTop] at hdiff ⊢
  intro η hη
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith [abs_nonneg c]
  have hC_nonneg : 0 ≤ C := le_of_lt hCpos
  have hc_le_C : |c| ≤ C := by
    dsimp [C]
    nlinarith
  have hεsq_pos : 0 < ε * ε := mul_pos hε hε
  let δ : ℝ := η * (ε * ε) / C
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos (mul_pos hη hεsq_pos) hCpos
  obtain ⟨Ndiff, hNdiff⟩ := hdiff δ hδpos
  refine ⟨Ndiff, ?_⟩
  intro n hn_diff
  have ha_lower : ε ≤ a n := ha n
  have hb_lower : ε ≤ b n := hb n
  have ha_pos : 0 < a n := lt_of_lt_of_le hε ha_lower
  have hb_pos : 0 < b n := lt_of_lt_of_le hε hb_lower
  have ha_ne : a n ≠ 0 := ne_of_gt ha_pos
  have hb_ne : b n ≠ 0 := ne_of_gt hb_pos
  have hdiff_abs : |a n - b n| < δ := by
    simpa [Real.dist_eq] using hNdiff n hn_diff
  have hquot_eq : c / a n - c / b n = -(c * (a n - b n)) / (a n * b n) := by
    field_simp [ha_ne, hb_ne]
    ring
  have hden_lower : ε * ε ≤ |a n * b n| := by
    have hmul_lower : ε * ε ≤ a n * b n := by
      exact mul_le_mul ha_lower hb_lower (le_of_lt hε) (le_of_lt ha_pos)
    have hmul_pos : 0 < a n * b n := mul_pos ha_pos hb_pos
    simpa [abs_of_pos hmul_pos] using hmul_lower
  have hnum_bound : |c * (a n - b n)| ≤ C * |a n - b n| := by
    rw [abs_mul]
    exact mul_le_mul hc_le_C le_rfl (abs_nonneg _) hC_nonneg
  have hmain_bound : |c / a n - c / b n| ≤ C * |a n - b n| / (ε * ε) := by
    rw [hquot_eq, abs_div, abs_neg]
    have hden_pos_abs : 0 < |a n * b n| := abs_pos.mpr (mul_ne_zero ha_ne hb_ne)
    have hnonneg_num : 0 ≤ |c * (a n - b n)| := abs_nonneg _
    have hden_mono : |c * (a n - b n)| / |a n * b n| ≤
        |c * (a n - b n)| / (ε * ε) := by
      exact div_le_div_of_nonneg_left hnonneg_num hεsq_pos hden_lower
    have hnum_mono : |c * (a n - b n)| / (ε * ε) ≤
        (C * |a n - b n|) / (ε * ε) := by
      exact div_le_div_of_nonneg_right hnum_bound (le_of_lt hεsq_pos)
    exact le_trans hden_mono hnum_mono
  have hscaled_small : C * |a n - b n| / (ε * ε) < η := by
    have hCδ : C * δ = η * (ε * ε) := by
      dsimp [δ]
      field_simp [ne_of_gt hCpos]
    have hnum_small : C * |a n - b n| < η * (ε * ε) := by
      calc
        C * |a n - b n| < C * δ := mul_lt_mul_of_pos_left hdiff_abs hCpos
        _ = η * (ε * ε) := hCδ
    exact (div_lt_iff₀ hεsq_pos).2 hnum_small
  have habs_small : |c / a n - c / b n| < η := lt_of_le_of_lt hmain_bound hscaled_small
  simpa [Real.dist_eq] using habs_small

/-- Denominator lag drift follows from the projective/scale collapse plus finite positive-box
conversion.  This wrapper preserves the earlier public C2 seam while exposing the two real subproblems
above. -/
theorem sinkhorn_denominator_lag_drift_tendsto_zero_from_gauge_iterates {ι : Type*} [Fintype ι]
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
    SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq := by
  have hprojscale : SinkhornDenominatorProjectiveScaleLagZeroAlong φ0Iter φhat1Iter subseq :=
    sinkhorn_denominator_projective_scale_lag_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_denominator_lag_drift_zero_of_projective_scale_lag
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hbounds hprojscale

/-- Quotient-update algebra converting denominator lag drift into mixed-phase drift.

Once the denominator phases have vanishing lag drift and remain in a uniform positive finite box,
normalization equations
`φhat0Iter (n + 1) * φ0Iter n = p` and
`φ1Iter (n + 1) * φhat1Iter n = q` convert denominator lag drift into drift of the quotient-updated
mixed phases.  The subsequence must be eventually positive/cofinal so that the lagged normalization
at `(subseq n).pred` rewrites the current mixed phase at `subseq n`. -/
theorem sinkhorn_phase_drift_zero_of_denominator_lag_drift {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hdenom : SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq) :
    SinkhornPhaseDriftZeroAlong φhat0Iter φ1Iter subseq := by
  classical
  rcases hbounds with ⟨ε, _B, hε, _hB, hφ0, _hφhat0, _hφ1, hφhat1⟩
  have hsubseq_pos_event : ∀ᶠ n in Filter.atTop, 0 < subseq n := by
    have hgt0 : ∀ᶠ m : ℕ in Filter.atTop, 0 < m := by
      exact Filter.mem_atTop_sets.mpr ⟨1, fun m hm => hm⟩
    exact hsubseq.tendsto_atTop.eventually hgt0
  refine ⟨?_, ?_⟩
  · refine finite_function_tendsto_of_coordinate_tendsto
      (fun n => fun i => φhat0Iter (subseq n + 1) i - φhat0Iter (subseq n) i)
      (0 : ι → ℝ) ?_
    intro i
    have hdenom_i : Filter.Tendsto
        (fun n => φ0Iter (subseq n) i - φ0Iter ((subseq n).pred) i)
        Filter.atTop (nhds (0 : ℝ)) := by
      have hcoord := ((continuous_apply i).tendsto (0 : ι → ℝ)).comp hdenom.1
      simpa [Function.comp_def] using hcoord
    have ha_lower : ∀ n, ε ≤ φ0Iter (subseq n) i :=
      fun n => (hφ0 (subseq n) i).1
    have hb_lower : ∀ n, ε ≤ φ0Iter ((subseq n).pred) i :=
      fun n => (hφ0 ((subseq n).pred) i).1
    have hquot_tend : Filter.Tendsto
        (fun n => p i / φ0Iter (subseq n) i - p i / φ0Iter ((subseq n).pred) i)
        Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_const_div_sub_const_div_of_sub_tendsto_zero_of_eventually_lower
        (p i) (fun n => φ0Iter (subseq n) i)
        (fun n => φ0Iter ((subseq n).pred) i) ε hε ha_lower hb_lower hdenom_i
    have hquot_eq :
        (fun n => φhat0Iter (subseq n + 1) i - φhat0Iter (subseq n) i) =ᶠ[Filter.atTop]
          (fun n => p i / φ0Iter (subseq n) i -
            p i / φ0Iter ((subseq n).pred) i) := by
      filter_upwards [hsubseq_pos_event] with n hn
      have ha_ne : φ0Iter (subseq n) i ≠ 0 := ne_of_gt (hiter.φ0_pos (subseq n) i)
      have hb_ne : φ0Iter ((subseq n).pred) i ≠ 0 :=
        ne_of_gt (hiter.φ0_pos ((subseq n).pred) i)
      have hpred_succ : (subseq n).pred + 1 = subseq n := Nat.succ_pred_eq_of_pos hn
      have hsucc_eq : φhat0Iter (subseq n + 1) i = p i / φ0Iter (subseq n) i := by
        have hnorm := hiter.normalize_left (subseq n) i
        field_simp [ha_ne] at hnorm ⊢
        exact hnorm
      have hcurr_eq : φhat0Iter (subseq n) i = p i / φ0Iter ((subseq n).pred) i := by
        have hnorm := hiter.normalize_left ((subseq n).pred) i
        rw [hpred_succ] at hnorm
        field_simp [hb_ne] at hnorm ⊢
        exact hnorm
      rw [hsucc_eq, hcurr_eq]
    exact hquot_tend.congr' hquot_eq.symm
  · refine finite_function_tendsto_of_coordinate_tendsto
      (fun n => fun j => φ1Iter (subseq n + 1) j - φ1Iter (subseq n) j)
      (0 : ι → ℝ) ?_
    intro j
    have hdenom_j : Filter.Tendsto
        (fun n => φhat1Iter (subseq n) j - φhat1Iter ((subseq n).pred) j)
        Filter.atTop (nhds (0 : ℝ)) := by
      have hcoord := ((continuous_apply j).tendsto (0 : ι → ℝ)).comp hdenom.2
      simpa [Function.comp_def] using hcoord
    have ha_lower : ∀ n, ε ≤ φhat1Iter (subseq n) j :=
      fun n => (hφhat1 (subseq n) j).1
    have hb_lower : ∀ n, ε ≤ φhat1Iter ((subseq n).pred) j :=
      fun n => (hφhat1 ((subseq n).pred) j).1
    have hquot_tend : Filter.Tendsto
        (fun n => q j / φhat1Iter (subseq n) j - q j / φhat1Iter ((subseq n).pred) j)
        Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_const_div_sub_const_div_of_sub_tendsto_zero_of_eventually_lower
        (q j) (fun n => φhat1Iter (subseq n) j)
        (fun n => φhat1Iter ((subseq n).pred) j) ε hε ha_lower hb_lower hdenom_j
    have hquot_eq :
        (fun n => φ1Iter (subseq n + 1) j - φ1Iter (subseq n) j) =ᶠ[Filter.atTop]
          (fun n => q j / φhat1Iter (subseq n) j -
            q j / φhat1Iter ((subseq n).pred) j) := by
      filter_upwards [hsubseq_pos_event] with n hn
      have ha_ne : φhat1Iter (subseq n) j ≠ 0 := ne_of_gt (hiter.φhat1_pos (subseq n) j)
      have hb_ne : φhat1Iter ((subseq n).pred) j ≠ 0 :=
        ne_of_gt (hiter.φhat1_pos ((subseq n).pred) j)
      have hpred_succ : (subseq n).pred + 1 = subseq n := Nat.succ_pred_eq_of_pos hn
      have hsucc_eq : φ1Iter (subseq n + 1) j = q j / φhat1Iter (subseq n) j := by
        have hnorm := hiter.normalize_right (subseq n) j
        field_simp [ha_ne] at hnorm ⊢
        exact hnorm
      have hcurr_eq : φ1Iter (subseq n) j = q j / φhat1Iter ((subseq n).pred) j := by
        have hnorm := hiter.normalize_right ((subseq n).pred) j
        rw [hpred_succ] at hnorm
        field_simp [hb_ne] at hnorm ⊢
        exact hnorm
      rw [hsucc_eq, hcurr_eq]
    exact hquot_tend.congr' hquot_eq.symm

/-- Asymptotic-regularity seam for the two mixed phases.

The hard content is factored through two lower-level surfaces: first prove vanishing lag drift for
the denominator phases from the positive Sinkhorn dynamics and gauge, then use the normalization
quotient equations and the uniform finite box to transfer that drift to the mixed phases. -/
theorem sinkhorn_phase_drift_tendsto_zero_from_gauge_iterates {ι : Type*} [Fintype ι]
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
    SinkhornPhaseDriftZeroAlong φhat0Iter φ1Iter subseq := by
  have hdenom : SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq :=
    sinkhorn_denominator_lag_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_phase_drift_zero_of_denominator_lag_drift p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hpre.strict_mono hiter hbounds hdenom


end ChenGeorgiouPavon2021
