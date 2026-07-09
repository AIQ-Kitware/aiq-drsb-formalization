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
mixed phases.  This seam should be mostly finite-dimensional algebra and continuity of inversion on
`[ε, B]`. -/
theorem sinkhorn_phase_drift_zero_of_denominator_lag_drift {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hdenom : SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq) :
    SinkhornPhaseDriftZeroAlong φhat0Iter φ1Iter subseq := by
  sorry

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
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hiter hbounds hdenom


end ChenGeorgiouPavon2021
