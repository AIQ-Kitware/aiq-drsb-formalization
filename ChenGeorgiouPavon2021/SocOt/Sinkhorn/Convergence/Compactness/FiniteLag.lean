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

/-- One-phase finite positive-box conversion from projective-and-scale lag collapse to
coordinate lag drift.

This is the finite-dimensional algebra core: if two consecutive uniformly positive vectors have all
cross-products asymptotically flat and their totals asymptotically agree, then each coordinate
asymptotically agrees.  It is independent of the Sinkhorn equations. -/
theorem finite_phase_lag_drift_zero_of_projective_scale_lag {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ)
    (_hbox : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ n i, ε ≤ u n i ∧ u n i ≤ B)
    (_hprojscale : SinkhornPhaseProjectiveScaleLagZeroAlong u subseq) :
    Filter.Tendsto
      (fun n => fun i => u (subseq n) i - u ((subseq n).pred) i)
      Filter.atTop (nhds (0 : ι → ℝ)) := by
  sorry

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
