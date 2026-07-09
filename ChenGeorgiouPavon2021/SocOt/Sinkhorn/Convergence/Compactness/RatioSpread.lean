/-
# Finite ratio-spread utilities for Sinkhorn compactness

This file contains the projective ratio-spread quantities and generic order/topology lemmas shared
by the compactness/projective-lag proof.  It is Sinkhorn-light: the definitions are finite-vector
bookkeeping, while the actual Franklin--Lorenz/Birkhoff contraction lives in a separate file.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Finite scalar spread of the backward ratio vector `u (k.pred) / u k`.

This is a concrete progress metric for projective lag: it is zero exactly when all backward
coordinate ratios agree, and it bounds every coordinatewise ratio displacement. -/
noncomputable def finiteBackwardRatioSpread {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (k : ℕ) : ℝ :=
  ∑ ij : ι × ι,
    |u k.pred ij.1 / u k ij.1 - u k.pred ij.2 / u k ij.2|

/-- Finite scalar spread of the successor/current ratio vector `u (k + 1) / u k`.

This is the matrix-scaling diagonal-correction quantity that Franklin--Lorenz control directly:
for the implicit row-normalization cycle it is the spread of the left row correction
`φhat0Iter (k+1) / φhat0Iter k`, and for the implicit column-normalization cycle it is the
spread of the right column correction `φ1Iter (k+1) / φ1Iter k`. -/
noncomputable def finiteForwardRatioSpread {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (k : ℕ) : ℝ :=
  ∑ ij : ι × ι,
    |u (k + 1) ij.1 / u k ij.1 - u (k + 1) ij.2 / u k ij.2|

/-- The finite forward-ratio spread is nonnegative. -/
theorem finiteForwardRatioSpread_nonneg {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (k : ℕ) :
    0 ≤ finiteForwardRatioSpread u k := by
  classical
  unfold finiteForwardRatioSpread
  exact Finset.sum_nonneg (fun ij _hij => abs_nonneg
    (u (k + 1) ij.1 / u k ij.1 - u (k + 1) ij.2 / u k ij.2))

/-- A vanishing finite forward-ratio spread is itself a valid nonnegative envelope. -/
theorem finiteForwardRatioSpread_vanishing_envelope_of_tendsto_zero {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ)
    (hspread : Filter.Tendsto (fun k => finiteForwardRatioSpread u k)
      Filter.atTop (nhds (0 : ℝ))) :
    ∃ envelope : ℕ → ℝ,
      Filter.Tendsto envelope Filter.atTop (nhds (0 : ℝ)) ∧
        (∀ k, 0 ≤ envelope k) ∧
          ∀ k, finiteForwardRatioSpread u k ≤ envelope k := by
  refine ⟨fun k => finiteForwardRatioSpread u k, hspread, ?_, ?_⟩
  · intro k
    exact finiteForwardRatioSpread_nonneg u k
  · intro k
    exact le_rfl

/-- A nonnegative scalar sequence bounded by a vanishing nonnegative envelope tends to zero.

This is the pure real-analysis tail of the Franklin--Lorenz port.  The paper-level
Franklin--Lorenz seams are responsible for producing the actual geometric envelope; this lemma only
performs the order/topology squeeze once such an envelope is available. -/
theorem tendsto_nonnegative_atTop_zero_of_vanishing_envelope
    (s envelope : ℕ → ℝ)
    (henvelope : Filter.Tendsto envelope Filter.atTop (nhds (0 : ℝ)))
    (hs_nonneg : ∀ k, 0 ≤ s k)
    (henvelope_nonneg : ∀ k, 0 ≤ envelope k)
    (hbound : ∀ k, s k ≤ envelope k) :
    Filter.Tendsto s Filter.atTop (nhds (0 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  rw [Metric.tendsto_atTop] at henvelope
  obtain ⟨N, hN⟩ := henvelope δ hδ
  refine ⟨N, fun k hk => ?_⟩
  have henvelope_dist_eq : dist (envelope k) (0 : ℝ) = envelope k := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (henvelope_nonneg k)]
  have henvelope_small : envelope k < δ := by
    simpa [henvelope_dist_eq] using hN k hk
  have hs_small : s k < δ := lt_of_le_of_lt (hbound k) henvelope_small
  have hs_dist_eq : dist (s k) (0 : ℝ) = s k := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hs_nonneg k)]
  simpa [hs_dist_eq] using hs_small

/-- A nonnegative scalar sequence bounded by a strict geometric majorant tends to zero.

The Franklin--Lorenz/Birkhoff--Hopf proof should produce a bound of the form
`s k ≤ C * γ ^ k` with `0 ≤ γ < 1`; this lemma performs the last order/topology step. -/
theorem tendsto_nonnegative_atTop_zero_of_geometric_bound
    (s : ℕ → ℝ) (C γ : ℝ)
    (hs_nonneg : ∀ k, 0 ≤ s k)
    (hC_nonneg : 0 ≤ C)
    (hγ_nonneg : 0 ≤ γ)
    (hγ_lt_one : γ < 1)
    (hbound : ∀ k, s k ≤ C * γ ^ k) :
    Filter.Tendsto s Filter.atTop (nhds (0 : ℝ)) := by
  have hpow : Filter.Tendsto (fun k : ℕ => γ ^ k) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hγ_nonneg hγ_lt_one
  have hconst : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  have henvelope : Filter.Tendsto (fun k : ℕ => C * γ ^ k) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [mul_zero] using hconst.mul hpow
  exact tendsto_nonnegative_atTop_zero_of_vanishing_envelope
    s (fun k : ℕ => C * γ ^ k) henvelope hs_nonneg
    (fun k => mul_nonneg hC_nonneg (pow_nonneg hγ_nonneg k)) hbound

end ChenGeorgiouPavon2021
