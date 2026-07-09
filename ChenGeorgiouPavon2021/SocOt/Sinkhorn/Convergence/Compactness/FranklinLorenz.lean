/-
# Franklin--Lorenz finite matrix-scaling contraction seams

This file owns the paper-level Birkhoff--Hopf / Franklin--Lorenz Section 3 contraction input needed
by the finite Sinkhorn compactness proof.  It is intentionally separate from `ProjectiveLag.lean` so
future agents can work on the contraction port without touching the downstream compactness assembly.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf
import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.MatrixBridge

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Right-side Franklin--Lorenz core under a chosen Birkhoff contraction coefficient.

This is the hard column-normalization port.  Starting from a strict Hilbert-projective contraction
coefficient `γ` for the positive kernel, Franklin--Lorenz Section 3 should give a finite constant
`C` such that the column diagonal correction increments satisfy the geometric spread bound below.

Suggested proof route for the next agent:
1. identify the implicit column-normalized matrices
   `sinkhornColumnNormalizedMatrix G (φhat0Iter (k + 1)) (φ1Iter (k + 2))`;
2. express `φ1Iter (k + 1) / φ1Iter k` as the column correction between successive IPF steps;
3. apply Birkhoff--Hopf contraction to the positive kernel acting on the opposite marginal error;
4. use the finite box bounds to translate Hilbert/projective distance into
   `finiteForwardRatioSpread φ1Iter k`. -/
theorem sinkhorn_phi1_forward_ratio_spread_geometric_bound_of_birkhoff_coefficient
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (γ : ℝ) (_hγ_nonneg : 0 ≤ γ) (_hγ_lt_one : γ < 1) :
    ∃ C : ℝ,
      0 ≤ C ∧ ∀ k, finiteForwardRatioSpread φ1Iter k ≤ C * γ ^ k := by
  sorry

/-- Left-side Franklin--Lorenz core under a chosen Birkhoff contraction coefficient.

This is the row-normalization analogue of
`sinkhorn_phi1_forward_ratio_spread_geometric_bound_of_birkhoff_coefficient`.  It should share most
of the final proof with the right-side theorem after abstracting the row/column orientation. -/
theorem sinkhorn_phihat0_forward_ratio_spread_geometric_bound_of_birkhoff_coefficient
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (γ : ℝ) (_hγ_nonneg : 0 ≤ γ) (_hγ_lt_one : γ < 1) :
    ∃ C : ℝ,
      0 ≤ C ∧ ∀ k, finiteForwardRatioSpread φhat0Iter k ≤ C * γ ^ k := by
  sorry

/-- Harder/right-side Franklin--Lorenz core: geometric decay of the column-correction spread.

The paper-agnostic strict contraction coefficient is supplied by the Mathlib-staging
Birkhoff--Hopf seam, and the Sinkhorn-specific work is isolated in
`sinkhorn_phi1_forward_ratio_spread_geometric_bound_of_birkhoff_coefficient`. -/
theorem sinkhorn_phi1_forward_ratio_spread_geometric_bound_from_franklin_lorenz
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ C γ : ℝ,
      0 ≤ C ∧ 0 ≤ γ ∧ γ < 1 ∧
        ∀ k, finiteForwardRatioSpread φ1Iter k ≤ C * γ ^ k := by
  obtain ⟨γ, hγ_nonneg, hγ_lt_one⟩ :=
    ForMathlib.Matrix.positive_kernel_birkhoff_contraction_coefficient G hG
  obtain ⟨C, hC_nonneg, hbound⟩ :=
    sinkhorn_phi1_forward_ratio_spread_geometric_bound_of_birkhoff_coefficient
      p q G φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hG hiter hgauge hbounds γ hγ_nonneg hγ_lt_one
  exact ⟨C, γ, hC_nonneg, hγ_nonneg, hγ_lt_one, hbound⟩

/-- Left-side Franklin--Lorenz core: geometric decay of the row-correction spread. -/
theorem sinkhorn_phihat0_forward_ratio_spread_geometric_bound_from_franklin_lorenz
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ C γ : ℝ,
      0 ≤ C ∧ 0 ≤ γ ∧ γ < 1 ∧
        ∀ k, finiteForwardRatioSpread φhat0Iter k ≤ C * γ ^ k := by
  obtain ⟨γ, hγ_nonneg, hγ_lt_one⟩ :=
    ForMathlib.Matrix.positive_kernel_birkhoff_contraction_coefficient G hG
  obtain ⟨C, hC_nonneg, hbound⟩ :=
    sinkhorn_phihat0_forward_ratio_spread_geometric_bound_of_birkhoff_coefficient
      p q G φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hG hiter hgauge hbounds γ hγ_nonneg hγ_lt_one
  exact ⟨C, γ, hC_nonneg, hγ_nonneg, hγ_lt_one, hbound⟩

end ChenGeorgiouPavon2021
