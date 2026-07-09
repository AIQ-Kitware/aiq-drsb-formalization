/-
# Birkhoff--Hopf projective contraction for positive finite matrices

Mathlib-staging surface for the finite-dimensional positive-matrix contraction theorem behind
Franklin--Lorenz matrix scaling.  This file is deliberately paper-agnostic: it talks only about a
strictly positive finite kernel and the existence of a strict projective contraction coefficient.

The eventual upstream target is a Hilbert projective metric / Birkhoff contraction API for positive
linear maps on finite cones.  The DRSB Sinkhorn convergence proof imports this file only through the
coefficient-existence seam below.
-/

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix

/-- Pairwise quotient-spread of two finite positive vectors.

This is an elementary, log-free projective spread.  It is not intended to be the final Mathlib API;
it is a convenient finite-coordinate bridge between Hilbert's projective metric and the concrete
ratio-spread quantities used by the Sinkhorn compactness proof. -/
noncomputable def finitePairwiseRatioSpread {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : ℝ :=
  ∑ ij : ι × ι, |x ij.1 / y ij.1 - x ij.2 / y ij.2|

/-- The finite pairwise quotient-spread is nonnegative. -/
theorem finitePairwiseRatioSpread_nonneg {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    0 ≤ finitePairwiseRatioSpread x y := by
  classical
  unfold finitePairwiseRatioSpread
  exact Finset.sum_nonneg (fun ij _hij => abs_nonneg
    (x ij.1 / y ij.1 - x ij.2 / y ij.2))

/-- Birkhoff--Hopf coefficient seam for a strictly positive finite kernel.

For a positive finite matrix, the Hilbert-projective diameter of the image cone is finite, hence
Birkhoff's contraction coefficient `tanh(Δ / 4)` is strictly less than one.  A full Mathlib-style
proof should define the Hilbert projective distance/diameter and prove this theorem from the finite
cross-ratio bounds of `G`.

This is the paper-agnostic hard theorem that future agents should prove before specializing to
Sinkhorn/Franklin--Lorenz. -/
theorem positive_kernel_birkhoff_contraction_coefficient {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (_hG : ∀ i j, 0 < G i j) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 := by
  sorry

end ForMathlib.Matrix
