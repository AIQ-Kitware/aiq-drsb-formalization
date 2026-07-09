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

/-- Apply a finite kernel to a vector.  This is the finite-coordinate positive linear map used in
Birkhoff--Hopf. -/
noncomputable def positiveKernelApply {ι κ : Type*} [Fintype κ]
    (G : ι → κ → ℝ) (x : κ → ℝ) : ι → ℝ :=
  fun i => ∑ j : κ, G i j * x j

/-- Log-Hilbert projective spread, expressed as the supremum of coordinate cross-ratio logs.

This is the Mathlib-style metric target for the eventual Birkhoff--Hopf theorem.  Downstream DRSB
files currently use the log-free `finitePairwiseRatioSpread`; the Franklin--Lorenz bridge should
transport between this Hilbert spread and the concrete finite ratio-spread under the existing box
bounds. -/
noncomputable def finiteHilbertProjectiveLogSpread {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : ℝ :=
  sSup (Set.range (fun ij : ι × ι =>
    Real.log ((x ij.1 * y ij.2) / (x ij.2 * y ij.1))))

/-- The elementary cross-ratio of four entries of a positive finite kernel.

For a strictly positive kernel, the supremum of these quantities controls the projective diameter
of the image of the positive cone. -/
noncomputable def positiveKernelCrossRatio {ι κ : Type*}
    (G : ι → κ → ℝ) (i i' : ι) (j j' : κ) : ℝ :=
  (G i j * G i' j') / (G i j' * G i' j)

/-- Positivity of a positive-kernel cross-ratio. -/
theorem positiveKernelCrossRatio_pos {ι κ : Type*}
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j)
    (i i' : ι) (j j' : κ) :
    0 < positiveKernelCrossRatio G i i' j j' := by
  unfold positiveKernelCrossRatio
  exact div_pos (mul_pos (hG i j) (hG i' j')) (mul_pos (hG i j') (hG i' j))

/-- Nonnegativity of a positive-kernel cross-ratio. -/
theorem positiveKernelCrossRatio_nonneg {ι κ : Type*}
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j)
    (i i' : ι) (j j' : κ) :
    0 ≤ positiveKernelCrossRatio G i i' j j' :=
  le_of_lt (positiveKernelCrossRatio_pos G hG i i' j j')

/-- A finite, explicit cross-ratio bound for a positive finite kernel.

This uses a finite sum instead of a maximum.  It is less sharp than the standard projective diameter
but easier to stage: every individual cross-ratio is bounded by this finite quantity, and the
resulting coefficient is still strictly below one. -/
noncomputable def positiveKernelCrossRatioBound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) : ℝ :=
  1 + ∑ q : (ι × ι) × (κ × κ),
    positiveKernelCrossRatio G q.1.1 q.1.2 q.2.1 q.2.2

/-- The explicit finite cross-ratio bound is at least one for a positive kernel. -/
theorem positiveKernelCrossRatioBound_one_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    1 ≤ positiveKernelCrossRatioBound G := by
  classical
  unfold positiveKernelCrossRatioBound
  have hsum_nonneg :
      0 ≤ ∑ q : (ι × ι) × (κ × κ),
        positiveKernelCrossRatio G q.1.1 q.1.2 q.2.1 q.2.2 := by
    exact Finset.sum_nonneg (fun q _hq =>
      positiveKernelCrossRatio_nonneg G hG q.1.1 q.1.2 q.2.1 q.2.2)
  linarith

/-- Every coordinate cross-ratio is bounded by the explicit finite cross-ratio bound. -/
theorem positiveKernelCrossRatio_le_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j)
    (i i' : ι) (j j' : κ) :
    positiveKernelCrossRatio G i i' j j' ≤ positiveKernelCrossRatioBound G := by
  classical
  have hterm_nonneg : ∀ q : (ι × ι) × (κ × κ),
      0 ≤ positiveKernelCrossRatio G q.1.1 q.1.2 q.2.1 q.2.2 := by
    intro q
    exact positiveKernelCrossRatio_nonneg G hG q.1.1 q.1.2 q.2.1 q.2.2
  have hsingle :
      positiveKernelCrossRatio G i i' j j' ≤
        ∑ q : (ι × ι) × (κ × κ),
          positiveKernelCrossRatio G q.1.1 q.1.2 q.2.1 q.2.2 := by
    simpa using
      (Finset.single_le_sum
        (fun q _hq => hterm_nonneg q)
        (Finset.mem_univ ((i, i'), (j, j'))))
  unfold positiveKernelCrossRatioBound
  linarith

/-- A concrete strict coefficient obtained from the finite cross-ratio bound.

For a sharp Birkhoff--Hopf development this would usually be written as `tanh (Δ / 4)`, or in
log-free form using the square root of the image-cone cross-ratio diameter.  The present coefficient
uses a coarser finite bound, which is enough to supply a strict number below one. -/
noncomputable def positiveKernelBirkhoffCoefficient {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) : ℝ :=
  (positiveKernelCrossRatioBound G - 1) / positiveKernelCrossRatioBound G

/-- The explicit finite Birkhoff coefficient lies in `[0, 1)`. -/
theorem positiveKernelBirkhoffCoefficient_nonneg_lt_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    0 ≤ positiveKernelBirkhoffCoefficient G ∧ positiveKernelBirkhoffCoefficient G < 1 := by
  classical
  have hB_ge_one : 1 ≤ positiveKernelCrossRatioBound G :=
    positiveKernelCrossRatioBound_one_le G hG
  have hB_pos : 0 < positiveKernelCrossRatioBound G := lt_of_lt_of_le zero_lt_one hB_ge_one
  constructor
  · unfold positiveKernelBirkhoffCoefficient
    exact div_nonneg (sub_nonneg.mpr hB_ge_one) (le_of_lt hB_pos)
  · unfold positiveKernelBirkhoffCoefficient
    exact (div_lt_iff₀ hB_pos).2 (by linarith)

/-- Predicate saying that `γ` contracts Hilbert projective spread for a positive kernel. -/
def IsBirkhoffHopfContractionCoefficient {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) (γ : ℝ) : Prop :=
  ∀ x y : κ → ℝ,
    (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      finiteHilbertProjectiveLogSpread (positiveKernelApply G x) (positiveKernelApply G y) ≤
        γ * finiteHilbertProjectiveLogSpread x y

/-- The actual Birkhoff--Hopf contraction theorem for a strictly positive finite kernel.

This is the true Mathlib-facing hard theorem.  The preceding lemmas expose the finite cross-ratio
bound and an explicit strict coefficient.  A full proof should:

1. bound the image-cone Hilbert diameter using `positiveKernelCrossRatio_le_bound`;
2. apply Birkhoff's oscillation contraction estimate to Hilbert projective spread;
3. use the coarser coefficient `positiveKernelBirkhoffCoefficient`, which is still `< 1`.

This is intentionally stronger and more useful than the old bare `∃ γ, 0 ≤ γ ∧ γ < 1` seam. -/
theorem positive_kernel_birkhoff_hopf_contraction {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (_hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  sorry

/-- Birkhoff--Hopf coefficient seam for a strictly positive finite kernel.

This range-only wrapper is what the current DRSB Franklin--Lorenz file needs.  It is now proved from
an explicit finite cross-ratio coefficient; the genuine contraction estimate is isolated above as
`positive_kernel_birkhoff_hopf_contraction`. -/
theorem positive_kernel_birkhoff_contraction_coefficient {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 := by
  obtain ⟨hγ_nonneg, hγ_lt_one⟩ := positiveKernelBirkhoffCoefficient_nonneg_lt_one G hG
  exact ⟨positiveKernelBirkhoffCoefficient G, hγ_nonneg, hγ_lt_one⟩

end ForMathlib.Matrix
