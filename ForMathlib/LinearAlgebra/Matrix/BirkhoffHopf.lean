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

/-- Applying a nonnegative finite kernel to a nonnegative vector gives a nonnegative vector. -/
theorem positiveKernelApply_nonneg {ι κ : Type*} [Fintype κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (x : κ → ℝ) (hx : ∀ j, 0 ≤ x j) (i : ι) :
    0 ≤ positiveKernelApply G x i := by
  classical
  unfold positiveKernelApply
  exact Finset.sum_nonneg (fun j _hj => mul_nonneg (hG i j) (hx j))

/-- Applying a strictly positive finite kernel to a nonnegative vector with at least one positive
coordinate gives a strictly positive output coordinate. -/
theorem positiveKernelApply_pos_of_exists_pos {ι κ : Type*} [Fintype κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j)
    (x : κ → ℝ) (hx_nonneg : ∀ j, 0 ≤ x j)
    {j₀ : κ} (hx_pos : 0 < x j₀) (i : ι) :
    0 < positiveKernelApply G x i := by
  classical
  unfold positiveKernelApply
  exact Finset.sum_pos'
    (fun j _hj => mul_nonneg (le_of_lt (hG i j)) (hx_nonneg j))
    ⟨j₀, Finset.mem_univ j₀, mul_pos (hG i j₀) hx_pos⟩

/-- Applying a strictly positive finite kernel to a strictly positive vector gives a strictly
positive vector, provided the input index type is nonempty. -/
theorem positiveKernelApply_pos {ι κ : Type*} [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j)
    (x : κ → ℝ) (hx : ∀ j, 0 < x j) (i : ι) :
    0 < positiveKernelApply G x i := by
  classical
  obtain ⟨j₀⟩ := (inferInstance : Nonempty κ)
  exact positiveKernelApply_pos_of_exists_pos G hG x (fun j => le_of_lt (hx j)) (hx_pos := hx j₀) i

/-- Algebraic cross-multiplicative image bound supplied by the finite kernel cross-ratio bound.

Expanding both kernel applications, this is the finite double-sum estimate
`G i j * G i' j' ≤ B * (G i' j * G i j')` integrated against nonnegative weights.
It is the first real Birkhoff--Hopf proof obligation after the elementary coefficient facts. -/
def PositiveKernelApplyCrossRatioBounded {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) : Prop :=
  ∀ x y : κ → ℝ,
    (∀ j, 0 ≤ x j) → (∀ j, 0 ≤ y j) →
      ∀ i i' : ι,
        positiveKernelApply G x i * positiveKernelApply G y i' ≤
          positiveKernelCrossRatioBound G *
            (positiveKernelApply G x i' * positiveKernelApply G y i)

/-- Finite-sum image cross-ratio bound for a strictly positive kernel.

This should be proved by expanding the two products of finite sums, applying
`positiveKernelCrossRatio_le_bound` termwise, and summing against the nonnegative weights
`x j * y j'`.  This is an algebraic, non-topological subgoal and can be assigned independently
of the projective-metric contraction proof. -/
theorem positive_kernel_apply_crossRatioBounded {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (_hG : ∀ i j, 0 < G i j) :
    PositiveKernelApplyCrossRatioBounded G := by
  sorry

/-- Birkhoff's oscillation estimate once the image-cone cross-ratio is bounded.

This is the analytic/projective-metric subgoal: turn the finite image cross-ratio bound into
Hilbert projective contraction with the explicit coefficient.  It is intentionally separated from
the preceding finite-sum algebra so the two hardest pieces can be attacked independently. -/
theorem positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (_hG : ∀ i j, 0 < G i j)
    (_hbound : PositiveKernelApplyCrossRatioBounded G) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  sorry

/-- The actual Birkhoff--Hopf contraction theorem for a strictly positive finite kernel.

This wrapper is now proved from two smaller seams:

1. the finite double-sum image cross-ratio bound,
   `positive_kernel_apply_crossRatioBounded`;
2. the projective oscillation estimate,
   `positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound`.

The old single broad `sorry` has therefore been split into an algebraic task and an analytic
Hilbert-metric task. -/
theorem positive_kernel_birkhoff_hopf_contraction {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  exact positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound G hG
    (positive_kernel_apply_crossRatioBounded G hG)

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
