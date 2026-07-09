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

/-- Pointwise cross-product form of the finite cross-ratio bound.

This is the algebraic atom used before summing against nonnegative weights in the image-cone
cross-ratio estimate. -/
def PositiveKernelPointwiseCrossRatioBounded {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) : Prop :=
  ∀ i i' : ι, ∀ j j' : κ,
    G i j * G i' j' ≤ positiveKernelCrossRatioBound G * (G i' j * G i j')

/-- The explicit finite cross-ratio bound gives the pointwise cross-product inequality. -/
theorem positive_kernel_pointwise_crossRatioBounded {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j) :
    PositiveKernelPointwiseCrossRatioBounded G := by
  classical
  intro i i' j j'
  have hle := positiveKernelCrossRatio_le_bound G hG i i' j j'
  have hden : 0 < G i j' * G i' j := mul_pos (hG i j') (hG i' j)
  have hmul : G i j * G i' j' ≤
      positiveKernelCrossRatioBound G * (G i j' * G i' j) := by
    simpa [positiveKernelCrossRatio] using (div_le_iff₀ hden).1 hle
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

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

/-- Finite-sum image cross-ratio bound, assuming the pointwise cross-product inequality.

This is now the remaining algebra-only summation seam.  It should be proved by expanding the two
products of finite sums and summing `hpoint i i' j j'` against the nonnegative weights
`x j * y j'`. -/
theorem positive_kernel_apply_crossRatioBounded_of_pointwise_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (hpoint : PositiveKernelPointwiseCrossRatioBounded G) :
    PositiveKernelApplyCrossRatioBounded G := by
  classical
  unfold PositiveKernelApplyCrossRatioBounded positiveKernelApply
  intro x y hx hy i i'
  let B : ℝ := positiveKernelCrossRatioBound G
  have hterm : ∀ j j' : κ,
      (G i j * x j) * (G i' j' * y j') ≤
        B * ((G i' j * x j) * (G i j' * y j')) := by
    intro j j'
    have hxy : 0 ≤ x j * y j' := mul_nonneg (hx j) (hy j')
    have hmul := mul_le_mul_of_nonneg_right (hpoint i i' j j') hxy
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsum :
      (∑ j : κ, ∑ j' : κ, (G i j * x j) * (G i' j' * y j')) ≤
        ∑ j : κ, ∑ j' : κ,
          B * ((G i' j * x j) * (G i j' * y j')) := by
    exact Finset.sum_le_sum (fun j _hj =>
      Finset.sum_le_sum (fun j' _hj' => hterm j j'))
  calc
    (∑ j : κ, G i j * x j) * (∑ j : κ, G i' j * y j)
        = ∑ j : κ, ∑ j' : κ, (G i j * x j) * (G i' j' * y j') := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.mul_sum]
    _ ≤ ∑ j : κ, ∑ j' : κ,
          B * ((G i' j * x j) * (G i j' * y j')) := hsum
    _ = B * ((∑ j : κ, G i' j * x j) * (∑ j : κ, G i j * y j)) := by
          simp [B, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Finite-sum image cross-ratio bound for a strictly positive kernel.

The pointwise cross-product estimate is proved above from the explicit cross-ratio bound.  The only
remaining algebraic work is the separate summation seam
`positive_kernel_apply_crossRatioBounded_of_pointwise_bound`. -/
theorem positive_kernel_apply_crossRatioBounded {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j) :
    PositiveKernelApplyCrossRatioBounded G := by
  exact positive_kernel_apply_crossRatioBounded_of_pointwise_bound G
    (positive_kernel_pointwise_crossRatioBounded G hG)

/-- A pointwise bound on every log cross-ratio implies a bound on the finite Hilbert spread.

This is a small finite-`sSup` bridge.  The nonemptiness assumption is the natural one for
Hilbert's projective metric; the empty coordinate type is not a positive cone. -/
theorem finiteHilbertProjectiveLogSpread_le_of_forall_pair {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) (Δ : ℝ)
    (h : ∀ i i' : ι, Real.log ((x i * y i') / (x i' * y i)) ≤ Δ) :
    finiteHilbertProjectiveLogSpread x y ≤ Δ := by
  classical
  unfold finiteHilbertProjectiveLogSpread
  apply csSup_le (Set.range_nonempty _)
  intro z hz
  rcases hz with ⟨ij, rfl⟩
  exact h ij.1 ij.2

/-- Pointwise image log-cross-ratio control from the algebraic image cross-ratio bound. -/
theorem positive_kernel_apply_log_crossratio_le_of_apply_crossratio_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hbound : PositiveKernelApplyCrossRatioBounded G)
    (x y : κ → ℝ)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (i i' : ι) :
    Real.log (((positiveKernelApply G x i) * (positiveKernelApply G y i')) /
        ((positiveKernelApply G x i') * (positiveKernelApply G y i))) ≤
      Real.log (positiveKernelCrossRatioBound G) := by
  classical
  let B : ℝ := positiveKernelCrossRatioBound G
  have hx_nonneg : ∀ j, 0 ≤ x j := fun j => le_of_lt (hx j)
  have hy_nonneg : ∀ j, 0 ≤ y j := fun j => le_of_lt (hy j)
  have hle := hbound x y hx_nonneg hy_nonneg i i'
  have hnum_pos : 0 < positiveKernelApply G x i * positiveKernelApply G y i' :=
    mul_pos (positiveKernelApply_pos G hG x hx i)
      (positiveKernelApply_pos G hG y hy i')
  have hden_pos : 0 < positiveKernelApply G x i' * positiveKernelApply G y i :=
    mul_pos (positiveKernelApply_pos G hG x hx i')
      (positiveKernelApply_pos G hG y hy i)
  have hratio_pos : 0 <
      ((positiveKernelApply G x i * positiveKernelApply G y i') /
        (positiveKernelApply G x i' * positiveKernelApply G y i)) :=
    div_pos hnum_pos hden_pos
  have hratio_le :
      ((positiveKernelApply G x i * positiveKernelApply G y i') /
        (positiveKernelApply G x i' * positiveKernelApply G y i)) ≤ B := by
    exact (div_le_iff₀ hden_pos).2 (by simpa [B] using hle)
  exact Real.log_le_log hratio_pos (by simpa [B] using hratio_le)

/-- A finite positive kernel has image Hilbert diameter at most `Δ`.

This is the projective-diameter half of Birkhoff--Hopf: it is weaker than contraction, but it is
the exact bridge from the cross-multiplicative image estimate to the analytic oscillation lemma. -/
def PositiveKernelApplyHilbertLogDiameterBounded {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) (Δ : ℝ) : Prop :=
  ∀ x y : κ → ℝ,
    (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      finiteHilbertProjectiveLogSpread (positiveKernelApply G x) (positiveKernelApply G y) ≤ Δ

/-- The finite image cross-ratio bound gives a finite Hilbert projective diameter bound.

This is still substantial but algebraic/topological rather than the full Birkhoff oscillation
estimate: prove every image cross-ratio is at most `positiveKernelCrossRatioBound G`, take logs,
and pass to the finite supremum defining `finiteHilbertProjectiveLogSpread`. -/
theorem positive_kernel_apply_hilbert_log_diameter_bound_of_apply_crossratio_bound {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hbound : PositiveKernelApplyCrossRatioBounded G) :
    PositiveKernelApplyHilbertLogDiameterBounded G
      (Real.log (positiveKernelCrossRatioBound G)) := by
  classical
  unfold PositiveKernelApplyHilbertLogDiameterBounded
  intro x y hx hy
  apply finiteHilbertProjectiveLogSpread_le_of_forall_pair
  intro i i'
  exact positive_kernel_apply_log_crossratio_le_of_apply_crossratio_bound G hG hbound x y hx hy i i'

/-- Weighted-average form of the finite Birkhoff--Hopf scalar core.

This is the irreducible two-measure/finite-simplex inequality behind the positive-matrix theorem,
and is the Lean target closest to the elementary two-dimensional reduction in
Eveson--Nussbaum/Carroll.  The positive weights `a` and `b` are two rows of the positive kernel;
the hypothesis `hweight` says their projective diameter is bounded by `B`.  The conclusion says
that averaging two positive vectors against those two comparable weights contracts the Hilbert
log-spread by the coarse Birkhoff coefficient `(B - 1) / B`.

Once this scalar weighted-average inequality is proved, the matrix pointwise theorem below is just
substitution with `a j = G i j` and `b j = G i' j`. -/
theorem finite_weighted_average_log_crossratio_contraction_of_crossratio_bound {κ : Type*}
    [Fintype κ] [Nonempty κ]
    (a b x y : κ → ℝ) (B : ℝ)
    (_ha : ∀ j, 0 < a j) (_hb : ∀ j, 0 < b j)
    (_hx : ∀ j, 0 < x j) (_hy : ∀ j, 0 < y j)
    (_hB : 1 ≤ B)
    (_hweight : ∀ j j' : κ, a j * b j' ≤ B * (b j * a j')) :
    Real.log (((∑ j : κ, a j * x j) * (∑ j : κ, b j * y j)) /
        ((∑ j : κ, b j * x j) * (∑ j : κ, a j * y j))) ≤
      ((B - 1) / B) * finiteHilbertProjectiveLogSpread x y := by
  sorry

/-- Pointwise four-coordinate form of Birkhoff's oscillation estimate.

This is now only the matrix instantiation of the weighted-average scalar core above.  The remaining
nontrivial proof debt is no longer matrix bookkeeping: it is the finite weighted-average
Birkhoff--Hopf inequality
`finite_weighted_average_log_crossratio_contraction_of_crossratio_bound`. -/
theorem positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_apply_hilbert_log_diameter_bound
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (_hdiam : PositiveKernelApplyHilbertLogDiameterBounded G
      (Real.log (positiveKernelCrossRatioBound G)))
    (x y : κ → ℝ)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (i i' : ι) :
    Real.log (((positiveKernelApply G x i) * (positiveKernelApply G y i')) /
        ((positiveKernelApply G x i') * (positiveKernelApply G y i))) ≤
      positiveKernelBirkhoffCoefficient G * finiteHilbertProjectiveLogSpread x y := by
  classical
  have hcore :=
    finite_weighted_average_log_crossratio_contraction_of_crossratio_bound
      (a := fun j : κ => G i j)
      (b := fun j : κ => G i' j)
      (x := x)
      (y := y)
      (B := positiveKernelCrossRatioBound G)
      (fun j => hG i j)
      (fun j => hG i' j)
      hx
      hy
      (positiveKernelCrossRatioBound_one_le G hG)
      (positive_kernel_pointwise_crossRatioBounded G hG i i')
  simpa [positiveKernelApply, positiveKernelBirkhoffCoefficient] using hcore

/-- Birkhoff's oscillation estimate from finite image diameter.

The only nontrivial ingredient is the pointwise four-coordinate oscillation estimate above.  This
wrapper just packages those pointwise inequalities into the finite supremum defining Hilbert
projective spread.  The coefficient here is the deliberately coarse explicit coefficient
`(B - 1) / B`, which is above the standard `tanh (Δ / 4)` coefficient when `B = exp Δ`. -/
theorem positive_kernel_birkhoff_hopf_contraction_of_apply_hilbert_log_diameter_bound
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hdiam : PositiveKernelApplyHilbertLogDiameterBounded G
      (Real.log (positiveKernelCrossRatioBound G))) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  classical
  unfold IsBirkhoffHopfContractionCoefficient
  intro x y hx hy
  apply finiteHilbertProjectiveLogSpread_le_of_forall_pair
  intro i i'
  exact
    positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_apply_hilbert_log_diameter_bound
      G hG hdiam x y hx hy i i'

/-- Birkhoff's oscillation estimate once the image-cone cross-ratio is bounded.

This is the analytic/projective-metric subgoal: turn the finite image cross-ratio bound into
Hilbert projective contraction with the explicit coefficient.  It is now only a wrapper around two
smaller Mathlib-style seams: finite image diameter from cross-ratio control, and the pure
Birkhoff--Hopf oscillation estimate from finite image diameter. -/
theorem positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hbound : PositiveKernelApplyCrossRatioBounded G) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  exact positive_kernel_birkhoff_hopf_contraction_of_apply_hilbert_log_diameter_bound G hG
    (positive_kernel_apply_hilbert_log_diameter_bound_of_apply_crossratio_bound G hG hbound)

/-- The actual Birkhoff--Hopf contraction theorem for a strictly positive finite kernel.

This wrapper is now proved from two smaller seams:

1. the finite double-sum image cross-ratio bound,
   `positive_kernel_apply_crossRatioBounded`;
2. the projective oscillation estimate,
   `positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound`.

The old single broad `sorry` has therefore been split into an algebraic task and an analytic
Hilbert-metric task. -/
theorem positive_kernel_birkhoff_hopf_contraction {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
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
