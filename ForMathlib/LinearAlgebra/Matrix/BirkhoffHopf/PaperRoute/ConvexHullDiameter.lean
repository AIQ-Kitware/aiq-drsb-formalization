/-
# Convex-hull diameter step in the finite positive cone

This file isolates the finite-coordinate version of Eveson--Nussbaum Proposition 2.9(b): a convex
hull of mutually comparable rays has the same Hilbert diameter as the generating set.

For the finite positive-matrix proof, this is the bridge from column-wise projective diameter to the
projective diameter of the whole image cone.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.PositiveConeHilbert

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix
namespace BirkhoffHopf.PaperRoute

/-- Paper route Step 3: positive convex combinations stay strictly positive.

This is the finite-cone positivity fact used before applying Hilbert's metric to convex
combinations of positive columns. -/
theorem positive_convex_combination_pos {ι κ : Type*} [Fintype κ]
    (v : κ → ι → ℝ) (hv : ∀ k i, 0 < v k i)
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k : κ, w k = 1)
    (i : ι) :
    0 < ∑ k : κ, w k * v k i := by
  classical
  have hw_exists_pos : ∃ k : κ, 0 < w k := by
    by_contra hnone
    have hw_zero : ∀ k : κ, w k = 0 := by
      intro k
      have hle : w k ≤ 0 := by
        exact le_of_not_gt (fun hk_pos => hnone ⟨k, hk_pos⟩)
      exact le_antisymm hle (hw k)
    have hsum_zero : (∑ k : κ, w k) = 0 := by
      simp [hw_zero]
    have hone_zero : (1 : ℝ) = 0 := by
      rw [← hsum, hsum_zero]
    norm_num at hone_zero
  obtain ⟨k₀, hwk₀_pos⟩ := hw_exists_pos
  exact Finset.sum_pos'
    (fun k _hk => mul_nonneg (hw k) (le_of_lt (hv k i)))
    ⟨k₀, Finset.mem_univ k₀, mul_pos hwk₀_pos (hv k₀ i)⟩

/-- Paper route Step 3: strictly positive combinations with positive total weight. -/
theorem nonneg_combination_pos {ι κ : Type*} [Fintype κ]
    (v : κ → ι → ℝ) (hv : ∀ k i, 0 < v k i)
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwpos : 0 < ∑ k : κ, w k) (i : ι) :
    0 < ∑ k : κ, w k * v k i := by
  classical
  have hex : ∃ k, 0 < w k := by
    by_contra h
    have hall : ∀ k, w k = 0 := fun k =>
      le_antisymm (not_lt.mp (fun hk => h ⟨k, hk⟩)) (hw k)
    simp [hall] at hwpos
  obtain ⟨k₀, hk₀⟩ := hex
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hw k) (le_of_lt (hv k i)))
    ⟨k₀, Finset.mem_univ k₀, mul_pos hk₀ (hv k₀ i)⟩

/-- Paper route Step 3, ray version: nonzero nonnegative combinations of mutually comparable rays
have Hilbert diameter at most the generator diameter.

Paper analogue: Eveson--Nussbaum Proposition 2.9(a)/(b).  The argument never uses the normalization
`∑ w = 1`, only nonnegativity of the weights and positivity of their total, so the cone statement is
the general one and the convex-hull statement below is a corollary.

The estimate is termwise: `hD` gives the generator cross-multiplicative bound
`v k i * v l i' ≤ exp D * (v k i' * v l i)`, and summing it against the nonnegative weights
`w₁ k * w₂ l` bounds the cross-ratio of the two combinations. -/
theorem hilbert_diameter_nonnegativeHull_le_generator_diameter {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (v : κ → ι → ℝ) (hv : ∀ k i, 0 < v k i) (D : ℝ)
    (hD : ∀ k l : κ, finiteHilbertProjectiveLogSpread (v k) (v l) ≤ D)
    (w₁ w₂ : κ → ℝ)
    (hw₁ : ∀ k, 0 ≤ w₁ k) (hw₂ : ∀ k, 0 ≤ w₂ k)
    (hw₁_pos : 0 < ∑ k : κ, w₁ k) (hw₂_pos : 0 < ∑ k : κ, w₂ k) :
    finiteHilbertProjectiveLogSpread
        (fun i : ι => ∑ k : κ, w₁ k * v k i)
        (fun i : ι => ∑ k : κ, w₂ k * v k i) ≤ D := by
  classical
  have hgen : ∀ (k l : κ) (i i' : ι), v k i * v l i' ≤ Real.exp D * (v k i' * v l i) := by
    intro k l i i'
    have hle : Real.log ((v k i * v l i') / (v k i' * v l i)) ≤ D :=
      le_trans (finiteHilbertProjectiveLogSpread_pair_le (v k) (v l) i i') (hD k l)
    have hden : 0 < v k i' * v l i := mul_pos (hv k i') (hv l i)
    have hnum : 0 < v k i * v l i' := mul_pos (hv k i) (hv l i')
    rw [Real.log_le_iff_le_exp (div_pos hnum hden), div_le_iff₀ hden] at hle
    linarith
  apply finiteHilbertProjectiveLogSpread_le_of_forall_pair
  intro i i'
  have hX : ∀ i, 0 < ∑ k : κ, w₁ k * v k i := fun i => nonneg_combination_pos v hv w₁ hw₁ hw₁_pos i
  have hY : ∀ i, 0 < ∑ k : κ, w₂ k * v k i := fun i => nonneg_combination_pos v hv w₂ hw₂ hw₂_pos i
  rw [Real.log_le_iff_le_exp (div_pos (mul_pos (hX i) (hY i')) (mul_pos (hX i') (hY i))),
    div_le_iff₀ (mul_pos (hX i') (hY i))]
  have hterm : ∀ k l : κ, (w₁ k * v k i) * (w₂ l * v l i')
      ≤ Real.exp D * ((w₁ k * v k i') * (w₂ l * v l i)) := by
    intro k l
    have hww : 0 ≤ w₁ k * w₂ l := mul_nonneg (hw₁ k) (hw₂ l)
    nlinarith [hgen k l i i', hww]
  calc (∑ k : κ, w₁ k * v k i) * (∑ k : κ, w₂ k * v k i')
      = ∑ k : κ, ∑ l : κ, (w₁ k * v k i) * (w₂ l * v l i') := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
    _ ≤ ∑ k : κ, ∑ l : κ, Real.exp D * ((w₁ k * v k i') * (w₂ l * v l i)) :=
        Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hterm k l))
    _ = Real.exp D * ((∑ k : κ, w₁ k * v k i') * (∑ k : κ, w₂ k * v k i)) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Paper route Step 3: finite convex-hull diameter bound.

Paper analogue: Eveson--Nussbaum Proposition 2.9(b).  If all generator rays `v k` have pairwise
Hilbert distance at most `D`, then any two positive convex combinations of them also have Hilbert
distance at most `D`.  This is the `∑ w = 1` case of the cone statement above. -/
theorem hilbert_diameter_convexHull_le_generator_diameter {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (v : κ → ι → ℝ) (hv : ∀ k i, 0 < v k i) (D : ℝ)
    (hD : ∀ k l : κ, finiteHilbertProjectiveLogSpread (v k) (v l) ≤ D)
    (w₁ w₂ : κ → ℝ)
    (hw₁ : ∀ k, 0 ≤ w₁ k) (hw₂ : ∀ k, 0 ≤ w₂ k)
    (hw₁_sum : ∑ k : κ, w₁ k = 1) (hw₂_sum : ∑ k : κ, w₂ k = 1) :
    finiteHilbertProjectiveLogSpread
        (fun i : ι => ∑ k : κ, w₁ k * v k i)
        (fun i : ι => ∑ k : κ, w₂ k * v k i) ≤ D :=
  hilbert_diameter_nonnegativeHull_le_generator_diameter v hv D hD w₁ w₂ hw₁ hw₂
    (by rw [hw₁_sum]; exact zero_lt_one) (by rw [hw₂_sum]; exact zero_lt_one)

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
