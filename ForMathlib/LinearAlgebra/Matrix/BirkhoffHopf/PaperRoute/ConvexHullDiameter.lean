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

/-- Paper route Step 3: finite convex-hull diameter bound.

Paper analogue: Eveson--Nussbaum Proposition 2.9(b).  If all generator rays `v k` have pairwise
Hilbert distance at most `D`, then any two positive convex combinations of them also have Hilbert
distance at most `D`. -/
theorem hilbert_diameter_convexHull_le_generator_diameter {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (v : κ → ι → ℝ) (hv : ∀ k i, 0 < v k i) (D : ℝ)
    (hD : ∀ k l : κ, finiteHilbertProjectiveLogSpread (v k) (v l) ≤ D)
    (w₁ w₂ : κ → ℝ)
    (hw₁ : ∀ k, 0 ≤ w₁ k) (hw₂ : ∀ k, 0 ≤ w₂ k)
    (hw₁_sum : ∑ k : κ, w₁ k = 1) (hw₂_sum : ∑ k : κ, w₂ k = 1) :
    finiteHilbertProjectiveLogSpread
        (fun i : ι => ∑ k : κ, w₁ k * v k i)
        (fun i : ι => ∑ k : κ, w₂ k * v k i) ≤ D := by
  sorry

/-- Paper route Step 3, ray version: nonzero nonnegative combinations differ from convex
combinations only by positive scalar normalization.

Paper analogue: Proposition 2.9(a), passing between a cone and a cross-section on the same
nonnegative rays. -/
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
  sorry

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
