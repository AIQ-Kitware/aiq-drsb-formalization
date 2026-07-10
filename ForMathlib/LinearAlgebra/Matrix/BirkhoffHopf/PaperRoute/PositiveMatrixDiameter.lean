/-
# Positive-matrix image diameter formula

This file stages the finite positive-matrix theorem corresponding to Eveson--Nussbaum Theorem 6.2:
for a strictly positive matrix, the projective diameter of the image cone is the maximum of the
Hilbert distances between columns, equivalently the log of the finite four-index cross-ratio bound.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.ConvexHullDiameter

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix
namespace BirkhoffHopf.PaperRoute

/-- Paper route Step 4: image diameter is controlled by the diameter of the positive columns.

Paper analogue: Eveson--Nussbaum Theorem 6.2, first formula
`Δ(A) = max_{i,j in J} d(A e_i, A e_j)` in the strictly positive finite matrix case. -/
theorem positiveKernelApply_image_diameter_le_column_diameter {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) (D : ℝ)
    (hD : ∀ j j' : κ,
      finiteHilbertProjectiveLogSpread (fun i : ι => G i j) (fun i : ι => G i j') ≤ D) :
    ∀ x y : κ → ℝ,
      (∀ j, 0 < x j) → (∀ j, 0 < y j) →
        finiteHilbertProjectiveLogSpread
          (positiveKernelApply G x) (positiveKernelApply G y) ≤ D := by
  intro x y hx hy
  -- `G · x = ∑ⱼ xⱼ · (column j)` is a nonnegative combination of the columns
  have hxsum : 0 < ∑ j : κ, x j := Finset.sum_pos (fun j _ => hx j) Finset.univ_nonempty
  have hysum : 0 < ∑ j : κ, y j := Finset.sum_pos (fun j _ => hy j) Finset.univ_nonempty
  have hrwx : positiveKernelApply G x = fun i : ι => ∑ j : κ, x j * (fun j i => G i j) j i := by
    funext i; simp only [positiveKernelApply]; exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hrwy : positiveKernelApply G y = fun i : ι => ∑ j : κ, y j * (fun j i => G i j) j i := by
    funext i; simp only [positiveKernelApply]; exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [hrwx, hrwy]
  exact hilbert_diameter_nonnegativeHull_le_generator_diameter
    (fun j i => G i j) (fun j i => hG i j) D hD x y
    (fun j => (hx j).le) (fun j => (hy j).le) hxsum hysum

/-- Paper route Step 4: column diameter is bounded by the explicit finite cross-ratio bound.

Paper analogue: Eveson--Nussbaum Theorem 6.2, strictly positive matrix formula
`Δ(A) = log max_{i,j,p,q} a_{p i} a_{q j} / (a_{p j} a_{q i})`.

The current staging API uses the coarser finite sum bound `positiveKernelCrossRatioBound G`; this
is enough for a strict coefficient and can later be sharpened to a finite maximum. -/
theorem positiveKernel_column_diameter_le_crossratio_bound {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    ∀ j j' : κ,
      finiteHilbertProjectiveLogSpread (fun i : ι => G i j) (fun i : ι => G i j') ≤
        Real.log (positiveKernelCrossRatioBound G) := by
  intro j j'
  apply finiteHilbertProjectiveLogSpread_le_of_forall_pair
  intro i i'
  -- the `(i,i')` cross-ratio of columns `j, j'` *is* `positiveKernelCrossRatio G i i' j j'`
  have hpos : 0 < (G i j * G i' j') / (G i' j * G i j') :=
    div_pos (mul_pos (hG i j) (hG i' j')) (mul_pos (hG i' j) (hG i j'))
  refine Real.log_le_log hpos ?_
  have h := positiveKernelCrossRatio_le_bound G hG i i' j j'
  unfold positiveKernelCrossRatio at h
  calc (G i j * G i' j') / (G i' j * G i j')
      = (G i j * G i' j') / (G i j' * G i' j) := by rw [mul_comm (G i' j) (G i j')]
    _ ≤ positiveKernelCrossRatioBound G := h

/-- Paper route Step 4: positive-matrix finite image diameter bound in the current API.

Composition of the two Eveson--Nussbaum steps above: the image cone is the nonnegative hull of the
positive columns, and the column diameter is bounded by the explicit cross-ratio bound. -/
theorem positive_kernel_apply_hilbert_log_diameter_bound_paper_route {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    PositiveKernelApplyHilbertLogDiameterBounded G
      (Real.log (positiveKernelCrossRatioBound G)) :=
  positiveKernelApply_image_diameter_le_column_diameter G hG _
    (positiveKernel_column_diameter_le_crossratio_bound G hG)

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
