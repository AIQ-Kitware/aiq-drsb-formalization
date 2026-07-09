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
  sorry

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
  sorry

/-- Paper route Step 4: positive-matrix finite image diameter bound in the current API.

This should replace the older image-diameter route once the column-diameter and convex-hull lemmas
above are proved. -/
theorem positive_kernel_apply_hilbert_log_diameter_bound_paper_route {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    PositiveKernelApplyHilbertLogDiameterBounded G
      (Real.log (positiveKernelCrossRatioBound G)) := by
  sorry

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
