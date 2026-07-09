/-
# Normalized two-by-two Birkhoff computation

This file stages the concrete calculus core of Eveson--Nussbaum Section 5.  After reducing a
positive two-dimensional problem by cone automorphisms, the normalized matrix is

  A_α = [[α, 1], [1, α]],  α > 1.

The contraction constant is `(α - 1) / (α + 1) = tanh ((log α) / 2)`, obtained by maximizing the
one-variable function

  φ(t) = ((α^2 - 1) * t) / ((α + t) * (α * t + 1)).
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.PositiveConeHilbert

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix
namespace BirkhoffHopf.PaperRoute

/-- The normalized symmetric positive two-by-two kernel from Eveson--Nussbaum Section 5. -/
noncomputable def symmetricTwoByTwoKernel (α : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then α else 1

/-- The one-variable function whose maximum gives the normalized two-by-two contraction ratio. -/
noncomputable def symmetricTwoByTwoPhi (α t : ℝ) : ℝ :=
  ((α ^ 2 - 1) * t) / ((α + t) * (α * t + 1))

/-- Positivity of the normalized symmetric two-by-two kernel. -/
theorem symmetricTwoByTwoKernel_pos {α : ℝ} (hα : 1 < α) :
    ∀ i j : Fin 2, 0 < symmetricTwoByTwoKernel α i j := by
  intro i j
  unfold symmetricTwoByTwoKernel
  by_cases hij : i = j
  · simp [hij, lt_trans zero_lt_one hα]
  · simp [hij]

/-- Paper route Step 5: the elementary calculus maximum in the normalized two-by-two case.

Paper analogue: Eveson--Nussbaum Theorem 5.3, where `φ'(t) = 0` iff `t = 1`, and the maximum value
is `(α - 1) / (α + 1)`.  This should be attacked as a pure real-algebra/calculus lemma. -/
theorem symmetricTwoByTwoPhi_le {α t : ℝ} (hα : 1 < α) (ht : 0 < t) :
    symmetricTwoByTwoPhi α t ≤ (α - 1) / (α + 1) := by
  sorry

/-- Paper route Step 5: normalized two-by-two Birkhoff contraction.

Paper analogue: Eveson--Nussbaum Theorem 5.3,
`N(A_α) = k(A_α) = (α - 1)/(α + 1)`. -/
theorem symmetricTwoByTwo_birkhoff_contraction {α : ℝ} (hα : 1 < α) :
    IsBirkhoffHopfContractionCoefficient
      (symmetricTwoByTwoKernel α) ((α - 1) / (α + 1)) := by
  sorry

/-- Paper route Step 6: positive two-by-two matrices reduce to the normalized symmetric case.

Paper analogue: Eveson--Nussbaum Lemma 5.1.  Positive diagonal row/column scalings, possibly
combined with a row swap, transform a positive nonsingular `2 × 2` matrix into
`[[α, 1], [1, α]]` with `α > 1`.  The existential data below records exactly the scaling and
permutation witnesses that later invariance lemmas must consume. -/
theorem positive_twoByTwo_reduces_to_symmetric_normal_form
    (A : Fin 2 → Fin 2 → ℝ) (_hA : ∀ i j, 0 < A i j)
    (_hdet : A (0 : Fin 2) (0 : Fin 2) * A (1 : Fin 2) (1 : Fin 2) ≠
      A (0 : Fin 2) (1 : Fin 2) * A (1 : Fin 2) (0 : Fin 2)) :
    ∃ α : ℝ, ∃ rowScale colScale : Fin 2 → ℝ, ∃ rowPerm : Fin 2 ≃ Fin 2,
      1 < α ∧
        (∀ i, 0 < rowScale i) ∧
        (∀ j, 0 < colScale j) ∧
        (∀ i j : Fin 2,
          rowScale i * A (rowPerm i) j * colScale j = symmetricTwoByTwoKernel α i j) := by
  sorry

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
