/-
# Positive-cone Hilbert metric facts for the paper-route Birkhoff--Hopf proof

This file starts the finite-dimensional route suggested by Eveson--Nussbaum's elementary proof
and the matrix formulas recorded in Section 6 of that paper:

1. work in the standard finite positive cone;
2. use the coordinate cross-ratio formula for Hilbert's projective metric;
3. record invariance under positive coordinate scalings / cone automorphisms;
4. feed those facts to convex-hull and two-dimensional reduction files.

The older weighted-average route remains in `ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf` for now.
This file is intentionally a paper-route staging surface, not a replacement API yet.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix
namespace BirkhoffHopf.PaperRoute

/-- Paper route Step 1: finite quadrant pairwise cross-ratio upper bound.

Paper analogue: the standard-quadrant formula in Section 6,
`d_C(x,y) = log max_{p,q} x_p y_q / (x_q y_p)`.

This wrapper exposes the already-staged finite-`sSup` lemma under a paper-route name. -/
theorem quadrant_hilbert_pair_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) (i i' : ι) :
    Real.log ((x i * y i') / (x i' * y i)) ≤
      finiteHilbertProjectiveLogSpread x y := by
  exact finiteHilbertProjectiveLogSpread_pair_le x y i i'

/-- Paper route Step 1: nonnegativity of Hilbert spread for strictly positive finite vectors.

Paper analogue: Hilbert's projective metric is a nonnegative pseudometric on each comparability
component. -/
theorem quadrant_hilbert_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    0 ≤ finiteHilbertProjectiveLogSpread x y := by
  exact finiteHilbertProjectiveLogSpread_nonneg_of_pos x y hx hy

/-- Paper route Step 2: invariance under positive coordinatewise scaling.

Paper analogue: Eveson--Nussbaum Lemma 3.12, cone-isomorphism invariance.  In the finite
standard cone, positive diagonal maps are cone automorphisms, so Hilbert projective distances are
unchanged after multiplying both vectors coordinatewise by the same positive scale. -/
theorem quadrant_hilbert_coordScale_eq {ι : Type*} [Fintype ι]
    (x y d : ι → ℝ) (_hd : ∀ i, 0 < d i) :
    finiteHilbertProjectiveLogSpread (fun i => d i * x i) (fun i => d i * y i) =
      finiteHilbertProjectiveLogSpread x y := by
  sorry

/-- Paper route Step 2: invariance under permutation of finite coordinates.

Paper analogue: cone-isomorphism invariance for permutation matrices. -/
theorem quadrant_hilbert_equivPerm_eq {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (x y : ι' → ℝ) :
    finiteHilbertProjectiveLogSpread (fun i : ι => x (e i)) (fun i : ι => y (e i)) =
      finiteHilbertProjectiveLogSpread x y := by
  sorry

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
