/-
# Assembly theorem for the paper-route Birkhoff--Hopf proof

This file is the intended replacement spine for the currently parked weighted-average route.  It
matches the finite-dimensional chain described in the Eveson--Nussbaum modernization note:

positive matrix
  -> image cone is the nonnegative hull of its positive columns
  -> convex-hull diameter equals generator diameter
  -> positive-matrix diameter is the four-index cross-ratio formula
  -> reduce contraction to the normalized two-by-two calculation
  -> export the current `IsBirkhoffHopfContractionCoefficient` theorem.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.PositiveMatrixDiameter
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.TwoByTwo

set_option autoImplicit false

namespace ForMathlib.Matrix
namespace BirkhoffHopf.PaperRoute

/-- Paper route Step 7: arbitrary finite positive matrices inherit the two-dimensional
Birkhoff--Hopf contraction.

Paper analogue: Eveson--Nussbaum Lemma 3.11, reduction to two-dimensional subspaces, together with
Theorem 5.3.  In the finite-matrix specialization this should be proved by restricting to the
coordinates appearing in a four-point cross-ratio. -/
theorem positiveKernel_birkhoff_contraction_from_twoByTwo {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (_hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  sorry

/-- Paper route Step 8: public finite positive-kernel Birkhoff--Hopf contraction theorem.

This is the theorem that should eventually replace the current weighted-average proof spine in
`ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf`. -/
theorem positive_kernel_birkhoff_hopf_contraction_paper_route {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  exact positiveKernel_birkhoff_contraction_from_twoByTwo G hG

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
