/-
# Local sharp vs. global coarse Birkhoff--Hopf coefficient

The single place where depending on **both** finite Birkhoff--Hopf proof routes is intentional.
It records, and makes machine-checkable, the precise coefficient distinction:

* Both public finite-kernel capstones — the direct Doeblin route
  `ForMathlib.Matrix.positive_kernel_birkhoff_hopf_contraction` and the paper route
  `ForMathlib.Matrix.BirkhoffHopf.PaperRoute.positive_kernel_birkhoff_hopf_contraction_paper_route`
  — export the **same** coefficient `positiveKernelBirkhoffCoefficient G = (B - 1) / B`, where
  `B = positiveKernelCrossRatioBound G` is the deliberately coarse finite cross-ratio *sum* bound.

* The paper route proves a genuinely sharper normalized **two-dimensional** coefficient internally:
  for the symmetric kernel `[[α, 1], [1, α]]` (`α > 1`) the local contraction ratio is
  `(α - 1) / (α + 1) = tanh ((log α) / 2)` (`symmetricTwoByTwoPhi_le`).

* But the paper **assembly** relaxes that local `2 × 2` result back to the same coarse global
  `(B - 1) / B` (its final `calc` bounds by `((B - 1) / B) * …`). So the paper capstone does **not**
  yet export a sharper global matrix coefficient than the direct route.

This module proves the clean algebraic gap between the sharp local coefficient `(α - 1) / (α + 1)`
and the coarse coefficient `(B - 1) / B` at the two-by-two cross-ratio diameter `B = α²`, namely
`(α - 1) / (α + 1) < (α² - 1) / α²`. A sharper global paper-route theorem would retain the local
coefficient through the global assembly; that generalization is described in
`audits/UPSTREAM_CANDIDATES_2026-07-10.md`.

Nothing in either proof route imports this module.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.Direct
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix
namespace BirkhoffHopf.Comparison

/-- **Sharp local coefficient is strictly below the coarse coefficient.**

For `α > 1`, the sharp normalized two-by-two Birkhoff coefficient `(α - 1) / (α + 1)` is strictly
smaller than the coarse coefficient `(B - 1) / B` evaluated at the two-by-two cross-ratio diameter
`B = α²`.  The gap is exactly `(α - 1) · (2α + 1)` after clearing denominators:
`(α² - 1)(α + 1) - (α - 1)α² = (α - 1)(2α + 1) > 0`.  Pure ordered-field algebra — it invokes
neither contraction theorem. -/
theorem symmetricTwoByTwoCoefficient_lt_coarse {α : ℝ} (hα : 1 < α) :
    (α - 1) / (α + 1) < (α ^ 2 - 1) / α ^ 2 := by
  have hαp : (0 : ℝ) < α + 1 := by linarith
  have hα2 : (0 : ℝ) < α ^ 2 := by positivity
  rw [div_lt_div_iff₀ hαp hα2]
  nlinarith [mul_pos (sub_pos.mpr hα) (show (0 : ℝ) < 2 * α + 1 by linarith)]

/-- Non-strict `≤` corollary of `symmetricTwoByTwoCoefficient_lt_coarse`, convenient for rewriting
in a chain that only needs the coarse coefficient as an upper bound. -/
theorem symmetricTwoByTwoCoefficient_le_coarse {α : ℝ} (hα : 1 < α) :
    (α - 1) / (α + 1) ≤ (α ^ 2 - 1) / α ^ 2 :=
  le_of_lt (symmetricTwoByTwoCoefficient_lt_coarse hα)

/-- The paper route's sharp local bound placed inside the coarse regime: the maximized normalized
two-by-two ratio `symmetricTwoByTwoPhi α t` is strictly below the coarse coefficient `(α² - 1) / α²`.
Chains the paper-route sharp estimate `symmetricTwoByTwoPhi_le` with the algebraic comparison. -/
theorem symmetricTwoByTwoPhi_lt_coarse {α t : ℝ} (hα : 1 < α) (ht : 0 < t) :
    BirkhoffHopf.PaperRoute.symmetricTwoByTwoPhi α t < (α ^ 2 - 1) / α ^ 2 :=
  lt_of_le_of_lt (BirkhoffHopf.PaperRoute.symmetricTwoByTwoPhi_le hα ht)
    (symmetricTwoByTwoCoefficient_lt_coarse hα)

/-- **Both public capstones export the same coarse coefficient.**

A concrete witness that the direct route and the paper route certify the *identical*
`positiveKernelBirkhoffCoefficient G`; the paper route does not (yet) hand back a sharper global
coefficient.  This is exactly why the sharpening campaign in the upstream dossier remains open. -/
theorem both_routes_export_same_coarse_coefficient {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) ∧
      IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) :=
  ⟨positive_kernel_birkhoff_hopf_contraction G hG,
    BirkhoffHopf.PaperRoute.positive_kernel_birkhoff_hopf_contraction_paper_route G hG⟩

end BirkhoffHopf.Comparison
end ForMathlib.Matrix
