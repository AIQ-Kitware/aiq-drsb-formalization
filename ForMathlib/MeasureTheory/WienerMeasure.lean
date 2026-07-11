/-
# The Wiener measure (continuum reference path law) via Kolmogorov extension

The law of standard Brownian motion on the path space `ℝ≥0 → ℝ`, built by applying the
(vendored) Kolmogorov extension theorem `MeasureTheory.projectiveLimit` to **Mathlib's own**
Brownian projective family `ProbabilityTheory.BrownianReal.projectiveFamily` (the centered
Gaussians with covariance `min s t`, proven consistent in Mathlib as
`isProjectiveMeasureFamily_projectiveFamily`).

This supplies the **continuum reference measure `R`** used by the DRSB Schrödinger-bridge
development.  Mathlib provides the Brownian projective family, and the vendored projective-limit
machinery in `ForMathlib/KolmogorovExtension/` constructs the path measure.

**Attribution.** The `projectiveLimit` machinery is vendored from `RemyDegenne/kolmogorov_extension4`
(Apache-2.0; see `ForMathlib/KolmogorovExtension/README.md`). This file is *our own* assembly on top
of Mathlib's projective family. `DRSB-INDEP` (related work): `RemyDegenne/brownian-motion`'s
`ProbabilityTheory.BrownianReal.gaussianLimit` builds the same object by the same recipe on that
repo's local Gaussian family; we instead apply the extension to Mathlib's in-pin family, so this is
independently written — cited as a see-also, not a derivation.
-/
import ForMathlib.KolmogorovExtension.KolmogorovExtension
import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ForMathlib.MeasureTheory

/-- **The Wiener measure** (law of standard real Brownian motion) on the path space `ℝ≥0 → ℝ`,
as the Kolmogorov extension (`projectiveLimit`) of Mathlib's Brownian projective family
`BrownianReal.projectiveFamily`. This is the DRSB continuum reference path law `R`. -/
noncomputable def wienerMeasure : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily

/-- The Wiener measure is a probability measure. -/
instance isProbabilityMeasure_wienerMeasure : IsProbabilityMeasure wienerMeasure :=
  isProbabilityMeasure_projectiveLimit BrownianReal.isProjectiveMeasureFamily_projectiveFamily

/-- **The finite-dimensional distributions of the Wiener measure are the Brownian Gaussians.**
For every finite set of times `I ⊆ ℝ≥0`, the pushforward of `wienerMeasure` under the coordinate
restriction `ω ↦ (ω t)_{t ∈ I}` is `BrownianReal.projectiveFamily I` — the centered Gaussian with
covariance `min s t`. This is the projective-limit / consistency property, and it is exactly the
"grid marginals of the continuum reference are the Gaussians" fact the DRSB energy identity's
projection argument needs on the reference side. -/
lemma isProjectiveLimit_wienerMeasure :
    IsProjectiveLimit wienerMeasure BrownianReal.projectiveFamily :=
  isProjectiveLimit_projectiveLimit BrownianReal.isProjectiveMeasureFamily_projectiveFamily

end ForMathlib.MeasureTheory
