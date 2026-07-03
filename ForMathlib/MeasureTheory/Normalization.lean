/-
# Normalizing a finite, nonzero measure to a probability measure (Mathlib-staging)

Mathlib has `Measure.tilted_const'` (`μ.tilted (fun _ ↦ c) = (μ univ)⁻¹ • μ`) and
`isProbabilityMeasure_tilted`, but no *direct* statement that scaling a finite,
nonzero measure by the inverse of its total mass yields a probability measure. That
one-line fact is used whenever a construction produces an unnormalized (finite,
nonzero) measure and one wants its normalization — here, the Sinkhorn-DRO worst-case
Gibbs conditional `γ*_x ∝ e^{(f−λc)/(λκ)} ν` (`WangGaoXie2023.exists_worstCase_gibbs`).

Upstream candidate: `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`
(next to `IsProbabilityMeasure`), or `Measure/Tilted.lean` as a corollary of
`tilted_const'`. Stated with explicit mass side-conditions (`μ univ ≠ 0`, `≠ ∞`)
rather than `[NeZero μ] [IsFiniteMeasure μ]` because the DRO call sites carry the
finiteness/positivity as hypotheses on the total mass, not as instances.
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace ForMathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Normalization to a probability measure.** Scaling a measure by the inverse of
its total mass gives a probability measure, provided that mass is nonzero and finite:
`IsProbabilityMeasure ((μ univ)⁻¹ • μ)`. The witness is `((μ univ)⁻¹ • μ) univ =
(μ univ)⁻¹ * μ univ = 1` by `ENNReal.inv_mul_cancel`. -/
theorem isProbabilityMeasure_inv_univ_smul (μ : Measure α)
    (h0 : μ Set.univ ≠ 0) (hfin : μ Set.univ ≠ ∞) :
    IsProbabilityMeasure ((μ Set.univ)⁻¹ • μ) :=
  ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hfin]⟩

end ForMathlib.MeasureTheory
