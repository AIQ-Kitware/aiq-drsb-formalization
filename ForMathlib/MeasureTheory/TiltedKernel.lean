/-
# The tilted (Gibbs) kernel (Mathlib-staging)

Mathlib has `Measure.tilted ν g = ν.withDensity (fun y => ofReal (exp (g y) / ∫ exp g dν))`, the
Gibbs measure attached to a *single* potential `g`. Entropic optimal transport needs the
**parametrized** family `x ↦ ν.tilted (A x)` packaged as a `Kernel α β`, so that `μ̂ ⊗ₘ P` is a
coupling and the KL chain rule applies to it.

`Kernel.withDensity` supplies exactly that, once the joint density is shown measurable; the tilted
normalizer `Z x = ∫ exp (A x ·) dν` is measurable in `x` by `StronglyMeasurable.integral_prod_right'`.

This is the object that turns the *pointwise* Gibbs attainment identity
(`ForMathlib.MeasureTheory.entropic_gibbs_attained_tilted`) into a statement about couplings: the
converse Lagrangian bound of Sinkhorn-DRO strong duality.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ForMathlib.MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **The tilted (Gibbs) kernel**: `x ↦ ν.tilted (A x)`, as a `Kernel α β`.

Built as a `Kernel.withDensity` of the constant kernel so that measurability in `x` is handled by
the `withDensity` API rather than by hand. See `tiltedKernel_apply` for the defining property (which
holds *for every* `x`, not merely a.e.). -/
noncomputable def tiltedKernel (ν : Measure β) [SFinite ν] (A : α → β → ℝ) : Kernel α β :=
  Kernel.withDensity (Kernel.const α ν)
    (fun x y => ENNReal.ofReal (Real.exp (A x y) / ∫ z, Real.exp (A x z) ∂ν))

/-- The normalizer `Z x = ∫ exp (A x ·) dν` of the tilted kernel is measurable. -/
theorem measurable_tiltedKernel_normalizer (ν : Measure β) [SFinite ν] (A : α → β → ℝ)
    (hA : Measurable (Function.uncurry A)) :
    Measurable fun x : α => ∫ z, Real.exp (A x z) ∂ν :=
  (StronglyMeasurable.integral_prod_right'
    (f := fun p : α × β => Real.exp (A p.1 p.2))
    (Real.continuous_exp.comp_stronglyMeasurable hA.stronglyMeasurable)).measurable

/-- **The tilted kernel is the tilted measure, pointwise.** -/
theorem tiltedKernel_apply (ν : Measure β) [SFinite ν] (A : α → β → ℝ)
    (hA : Measurable (Function.uncurry A)) (x : α) :
    tiltedKernel ν A x = ν.tilted (A x) := by
  have hd : Measurable (Function.uncurry fun x y =>
      ENNReal.ofReal (Real.exp (A x y) / ∫ z, Real.exp (A x z) ∂ν)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp hA).div
        ((measurable_tiltedKernel_normalizer ν A hA).comp measurable_fst))
  rw [tiltedKernel, Kernel.withDensity_apply _ hd, Kernel.const_apply]
  rfl

/-- **The tilted kernel is Markov** when every potential slice has an integrable exponential. -/
theorem isMarkovKernel_tiltedKernel (ν : Measure β) [IsProbabilityMeasure ν] (A : α → β → ℝ)
    (hA : Measurable (Function.uncurry A))
    (hexp : ∀ x, Integrable (fun y => Real.exp (A x y)) ν) :
    IsMarkovKernel (tiltedKernel ν A) := by
  constructor
  intro x
  rw [tiltedKernel_apply ν A hA x]
  exact isProbabilityMeasure_tilted (hexp x)

end ForMathlib.MeasureTheory
