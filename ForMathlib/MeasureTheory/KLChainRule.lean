/-
# Real-valued KL chain rule (marginal split)

Real-valued (`toReal`) form of Mathlib's Kullback–Leibler chain rule
`InformationTheory.klDiv_compProd_eq_add`. This is the **marginal-split backbone (★)** of the
roadmap for `ChenGeorgiouPavon2021.energy_identity` (see `ROADMAP_ENERGY_IDENTITY.md`): for path
laws that disintegrate over the initial coordinate as `P = ρ₀ ⊗ₘ Kᵘ`, `R = ρ₀^W ⊗ₘ Kᵂ`,

`D(P‖R) = D(ρ₀‖ρ₀^W) + D(ρ₀⊗ₘKᵘ ‖ ρ₀⊗ₘKᵂ)`.

Mathlib's chain rule *"holds without any assumption on the measurable spaces"*, so this works for
the abstract path space `Path X = ℝ→X` (only a `MeasurableSpace`), with no standard-Borel
hypothesis. The only extra content over the `ℝ≥0∞` chain rule is the `toReal` bookkeeping, which
needs both summands finite (the finite-relative-entropy / finite-energy regime).

Axiom-clean; a thin, reusable wrapper. No new mathematics — the mathematics is Mathlib's.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ForMathlib.MeasureTheory

open InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}

/-- **Real-valued KL chain rule / marginal split (★).**
`(D(μ⊗ₘκ ‖ ν⊗ₘη)).toReal = (D(μ‖ν)).toReal + (D(μ⊗ₘκ ‖ μ⊗ₘη)).toReal`, the `toReal` form of
`InformationTheory.klDiv_compProd_eq_add`.  The finiteness hypotheses `h1`, `h2` (each summand
`≠ ∞`) are exactly what lets `toReal` distribute over the sum; they hold in the finite-relative-
entropy regime.  No assumption on the measurable spaces. -/
theorem toReal_klDiv_compProd_eq_add
    (μ ν : Measure 𝓧) (κ η : Kernel 𝓧 𝓨)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
    (h1 : klDiv μ ν ≠ ∞) (h2 : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    (klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)).toReal
      = (klDiv μ ν).toReal + (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal := by
  rw [klDiv_compProd_eq_add, ENNReal.toReal_add h1 h2]

/-- **Conditional KL divergence = averaged pointwise KL (cond).**
`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ`: the KL divergence between two
composition-products *sharing the same first marginal* `μ` is the `μ`-average of the pointwise KL
divergences of the kernel slices.

This is **exactly the integral form of the conditional KL divergence that Mathlib's
`InformationTheory/KullbackLeibler/ChainRule.lean` lists as a `TODO`** (the file proves only the
`compProd`-vs-`compProd` form `klDiv (μ⊗ₘκ) (μ⊗ₘη)`, deferring the `μ[fun x ↦ klDiv (κ x) (η x)]`
form because measurability of `x ↦ klDiv (κ x) (η x)` "is not always guaranteed"). Here we obtain
the `ℝ≥0∞`-valued identity with **no measurability side-condition on that map**: the only analytic
hypothesis is absolute continuity `μ ⊗ₘ κ ≪ μ ⊗ₘ η` (the finite-relative-entropy / Girsanov domain
regime), because we never integrate `x ↦ klDiv (κ x) (η x)` directly — we recognise it, `μ`-a.e., as
the inner slice of a lintegral of the *jointly measurable* kernel Radon–Nikodym derivative
`Kernel.rnDeriv κ η`. That derivative carries the standard `CountableOrCountablyGenerated 𝓧 𝓨`
typeclass (the setting in which `Kernel.rnDeriv` is jointly measurable — the same hypothesis Mathlib
uses throughout `Probability/Kernel/RadonNikodym`), which is the *only* structural assumption. It
holds for every standard-Borel / Polish state and value space.

Roadmap role (see `ROADMAP_ENERGY_IDENTITY.md`, step (cond)): this reduces the abstract conditional
edge `D(ρ₀⊗ₘKᵘ ‖ ρ₀⊗ₘKᵂ)` of `ChenGeorgiouPavon2021.energy_identity` to the **per-trajectory
Cameron–Martin atom** `∫ D(Kᵘ_x ‖ Kᵂ_x) dρ₀`, which is the object whose discrete Euler–Maruyama
instance is already proved. No stochastic-analysis infrastructure is used.

Proof sketch. Per-trajectory absolute continuity `κ x ≪ η x` holds `μ`-a.e.
(`absolutelyContinuous_compProd_right_iff`), so `κ x = η.withDensity (κ.rnDeriv η) x` `μ`-a.e.
(`Kernel.withDensity_rnDeriv_eq`). Hence `μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2)`
(`compProd_congr` then `compProd_withDensity`), so the compProd Radon–Nikodym derivative *is* that
jointly measurable density (`rnDeriv_withDensity`). Writing `klDiv` as a lintegral of `klFun` of the
derivative (`klDiv_eq_lintegral_klFun_of_ac`), `lintegral_compProd` peels the outer `μ`-integral, and
the inner `η x`-integral is recognised as `klDiv (κ x) (η x)` via
`Kernel.rnDeriv_eq_rnDeriv_measure`. -/
theorem klDiv_compProd_eq_lintegral
    (μ : Measure 𝓧) (κ η : Kernel 𝓧 𝓨)
    [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]
    [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  -- per-trajectory absolute continuity, μ-a.e.
  have h_ac_ker : ∀ᵐ x ∂μ, κ x ≪ η x :=
    Measure.absolutelyContinuous_compProd_right_iff.mp h_ac
  -- μ-a.e. `κ x` is `η x` reweighted by the kernel Radon–Nikodym derivative
  have hκ_eq : ∀ᵐ x ∂μ, κ x = η.withDensity (κ.rnDeriv η) x := by
    filter_upwards [h_ac_ker] with x hx using (Kernel.withDensity_rnDeriv_eq hx).symm
  have hmeas : Measurable (fun p : 𝓧 × 𝓨 ↦ κ.rnDeriv η p.1 p.2) := κ.measurable_rnDeriv η
  -- so `μ ⊗ₘ κ` is the withDensity of `μ ⊗ₘ η` by that jointly measurable density
  have h_wd : μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) := by
    rw [Measure.compProd_congr hκ_eq, Measure.compProd_withDensity hmeas]
  -- read off the compProd Radon–Nikodym derivative
  have h_rn : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] (fun p ↦ κ.rnDeriv η p.1 p.2) := by
    rw [h_wd]; exact Measure.rnDeriv_withDensity (μ ⊗ₘ η) hmeas
  -- the integrand of the compProd KL lintegral, in terms of the kernel derivative
  have hint : Measurable (fun p : 𝓧 × 𝓨 ↦
      ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)) :=
    (measurable_klFun.comp hmeas.ennreal_toReal).ennreal_ofReal
  rw [klDiv_eq_lintegral_klFun_of_ac h_ac,
    lintegral_congr_ae (h_rn.mono fun p hp ↦ by rw [hp]),
    Measure.lintegral_compProd hint]
  -- the inner `η x`-integral is `klDiv (κ x) (η x)`, μ-a.e.
  refine lintegral_congr_ae ?_
  filter_upwards [h_ac_ker] with x hx
  rw [klDiv_eq_lintegral_klFun_of_ac hx]
  refine lintegral_congr_ae ?_
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := x)] with y hy
  rw [hy]

/-- **Conditional KL divergence = averaged pointwise KL (cond), real / integral form.**
`(klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ x, (klDiv (κ x) (η x)).toReal ∂μ` — the exact statement of the
roadmap's step (cond): the (finite) conditional relative entropy equals the `μ`-average of the
per-slice relative entropies as an ordinary Bochner integral.

The `ℝ≥0∞`-valued `klDiv_compProd_eq_lintegral` supplies the identity; the extra content here is the
`toReal`↔`∫` bridge. Crucially, although `x ↦ klDiv (κ x) (η x)` need not be measurable in general
(the very reason Mathlib defers this form), it is `μ`-a.e. equal to the manifestly measurable slice
lintegral of the jointly measurable `Kernel.rnDeriv κ η` (`Measurable.lintegral_kernel_prod_right'`),
hence `AEMeasurable`; finiteness of the total (`h_fin`) forces the slices `μ`-a.e. finite
(`ae_lt_top'`), so `integral_toReal` applies. -/
theorem toReal_klDiv_compProd_eq_integral
    (μ : Measure 𝓧) (κ η : Kernel 𝓧 𝓨)
    [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]
    [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (h_fin : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ x, (klDiv (κ x) (η x)).toReal ∂μ := by
  have hmeas : Measurable (fun p : 𝓧 × 𝓨 ↦ κ.rnDeriv η p.1 p.2) := κ.measurable_rnDeriv η
  -- the slice map is μ-a.e. the measurable slice lintegral of the kernel derivative
  have hg_meas : Measurable
      (fun x ↦ ∫⁻ y, ENNReal.ofReal (klFun (κ.rnDeriv η x y).toReal) ∂(η x)) :=
    Measurable.lintegral_kernel_prod_right' (κ := η)
      ((measurable_klFun.comp hmeas.ennreal_toReal).ennreal_ofReal)
  have h_ac_ker : ∀ᵐ x ∂μ, κ x ≪ η x :=
    Measure.absolutelyContinuous_compProd_right_iff.mp h_ac
  have key : (fun x ↦ klDiv (κ x) (η x))
      =ᵐ[μ] (fun x ↦ ∫⁻ y, ENNReal.ofReal (klFun (κ.rnDeriv η x y).toReal) ∂(η x)) := by
    filter_upwards [h_ac_ker] with x hx
    rw [klDiv_eq_lintegral_klFun_of_ac hx]
    refine lintegral_congr_ae ?_
    filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := x)] with y hy
    rw [hy]
  have haem : AEMeasurable (fun x ↦ klDiv (κ x) (η x)) μ := ⟨_, hg_meas, key⟩
  have h_lint : ∫⁻ x, klDiv (κ x) (η x) ∂μ ≠ ∞ := by
    rwa [← klDiv_compProd_eq_lintegral μ κ η h_ac]
  rw [klDiv_compProd_eq_lintegral μ κ η h_ac, ← integral_toReal haem (ae_lt_top' haem h_lint)]

end ForMathlib.MeasureTheory
