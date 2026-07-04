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

end ForMathlib.MeasureTheory
