/-
# KL disintegration: conditional KL is the integrated kernel KL

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) with the
proof omitted;
`Leaderboard.lean` imports the project and supplies the proofs. `#print axioms` on a
listed theorem transitively certifies its whole proof tree, so the supporting lemmas
are not listed. Where one listed theorem is a corollary of another (both are public
entry points of the same proposed PR), the dependency gate is transitive either way.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open InformationTheory

namespace ForMathlib.MeasureTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}

theorem klDiv_compProd_eq_lintegral
    (μ : Measure 𝓧) (κ η : Kernel 𝓧 𝓨)
    [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]
    [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  sorry

theorem toReal_klDiv_compProd_eq_integral
    (μ : Measure 𝓧) (κ η : Kernel 𝓧 𝓨)
    [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]
    [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (h_fin : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ x, (klDiv (κ x) (η x)).toReal ∂μ := by
  sorry

end ForMathlib.MeasureTheory
