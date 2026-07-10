/-
# Convexity of the Kullback–Leibler divergence (Mathlib candidate 02)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) with the
proof omitted;
`Leaderboard.lean` imports the project and supplies the proofs. `#print axioms` on a
listed theorem transitively certifies its whole proof tree, so the supporting lemmas
are not listed. Where one listed theorem is a corollary of another (both are public
entry points of the same proposed PR), the dependency gate is transitive either way.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace ForMathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

theorem klDiv_mix_le (a b : ℝ≥0) (hab : a + b = 1)
    (μ₁ μ₂ ν : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν]
    (hac₁ : μ₁ ≪ ν) (hac₂ : μ₂ ≪ ν) :
    klDiv (a • μ₁ + b • μ₂) ν ≤ a * klDiv μ₁ ν + b * klDiv μ₂ ν := by
  sorry

theorem klDiv_mix_ne_top (a b : ℝ≥0) (hab : a + b = 1)
    (μ₁ μ₂ ν : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν]
    (hac₁ : μ₁ ≪ ν) (hac₂ : μ₂ ≪ ν)
    (h₁ : klDiv μ₁ ν ≠ ⊤) (h₂ : klDiv μ₂ ν ≠ ⊤) :
    klDiv (a • μ₁ + b • μ₂) ν ≠ ⊤ := by
  sorry

theorem toReal_klDiv_mix_le (a b : ℝ≥0) (hab : a + b = 1)
    (μ₁ μ₂ ν : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν]
    (hac₁ : μ₁ ≪ ν) (hac₂ : μ₂ ≪ ν)
    (h₁ : klDiv μ₁ ν ≠ ⊤) (h₂ : klDiv μ₂ ν ≠ ⊤) :
    (klDiv (a • μ₁ + b • μ₂) ν).toReal
      ≤ (a : ℝ) * (klDiv μ₁ ν).toReal + (b : ℝ) * (klDiv μ₂ ν).toReal := by
  sorry

end ForMathlib.MeasureTheory
