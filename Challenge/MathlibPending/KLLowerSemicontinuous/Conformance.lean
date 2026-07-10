/-
# Setwise lower semicontinuity of the KL divergence

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) with the
proof omitted;
`Leaderboard.lean` imports the project and supplies the proofs. `#print axioms` on a
listed theorem transitively certifies its whole proof tree, so the supporting lemmas
are not listed. Where one listed theorem is a corollary of another (both are public
entry points of the same proposed PR), the dependency gate is transitive either way.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory InformationTheory Filter
open scoped ENNReal Topology

namespace ForMathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

variable (μ ν : Measure α)

theorem toReal_klDiv_le_of_tendsto_integral {ι : Type*} {l : Filter ι} [l.NeBot]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (μs : ι → Measure α)
    [∀ i, IsProbabilityMeasure (μs i)]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ)
    (hacs : ∀ i, μs i ≪ ν) (hllrs : ∀ i, Integrable (llr (μs i) ν) (μs i))
    (hconv : ∀ f : α → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun i => ∫ x, f x ∂(μs i)) l (𝓝 (∫ x, f x ∂μ)))
    (C : ℝ) (hC : ∀ i, (klDiv (μs i) ν).toReal ≤ C) :
    (klDiv μ ν).toReal ≤ C := by
  sorry

end ForMathlib.MeasureTheory
