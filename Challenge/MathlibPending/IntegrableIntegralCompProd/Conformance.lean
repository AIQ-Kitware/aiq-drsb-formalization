/-
# Measure-level `Integrable.integral_compProd`

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) with the
proof omitted;
`Leaderboard.lean` imports the project and supplies the proofs. `#print axioms` on a
listed theorem transitively certifies its whole proof tree, so the supporting lemmas
are not listed. Where one listed theorem is a corollary of another (both are public
entry points of the same proposed PR), the dependency gate is transitive either way.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ForMathlib.OT

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem integrable_integral_compProd {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsSFiniteKernel κ] {g : α × β → ℝ} (hg : Integrable g (μ ⊗ₘ κ)) :
    Integrable (fun x => ∫ y, g (x, y) ∂(κ x)) μ := by
  sorry

end ForMathlib.OT
