/-
# Measurable ε-argmax selectors (a KRN-free measurable selection)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) with the
proof omitted;
`Leaderboard.lean` imports the project and supplies the proofs.

The section structure mirrors the ForMathlib source exactly: the comparator compares
universe signatures and instance telescopes without alpha-normalising, so an added or
reordered `variable` shifts a universe slot and fails the export match.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory TopologicalSpace

namespace ForMathlib.MeasureTheory

variable {Y : Type*} [MeasurableSpace Y]

section CountableIndex

variable {ι : Type*} [Countable ι] [Nonempty ι] [MeasurableSpace ι]

theorem exists_measurable_eps_argmax
    (F : ι → Y → ℝ) (hF : ∀ i, Measurable (F i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Y → ι, Measurable g ∧ ∀ y, (⨆ i, F i y) - ε < F (g y) y := by
  sorry

end CountableIndex

section Separable

variable {X : Type*} [TopologicalSpace X] [Nonempty X]

theorem sSup_image_dense_eq (D : Set X) (hD : Dense D) (φ : X → ℝ) (hφ : Continuous φ)
    (hbdd : BddAbove (Set.range φ)) :
    sSup (φ '' D) = sSup (Set.range φ) := by
  sorry

variable [SeparableSpace X] [MeasurableSpace X]

theorem exists_measurable_eps_argmax_of_separable
    (F : X → Y → ℝ) (hFy : ∀ x, Measurable (F x))
    (hFx : ∀ y, Continuous fun x => F x y)
    (hbdd : ∀ y, BddAbove (Set.range fun x => F x y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Y → X, Measurable g ∧ ∀ y, (⨆ x, F x y) - ε < F (g y) y := by
  sorry

end Separable

end ForMathlib.MeasureTheory
