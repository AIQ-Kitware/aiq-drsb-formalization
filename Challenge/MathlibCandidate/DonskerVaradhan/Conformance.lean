/-
# Donsker–Varadhan variational principle (Mathlib candidate 01)

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
open scoped ENNReal

namespace ForMathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

theorem isGreatest_donskerVaradhan
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hf_tilted : Integrable f (ν.tilted f)) :
    IsGreatest
      { r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ ≪ ν ∧
          Integrable f μ ∧ Integrable (llr μ ν) μ ∧
          r = ∫ x, f x ∂μ - (klDiv μ ν).toReal }
      (Real.log (∫ x, Real.exp (f x) ∂ν)) := by
  sorry

theorem log_integral_exp_eq_sSup
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hf_tilted : Integrable f (ν.tilted f)) :
    Real.log (∫ x, Real.exp (f x) ∂ν)
      = sSup { r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ ≪ ν ∧
          Integrable f μ ∧ Integrable (llr μ ν) μ ∧
          r = ∫ x, f x ∂μ - (klDiv μ ν).toReal } := by
  sorry

end ForMathlib.MeasureTheory
