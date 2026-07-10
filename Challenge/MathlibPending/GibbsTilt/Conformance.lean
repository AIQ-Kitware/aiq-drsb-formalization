/-
# The Gibbs tilt: finite KL and the attained entropic Lagrangian

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

theorem klDiv_tilted_ne_top {ν : Measure α} [IsProbabilityMeasure ν] {g : α → ℝ}
    (hexp : Integrable (fun x => Real.exp (g x)) ν) (hg : Integrable g (ν.tilted g)) :
    klDiv (ν.tilted g) ν ≠ ⊤ := by
  sorry

theorem entropic_gibbs_attained_tilted {ν : Measure α} [IsProbabilityMeasure ν] {f cx : α → ℝ}
    {κ lam : ℝ} (hκ : 0 < κ) (hlam : 0 < lam)
    (hexp : Integrable (fun y => Real.exp ((f y - lam * cx y) / (lam * κ))) ν)
    (hf : Integrable f (ν.tilted fun y => (f y - lam * cx y) / (lam * κ)))
    (hc : Integrable cx (ν.tilted fun y => (f y - lam * cx y) / (lam * κ))) :
    lam * κ * Real.log (∫ y, Real.exp ((f y - lam * cx y) / (lam * κ)) ∂ν)
      = (∫ y, f y ∂(ν.tilted fun y => (f y - lam * cx y) / (lam * κ)))
        - lam * ((∫ y, cx y ∂(ν.tilted fun y => (f y - lam * cx y) / (lam * κ)))
          + κ * (klDiv (ν.tilted fun y => (f y - lam * cx y) / (lam * κ)) ν).toReal) := by
  sorry

end ForMathlib.MeasureTheory
