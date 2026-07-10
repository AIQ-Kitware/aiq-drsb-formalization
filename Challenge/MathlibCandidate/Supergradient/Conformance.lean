/-
# Supergradient existence for concave functions on ℝ (Mathlib candidate 03)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) with the
proof omitted;
`Leaderboard.lean` imports the project and supplies the proofs. `#print axioms` on a
listed theorem transitively certifies its whole proof tree, so the supporting lemmas
are not listed. Where one listed theorem is a corollary of another (both are public
entry points of the same proposed PR), the dependency gate is transitive either way.
-/
import Mathlib

set_option autoImplicit false

open Set

namespace ForMathlib.Analysis



theorem exists_supergradient_of_concaveOn {a b : ℝ} {h : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc a b) h) {δ : ℝ} (hδ : δ ∈ Ioo a b) :
    ∃ m : ℝ, ∀ t ∈ Icc a b, h t ≤ h δ + m * (t - δ) := by
  sorry

theorem exists_nonneg_multiplier {a b : ℝ} {h : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc a b) h) (hmono : MonotoneOn h (Icc a b)) {δ : ℝ} (hδ : δ ∈ Ioo a b) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ t ∈ Icc a b, h t + m * (δ - t) ≤ h δ := by
  sorry

theorem exists_supergradient_of_concaveOn' {s : Set ℝ} {h : ℝ → ℝ} (hconc : ConcaveOn ℝ s h)
    {a b δ : ℝ} (hamem : a ∈ s) (hbmem : b ∈ s) (haδ : a < δ) (hδb : δ < b) (hδ : δ ∈ s) :
    ∃ m : ℝ, ∀ t ∈ s, h t ≤ h δ + m * (t - δ) := by
  sorry

theorem exists_nonneg_multiplier' {s : Set ℝ} {h : ℝ → ℝ} (hconc : ConcaveOn ℝ s h)
    (hmono : MonotoneOn h s) {a b δ : ℝ} (hamem : a ∈ s) (hbmem : b ∈ s)
    (haδ : a < δ) (hδb : δ < b) (hδ : δ ∈ s) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ t ∈ s, h t + m * (δ - t) ≤ h δ := by
  sorry

end ForMathlib.Analysis
