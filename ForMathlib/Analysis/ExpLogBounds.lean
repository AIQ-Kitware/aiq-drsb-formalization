/-
# Elementary exp/log error conversion bounds

Reusable analysis staging lemmas for converting logarithmic relative-error control into ordinary
multiplicative relative-error control.  These are independent of Sinkhorn, Franklin--Lorenz, and
Birkhoff--Hopf; they are the real-analysis tail behind projective metric convergence estimates.
-/

import Mathlib

set_option autoImplicit false

namespace ForMathlib.Analysis

/-- Hard analysis core: geometric decay of logarithmic relative error implies geometric decay of
multiplicative relative error.

For positive ratios `r k j`, a bound on `|log (r k j)|` should imply a bound on `|r k j - 1|`.
The proof should use that `exp` is locally Lipschitz on the bounded log range supplied by the initial
constant in the geometric log bound.  A typical constant is `C * exp C`, since `0 ≤ γ < 1` gives
`|log (r k j)| ≤ C` for every `k`.

This is intended as a small Mathlib-style analysis lemma, separate from the Franklin--Lorenz matrix
scaling argument. -/
theorem relative_error_geometric_bound_of_log_relative_error_geometric_bound
    {ι : Type*} [Fintype ι]
    (r : ℕ → ι → ℝ) (γ : ℝ)
    (_hγ_nonneg : 0 ≤ γ) (_hγ_lt_one : γ < 1)
    (_hr_pos : ∀ k j, 0 < r k j)
    (_hlog : ∃ C : ℝ,
      0 ≤ C ∧ ∀ k j, |Real.log (r k j)| ≤ C * γ ^ k) :
    ∃ C : ℝ,
      0 ≤ C ∧ ∀ k j, |r k j - 1| ≤ C * γ ^ k := by
  sorry

end ForMathlib.Analysis
