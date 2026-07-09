/-
# Elementary exp/log error conversion bounds

Reusable analysis staging lemmas for converting logarithmic relative-error control into ordinary
multiplicative relative-error control.  These are independent of Sinkhorn, Franklin--Lorenz, and
Birkhoff--Hopf; they are the real-analysis tail behind projective metric convergence estimates.
-/

import Mathlib

set_option autoImplicit false

namespace ForMathlib.Analysis

/-- Hard analysis core with an explicit constant.

If `0 ≤ γ < 1` and the logarithmic relative errors satisfy
`|log (r k j)| ≤ C * γ^k`, then the ordinary relative errors satisfy the same geometric rate with
the explicit constant `exp C * C`.

The intended proof is one-variable calculus:

1. `0 ≤ γ < 1` gives `γ^k ≤ 1`, hence `|log (r k j)| ≤ C`;
2. for `|t| ≤ C`, the mean-value theorem / convexity of `exp` gives
   `|exp t - 1| ≤ exp C * |t|`;
3. use `exp (log r) = r` for `r > 0`.

This is a genuinely reusable Mathlib-style real-analysis lemma; it is independent of matrix
scaling. -/
theorem hard_core_relative_error_geometric_bound_explicit_constant_of_log_bound
    {ι : Type*} [Fintype ι]
    (r : ℕ → ι → ℝ) (C γ : ℝ)
    (_hC_nonneg : 0 ≤ C)
    (_hγ_nonneg : 0 ≤ γ) (_hγ_lt_one : γ < 1)
    (_hr_pos : ∀ k j, 0 < r k j)
    (_hlog : ∀ k j, |Real.log (r k j)| ≤ C * γ ^ k) :
    ∀ k j, |r k j - 1| ≤ (Real.exp C * C) * γ ^ k := by
  sorry

/-- Geometric decay of logarithmic relative error implies geometric decay of multiplicative
relative error.

This wrapper packages the explicit-constant hard core above into the existential form needed by the
Franklin--Lorenz development. -/
theorem relative_error_geometric_bound_of_log_relative_error_geometric_bound
    {ι : Type*} [Fintype ι]
    (r : ℕ → ι → ℝ) (γ : ℝ)
    (hγ_nonneg : 0 ≤ γ) (hγ_lt_one : γ < 1)
    (hr_pos : ∀ k j, 0 < r k j)
    (hlog : ∃ C : ℝ,
      0 ≤ C ∧ ∀ k j, |Real.log (r k j)| ≤ C * γ ^ k) :
    ∃ C : ℝ,
      0 ≤ C ∧ ∀ k j, |r k j - 1| ≤ C * γ ^ k := by
  rcases hlog with ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨Real.exp C * C, ?_, ?_⟩
  · exact mul_nonneg (le_of_lt (Real.exp_pos C)) hC_nonneg
  · exact hard_core_relative_error_geometric_bound_explicit_constant_of_log_bound
      r C γ hC_nonneg hγ_nonneg hγ_lt_one hr_pos hC_bound

end ForMathlib.Analysis
