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



/-- Pairwise logarithmic ratio control plus a uniform box gives pairwise ordinary-ratio control.

This is the reusable real-analysis bridge needed by the Franklin--Lorenz right-column path.  It
reduces the pairwise statement to the pointwise `log`-to-ordinary-error lemma above by applying that
lemma to the quotient family

`(k, i, j) ↦ r k i / r k j`.

The remaining estimate is the elementary identity

`r_i - r_j = r_j * (r_i / r_j - 1)`

and the uniform bound on `|r_j|`. -/
theorem pairwise_error_geometric_bound_of_pairwise_log_ratio_bound_and_box
    {ι : Type*} [Fintype ι]
    (r : ℕ → ι → ℝ) (γ : ℝ)
    (hγ_nonneg : 0 ≤ γ) (hγ_lt_one : γ < 1)
    (hr_pos : ∀ k j, 0 < r k j)
    (hr_box : ∃ R : ℝ, 0 ≤ R ∧ ∀ k j, |r k j| ≤ R)
    (hlog : ∃ C : ℝ,
      0 ≤ C ∧ ∀ k (ij : ι × ι), |Real.log ((r k ij.1) / (r k ij.2))| ≤ C * γ ^ k) :
    ∃ C : ℝ,
      0 ≤ C ∧ ∀ k (ij : ι × ι), |r k ij.1 - r k ij.2| ≤ C * γ ^ k := by
  classical
  rcases hr_box with ⟨R, hR_nonneg, hR_bound⟩
  rcases hlog with ⟨C, hC_nonneg, hC_bound⟩
  let q : ℕ → (ι × ι) → ℝ := fun k ij => r k ij.1 / r k ij.2
  have hq_pos : ∀ k ij, 0 < q k ij := by
    intro k ij
    exact div_pos (hr_pos k ij.1) (hr_pos k ij.2)
  have hq_log : ∀ k ij, |Real.log (q k ij)| ≤ C * γ ^ k := by
    intro k ij
    exact hC_bound k ij
  have hq_bound :=
    hard_core_relative_error_geometric_bound_explicit_constant_of_log_bound
      q C γ hC_nonneg hγ_nonneg hγ_lt_one hq_pos hq_log
  refine ⟨R * (Real.exp C * C), ?_, ?_⟩
  · exact mul_nonneg hR_nonneg (mul_nonneg (le_of_lt (Real.exp_pos C)) hC_nonneg)
  · intro k ij
    have hden_pos : 0 < r k ij.2 := hr_pos k ij.2
    have hden_ne : r k ij.2 ≠ 0 := ne_of_gt hden_pos
    have hrewrite : r k ij.1 - r k ij.2 = r k ij.2 * (q k ij - 1) := by
      dsimp [q]
      field_simp [hden_ne]
    rw [hrewrite, abs_mul]
    have hrel := hq_bound k ij
    have hden_bound : |r k ij.2| ≤ R := hR_bound k ij.2
    have hrel_nonneg : 0 ≤ |q k ij - 1| := abs_nonneg _
    have hprod := mul_le_mul hden_bound hrel hrel_nonneg hR_nonneg
    calc
      |r k ij.2| * |q k ij - 1|
          ≤ R * ((Real.exp C * C) * γ ^ k) := hprod
      _ = (R * (Real.exp C * C)) * γ ^ k := by ring

end ForMathlib.Analysis
