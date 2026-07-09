/-
# Marginal-inversion seams for the finite Sinkhorn ratio proof

This file isolates the algebra that converts ordinary potential ratios into hatted ratios via the
left and right marginal identities.  The remaining `finite_sinkhorn_hatted_ratio_lower_from_forward_upper`
seam is intentionally here so it can be attacked separately from the weighted-average equality lemma.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.FiniteSystem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Right marginal identities say that hatted right ratios are inverse right ratios. -/
theorem finite_sinkhorn_hatted1_ratio_eq_inv {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (j : ι) :
    sinkhornRatio ψhat1 φhat1 j = (sinkhornRatio ψ1 φ1 j)⁻¹ := by
  unfold sinkhornRatio
  have hψ1_ne : ψ1 j ≠ 0 := ne_of_gt (hψsys.φ1_pos j)
  have hφ1_ne : φ1 j ≠ 0 := ne_of_gt (hφsys.φ1_pos j)
  have hφhat1_ne : φhat1 j ≠ 0 := ne_of_gt (hφsys.φhat1_pos j)
  field_simp [hψ1_ne, hφ1_ne, hφhat1_ne]
  calc
    ψhat1 j * ψ1 j = ψ1 j * ψhat1 j := by ring
    _ = q j := hψsys.normalize_right j
    _ = φ1 j * φhat1 j := by rw [← hφsys.normalize_right j]
    _ = φhat1 j * φ1 j := by ring

/-- Left marginal identities say that hatted left ratios are inverse left ratios. -/
theorem finite_sinkhorn_hatted0_ratio_eq_inv {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (i : ι) :
    sinkhornRatio ψhat0 φhat0 i = (sinkhornRatio ψ0 φ0 i)⁻¹ := by
  unfold sinkhornRatio
  have hψ0_ne : ψ0 i ≠ 0 := ne_of_gt (hψsys.φ0_pos i)
  have hφ0_ne : φ0 i ≠ 0 := ne_of_gt (hφsys.φ0_pos i)
  have hφhat0_ne : φhat0 i ≠ 0 := ne_of_gt (hφsys.φhat0_pos i)
  field_simp [hψ0_ne, hφ0_ne, hφhat0_ne]
  calc
    ψhat0 i * ψ0 i = ψ0 i * ψhat0 i := by ring
    _ = p i := hψsys.normalize_left i
    _ = φ0 i * φhat0 i := by rw [← hφsys.normalize_left i]
    _ = φhat0 i * φ0 i := by ring

/-- At the right-ratio maximizer, the hatted-right ratio is exactly the inverse maximum.

This is the pointwise marginal-inversion equality for the distinguished index `jstar`. -/
theorem finite_sinkhorn_hatted1_ratio_eq_inv_at_right_max {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (jstar : ι) :
    sinkhornRatio ψhat1 φhat1 jstar = (sinkhornRatio ψ1 φ1 jstar)⁻¹ := by
  exact finite_sinkhorn_hatted1_ratio_eq_inv p q G
    φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys jstar

/-- The marginal identities invert common-ratio upper bounds into hatted-ratio lower bounds.

This is the algebraic bridge from the forward upper bound to the hatted-left side.  It is
true pointwise because `ψ0 * ψhat0 = p = φ0 * φhat0`, so the hatted ratio is the inverse
of the ordinary ratio. -/
theorem finite_sinkhorn_hatted_ratio_lower_from_forward_upper {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (_hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (M : ℝ)
    (_hleft_upper : ∀ i, sinkhornRatio ψ0 φ0 i ≤ M) :
    (∀ i, M⁻¹ ≤ sinkhornRatio ψhat0 φhat0 i) := by
  sorry


end ChenGeorgiouPavon2021
