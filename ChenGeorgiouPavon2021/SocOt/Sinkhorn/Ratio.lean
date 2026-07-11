/-
# Finite Sinkhorn ratio maximum principle

This module contains the finite uniqueness half of the Sinkhorn development, expressed as a
positive-matrix maximum principle independently of the convergence argument.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Ratio.WeightedAverage
import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Ratio.MarginalInversion

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Finite maximum witness for the right potential ratio.

This is the purely order-theoretic first step in the Sinkhorn ratio-collapse proof: on a nonempty
finite index type, the right ratio `ψ1 / φ1` has a maximizer.  It is separated out so the analytic
maximum-principle work below can be tried with a fixed `jstar` and a concrete extremal hypothesis. -/
theorem finite_sinkhorn_ratio_right_max_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    (φ1 ψ1 : ι → ℝ) :
    ∃ jstar : ι, ∀ j, sinkhornRatio ψ1 φ1 j ≤ sinkhornRatio ψ1 φ1 jstar := by
  classical
  obtain ⟨j0⟩ := (inferInstance : Nonempty ι)
  have huniv_nonempty : (Finset.univ : Finset ι).Nonempty := ⟨j0, by simp⟩
  obtain ⟨jstar, _hjstar_mem, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (sinkhornRatio ψ1 φ1) huniv_nonempty
  exact ⟨jstar, fun j => hmax j (by simp)⟩

/-- Forward equations rewrite the left ratio as a weighted average of right ratios.

This is the algebraic heart of the forward half of the maximum principle.  The weights are
`G i j * φ1 j`, and the denominator is the forward Sinkhorn sum for `φ0 i`. -/
theorem finite_sinkhorn_forward_ratio_identity {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1) :
    ∀ i, sinkhornRatio ψ0 φ0 i =
      (∑ j, (G i j * φ1 j) * sinkhornRatio ψ1 φ1 j) / φ0 i := by
  intro i
  have hsum :
      (∑ j, (G i j * φ1 j) * sinkhornRatio ψ1 φ1 j) =
        ∑ j, G i j * ψ1 j := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    unfold sinkhornRatio
    field_simp [ne_of_gt (hφsys.φ1_pos j)]
  calc
    sinkhornRatio ψ0 φ0 i = ψ0 i / φ0 i := rfl
    _ = (∑ j, G i j * ψ1 j) / φ0 i := by rw [hψsys.forward i]
    _ = (∑ j, (G i j * φ1 j) * sinkhornRatio ψ1 φ1 j) / φ0 i := by rw [hsum]

/-- The forward weighted-average bound after the ratio identity has been established.

This packages the generic weighted-average inequality with the Sinkhorn positivity hypotheses. -/
theorem finite_sinkhorn_forward_weighted_average_le_right_max {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (_hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (jstar : ι)
    (hright_max : ∀ j, sinkhornRatio ψ1 φ1 j ≤ sinkhornRatio ψ1 φ1 jstar) :
    ∀ i, (∑ j, (G i j * φ1 j) * sinkhornRatio ψ1 φ1 j) / φ0 i
      ≤ sinkhornRatio ψ1 φ1 jstar := by
  intro i
  exact finite_weighted_average_le_of_nonneg
    (fun j => G i j * φ1 j) (sinkhornRatio ψ1 φ1)
    (sinkhornRatio ψ1 φ1 jstar) (φ0 i)
    (fun j => mul_nonneg (le_of_lt (hG i j)) (le_of_lt (hφsys.φ1_pos j)))
    (hφsys.φ0_pos i)
    (hφsys.forward i)
    hright_max

/-- Forward weighted-average inequality for the finite Sinkhorn ratio proof.

With `jstar` maximizing the right ratio, the forward Sinkhorn equations and positivity of the kernel
show every left ratio is bounded above by the same right maximum.  The proof is split into the ratio
identity and a generic weighted-average inequality. -/
theorem finite_sinkhorn_ratio_left_le_right_max {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (jstar : ι)
    (hright_max : ∀ j, sinkhornRatio ψ1 φ1 j ≤ sinkhornRatio ψ1 φ1 jstar) :
    ∀ i, sinkhornRatio ψ0 φ0 i ≤ sinkhornRatio ψ1 φ1 jstar := by
  intro i
  rw [finite_sinkhorn_forward_ratio_identity p q G
    φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys i]
  exact finite_sinkhorn_forward_weighted_average_le_right_max p q G
    φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys jstar hright_max i

/-- Backward equations rewrite a hatted-right ratio as a weighted average of hatted-left
ratios.

This is the exact analogue of `finite_sinkhorn_forward_ratio_identity` for the backward Sinkhorn
equations. -/
theorem finite_sinkhorn_backward_hatted_ratio_identity {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1) :
    ∀ j, sinkhornRatio ψhat1 φhat1 j =
      (∑ i, (G i j * φhat0 i) * sinkhornRatio ψhat0 φhat0 i) / φhat1 j := by
  intro j
  have hsum :
      (∑ i, (G i j * φhat0 i) * sinkhornRatio ψhat0 φhat0 i) =
        ∑ i, G i j * ψhat0 i := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    unfold sinkhornRatio
    field_simp [ne_of_gt (hφsys.φhat0_pos i)]
  calc
    sinkhornRatio ψhat1 φhat1 j = ψhat1 j / φhat1 j := rfl
    _ = (∑ i, G i j * ψhat0 i) / φhat1 j := by rw [hψsys.backward j]
    _ = (∑ i, (G i j * φhat0 i) * sinkhornRatio ψhat0 φhat0 i) / φhat1 j := by
      rw [hsum]

/-- Lower bounds propagate through the backward hatted weighted average. -/
theorem finite_sinkhorn_backward_hatted_ratio_lower {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (M : ℝ)
    (hhat0_lower : ∀ i, M⁻¹ ≤ sinkhornRatio ψhat0 φhat0 i) :
    ∀ j, M⁻¹ ≤ sinkhornRatio ψhat1 φhat1 j := by
  intro j
  rw [finite_sinkhorn_backward_hatted_ratio_identity p q G
    φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys j]
  exact finite_weighted_average_ge_of_nonneg
    (fun i => G i j * φhat0 i) (sinkhornRatio ψhat0 φhat0)
    M⁻¹ (φhat1 j)
    (fun i => mul_nonneg (le_of_lt (hG i j)) (le_of_lt (hφsys.φhat0_pos i)))
    (hφsys.φhat1_pos j)
    (hφsys.backward j)
    hhat0_lower

/-- Strict positivity turns the single extremal equality into equality of all hatted-left ratios.

The Sinkhorn-specific part is only packaging: the backward equation identifies the hatted-right
ratio at `jstar` with a strictly-positive weighted average of hatted-left ratios, and the generic
weighted-average equality lemma forces every hatted-left ratio to hit the lower bound. -/
theorem finite_sinkhorn_backward_extreme_forces_hatted0_eq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (M : ℝ) (jstar : ι)
    (hhat0_lower : ∀ i, M⁻¹ ≤ sinkhornRatio ψhat0 φhat0 i)
    (hhat1_star : sinkhornRatio ψhat1 φhat1 jstar = M⁻¹) :
    ∀ i, sinkhornRatio ψhat0 φhat0 i = M⁻¹ := by
  have havg_eq :
      (∑ i, (G i jstar * φhat0 i) * sinkhornRatio ψhat0 φhat0 i) / φhat1 jstar =
        M⁻¹ := by
    rw [← finite_sinkhorn_backward_hatted_ratio_identity p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys jstar]
    exact hhat1_star
  exact finite_weighted_average_eq_lower_forces_pointwise
    (fun i => G i jstar * φhat0 i) (sinkhornRatio ψhat0 φhat0)
    M⁻¹ (φhat1 jstar)
    (fun i => mul_pos (hG i jstar) (hφsys.φhat0_pos i))
    (hφsys.φhat1_pos jstar)
    (hφsys.backward jstar)
    hhat0_lower
    havg_eq

/-- Once all hatted-left ratios are extremal, the backward equation makes all hatted-right ratios
extremal as well. -/
theorem finite_sinkhorn_backward_hatted_ratio_eq_of_hatted0_eq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (M : ℝ)
    (hhat0_eq : ∀ i, sinkhornRatio ψhat0 φhat0 i = M⁻¹) :
    ∀ j, sinkhornRatio ψhat1 φhat1 j = M⁻¹ := by
  intro j
  rw [finite_sinkhorn_backward_hatted_ratio_identity p q G
    φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys j]
  have hsum :
      (∑ i, (G i j * φhat0 i) * sinkhornRatio ψhat0 φhat0 i) =
        φhat1 j * M⁻¹ := by
    calc
      (∑ i, (G i j * φhat0 i) * sinkhornRatio ψhat0 φhat0 i)
          = ∑ i, (G i j * φhat0 i) * M⁻¹ := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hhat0_eq i]
      _ = (∑ i, G i j * φhat0 i) * M⁻¹ := by
            rw [Finset.sum_mul]
      _ = φhat1 j * M⁻¹ := by
            rw [← hφsys.backward j]
  rw [hsum]
  field_simp [ne_of_gt (hφsys.φhat1_pos j)]

/-- Marginal identities convert exact hatted-right ratios back to exact right ratios. -/
theorem finite_sinkhorn_right_ratio_eq_from_hatted_eq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (M : ℝ)
    (_hM_pos : 0 < M)
    (hhat1_eq : ∀ j, sinkhornRatio ψhat1 φhat1 j = M⁻¹) :
    ∀ j, sinkhornRatio ψ1 φ1 j = M := by
  intro j
  have hinv : M⁻¹ = (sinkhornRatio ψ1 φ1 j)⁻¹ := by
    rw [← hhat1_eq j]
    exact finite_sinkhorn_hatted1_ratio_eq_inv p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys j
  have h := congrArg (fun x : ℝ => x⁻¹) hinv
  simpa [inv_inv] using h.symm

/-- Marginal identities convert exact hatted-left ratios back to exact left ratios. -/
theorem finite_sinkhorn_left_ratio_eq_from_hatted_eq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (M : ℝ)
    (_hM_pos : 0 < M)
    (hhat0_eq : ∀ i, sinkhornRatio ψhat0 φhat0 i = M⁻¹) :
    ∀ i, sinkhornRatio ψ0 φ0 i = M := by
  intro i
  have hinv : M⁻¹ = (sinkhornRatio ψ0 φ0 i)⁻¹ := by
    rw [← hhat0_eq i]
    exact finite_sinkhorn_hatted0_ratio_eq_inv p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys i
  have h := congrArg (fun x : ℝ => x⁻¹) hinv
  simpa [inv_inv] using h.symm

/-- Reverse bounds from the hatted/backward equations and marginal normalizations.

After the forward equations show all left ratios are bounded above by the right maximum, the
backward equation at the maximizing index forces equality throughout the strictly-positive finite
kernel.  The lower-bound conclusion is packaged from exact left/right ratio equalities. -/
theorem finite_sinkhorn_ratio_right_max_le_all {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (jstar : ι)
    (_hright_max : ∀ j, sinkhornRatio ψ1 φ1 j ≤ sinkhornRatio ψ1 φ1 jstar)
    (hleft_upper : ∀ i, sinkhornRatio ψ0 φ0 i ≤ sinkhornRatio ψ1 φ1 jstar) :
    (∀ i, sinkhornRatio ψ1 φ1 jstar ≤ sinkhornRatio ψ0 φ0 i) ∧
    (∀ j, sinkhornRatio ψ1 φ1 jstar ≤ sinkhornRatio ψ1 φ1 j) := by
  let M : ℝ := sinkhornRatio ψ1 φ1 jstar
  have hM_pos : 0 < M := by
    dsimp [M, sinkhornRatio]
    exact div_pos (hψsys.φ1_pos jstar) (hφsys.φ1_pos jstar)
  have hhat0_lower : ∀ i, M⁻¹ ≤ sinkhornRatio ψhat0 φhat0 i := by
    dsimp [M]
    exact finite_sinkhorn_hatted_ratio_lower_from_forward_upper p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys
      (sinkhornRatio ψ1 φ1 jstar) hleft_upper
  have hhat1_star : sinkhornRatio ψhat1 φhat1 jstar = M⁻¹ := by
    dsimp [M]
    exact finite_sinkhorn_hatted1_ratio_eq_inv_at_right_max p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys jstar
  have hhat0_eq : ∀ i, sinkhornRatio ψhat0 φhat0 i = M⁻¹ :=
    finite_sinkhorn_backward_extreme_forces_hatted0_eq p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys
      M jstar hhat0_lower hhat1_star
  have hhat1_eq : ∀ j, sinkhornRatio ψhat1 φhat1 j = M⁻¹ :=
    finite_sinkhorn_backward_hatted_ratio_eq_of_hatted0_eq p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys M hhat0_eq
  have hleft_eq : ∀ i, sinkhornRatio ψ0 φ0 i = M :=
    finite_sinkhorn_left_ratio_eq_from_hatted_eq p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys M hM_pos hhat0_eq
  have hright_eq : ∀ j, sinkhornRatio ψ1 φ1 j = M :=
    finite_sinkhorn_right_ratio_eq_from_hatted_eq p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hφsys hψsys M hM_pos hhat1_eq
  refine ⟨?_, ?_⟩
  · intro i
    exact le_of_eq (hleft_eq i).symm
  · intro j
    exact le_of_eq (hright_eq j).symm

/-- The local maximum-principle bridge for finite Sinkhorn uniqueness.

The proof is split into finite maximum selection, forward weighted averages, hatted/backward
propagation, and marginal inversion.  This wrapper contains only the final `le_antisymm` packaging. -/
theorem finite_sinkhorn_ratio_bridge_all_indices {ι : Type*} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1) :
    ∃ jstar : ι,
      (∀ i, sinkhornRatio ψ0 φ0 i = sinkhornRatio ψ1 φ1 jstar) ∧
      (∀ j, sinkhornRatio ψ1 φ1 j = sinkhornRatio ψ1 φ1 jstar) := by
  obtain ⟨jstar, hright_upper⟩ := finite_sinkhorn_ratio_right_max_exists φ1 ψ1
  have hleft_upper : ∀ i, sinkhornRatio ψ0 φ0 i ≤ sinkhornRatio ψ1 φ1 jstar :=
    finite_sinkhorn_ratio_left_le_right_max p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys jstar hright_upper
  obtain ⟨hleft_lower, hright_lower⟩ :=
    finite_sinkhorn_ratio_right_max_le_all p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys
      jstar hright_upper hleft_upper
  refine ⟨jstar, ?_, ?_⟩
  · intro i
    exact le_antisymm (hleft_upper i) (hleft_lower i)
  · intro j
    exact le_antisymm (hright_upper j) (hright_lower j)

/-- Finite ratio-collapse seam for the uniqueness proof.

The remaining maximum-principle work has been isolated in
`finite_sinkhorn_ratio_bridge_all_indices`.  This theorem handles the empty-index edge case and
packages the nonempty bridge as a positive common ratio. -/
theorem finite_sinkhorn_ratio_extreme_principle {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1) :
    ∃ c : ℝ, 0 < c ∧
      (∀ i, sinkhornRatio ψ0 φ0 i = c) ∧
      (∀ j, sinkhornRatio ψ1 φ1 j = c) := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · haveI : IsEmpty ι := hempty
    refine ⟨1, zero_lt_one, ?_, ?_⟩
    · intro i
      exact isEmptyElim i
    · intro j
      exact isEmptyElim j
  · haveI : Nonempty ι := hnonempty
    obtain ⟨jstar, hratio0, hratio1⟩ :=
      finite_sinkhorn_ratio_bridge_all_indices p q G
        φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys
    refine ⟨sinkhornRatio ψ1 φ1 jstar, ?_, hratio0, hratio1⟩
    exact div_pos (hψsys.φ1_pos jstar) (hφsys.φ1_pos jstar)

/-- Core uniqueness target for finite Schrödinger/Sinkhorn potentials.

This is the genuine Perron--Frobenius / projective-contraction seam: two positive solutions of the
finite Schrödinger system, for strictly positive kernel, have the same left and right potentials up
to one common positive scaling.  The reciprocal scaling of the hatted potentials is an algebraic
consequence proved below from the marginal normalization equations. -/
theorem sinkhorn_potentials_common_scaling {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1) :
    ∃ c : ℝ, 0 < c ∧
      (∀ i, ψ0 i = c * φ0 i) ∧
      (∀ j, ψ1 j = c * φ1 j) := by
  obtain ⟨c, hc, hratio0, hratio1⟩ :=
    finite_sinkhorn_ratio_extreme_principle p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys
  refine ⟨c, hc, ?_, ?_⟩
  · intro i
    have hφ0_ne : φ0 i ≠ 0 := ne_of_gt (hφsys.φ0_pos i)
    calc
      ψ0 i = (ψ0 i / φ0 i) * φ0 i := by field_simp [hφ0_ne]
      _ = sinkhornRatio ψ0 φ0 i * φ0 i := by rfl
      _ = c * φ0 i := by rw [hratio0 i]
  · intro j
    have hφ1_ne : φ1 j ≠ 0 := ne_of_gt (hφsys.φ1_pos j)
    calc
      ψ1 j = (ψ1 j / φ1 j) * φ1 j := by field_simp [hφ1_ne]
      _ = sinkhornRatio ψ1 φ1 j * φ1 j := by rfl
      _ = c * φ1 j := by rw [hratio1 j]

/-- Uniqueness of finite Schrödinger/Sinkhorn potentials up to reciprocal scaling.

The hard part is the common-scaling theorem for the two positive potential pairs.  Once that is
known, the reciprocal scaling of the hatted potentials follows directly from the two marginal
normalization equations and positivity. -/
theorem sinkhorn_potentials_unique_up_to_scaling {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1) :
    ∃ c : ℝ, 0 < c ∧
      (∀ i, ψ0 i = c * φ0 i) ∧
      (∀ i, ψhat0 i = c⁻¹ * φhat0 i) ∧
      (∀ j, ψ1 j = c * φ1 j) ∧
      (∀ j, ψhat1 j = c⁻¹ * φhat1 j) := by
  obtain ⟨c, hc, hψ0, hψ1⟩ :=
    sinkhorn_potentials_common_scaling p q G
      φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys
  refine ⟨c, hc, hψ0, ?_, hψ1, ?_⟩
  · intro i
    have hφ0_ne : φ0 i ≠ 0 := ne_of_gt (hφsys.φ0_pos i)
    have hc_ne : c ≠ 0 := ne_of_gt hc
    have hprod : (c * φ0 i) * ψhat0 i = φ0 i * φhat0 i := by
      calc
        (c * φ0 i) * ψhat0 i = ψ0 i * ψhat0 i := by rw [hψ0 i]
        _ = p i := hψsys.normalize_left i
        _ = φ0 i * φhat0 i := (hφsys.normalize_left i).symm
    have hcancel : c * ψhat0 i = φhat0 i := by
      apply mul_left_cancel₀ hφ0_ne
      calc
        φ0 i * (c * ψhat0 i) = (c * φ0 i) * ψhat0 i := by ring
        _ = φ0 i * φhat0 i := hprod
    calc
      ψhat0 i = c⁻¹ * (c * ψhat0 i) := by
        field_simp [hc_ne]
      _ = c⁻¹ * φhat0 i := by rw [hcancel]
  · intro j
    have hφ1_ne : φ1 j ≠ 0 := ne_of_gt (hφsys.φ1_pos j)
    have hc_ne : c ≠ 0 := ne_of_gt hc
    have hprod : (c * φ1 j) * ψhat1 j = φ1 j * φhat1 j := by
      calc
        (c * φ1 j) * ψhat1 j = ψ1 j * ψhat1 j := by rw [hψ1 j]
        _ = q j := hψsys.normalize_right j
        _ = φ1 j * φhat1 j := (hφsys.normalize_right j).symm
    have hcancel : c * ψhat1 j = φhat1 j := by
      apply mul_left_cancel₀ hφ1_ne
      calc
        φ1 j * (c * ψhat1 j) = (c * φ1 j) * ψhat1 j := by ring
        _ = φ1 j * φhat1 j := hprod
    calc
      ψhat1 j = c⁻¹ * (c * ψhat1 j) := by
        field_simp [hc_ne]
      _ = c⁻¹ * φhat1 j := by rw [hcancel]

end ChenGeorgiouPavon2021
