/-
# Generic finite weighted-average lemmas for the Sinkhorn ratio proof

This file contains the ordered-ring weighted-average facts used by the finite Sinkhorn maximum
principle.  It is deliberately independent of the Sinkhorn equations so a follow-on proof agent can
work on the remaining strict-equality lemma without touching the matrix-system wrappers.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.FiniteSystem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Generic finite weighted-average inequality needed by the forward ratio bound.

This is pure ordered-ring algebra over a finite type: if all sample values are bounded by `M` and
the weights are nonnegative with positive total `denom`, then the weighted average is bounded by
`M`.  It should be reusable outside Sinkhorn. -/
theorem finite_weighted_average_le_of_nonneg {ι : Type*} [Fintype ι]
    (w r : ι → ℝ) (M denom : ℝ)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hdenom_pos : 0 < denom)
    (hdenom : denom = ∑ j, w j)
    (hr_le : ∀ j, r j ≤ M) :
    (∑ j, w j * r j) / denom ≤ M := by
  classical
  have hsum_le : (∑ j, w j * r j) ≤ ∑ j, w j * M := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact mul_le_mul_of_nonneg_left (hr_le j) (hw_nonneg j)
  have hsum_le' : (∑ j, w j * r j) ≤ denom * M := by
    simpa [hdenom, Finset.sum_mul] using hsum_le
  rw [div_le_iff₀ hdenom_pos]
  nlinarith [hsum_le']

/-- Generic lower-bound version of the finite weighted-average inequality.

If all sample values are bounded below by `m`, and the weights are nonnegative with positive total
`denom`, then the finite weighted average is also bounded below by `m`. -/
theorem finite_weighted_average_ge_of_nonneg {ι : Type*} [Fintype ι]
    (w r : ι → ℝ) (m denom : ℝ)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hdenom_pos : 0 < denom)
    (hdenom : denom = ∑ j, w j)
    (hr_ge : ∀ j, m ≤ r j) :
    m ≤ (∑ j, w j * r j) / denom := by
  classical
  have hsum_ge : (∑ j, w j * m) ≤ ∑ j, w j * r j := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact mul_le_mul_of_nonneg_left (hr_ge j) (hw_nonneg j)
  have hsum_ge' : denom * m ≤ ∑ j, w j * r j := by
    simpa [hdenom, Finset.sum_mul] using hsum_ge
  rw [le_div_iff₀ hdenom_pos]
  nlinarith [hsum_ge']

/-- Equality in a strictly positive finite weighted average at a lower bound.

If every sample value is at least `m`, every weight is strictly positive, and the weighted average
is exactly `m`, then every sample value must be exactly `m`.  This is the pure ordered-algebra
maximum-principle seam behind finite Sinkhorn uniqueness. -/
theorem finite_weighted_average_eq_lower_forces_pointwise {ι : Type*} [Fintype ι]
    (w r : ι → ℝ) (m denom : ℝ)
    (hw_pos : ∀ i, 0 < w i)
    (hdenom_pos : 0 < denom)
    (hdenom : denom = ∑ i, w i)
    (hr_ge : ∀ i, m ≤ r i)
    (havg_eq : (∑ i, w i * r i) / denom = m) :
    ∀ i, r i = m := by
  classical
  have hnum_eq : (∑ i, w i * r i) = denom * m := by
    have hmul := congrArg (fun x : ℝ => x * denom) havg_eq
    field_simp [ne_of_gt hdenom_pos] at hmul
    nlinarith
  have hgap_nonneg : ∀ i, 0 ≤ w i * (r i - m) := by
    intro i
    exact mul_nonneg (le_of_lt (hw_pos i)) (sub_nonneg.mpr (hr_ge i))
  have hgap_sum_zero : (∑ i, w i * (r i - m)) = 0 := by
    calc
      (∑ i, w i * (r i - m)) = ∑ i, (w i * r i - w i * m) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      _ = (∑ i, w i * r i) - ∑ i, w i * m := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i, w i * r i) - (∑ i, w i) * m := by
        rw [Finset.sum_mul]
      _ = 0 := by
        rw [hnum_eq, ← hdenom]
        ring
  intro i
  have hterm_le_sum : w i * (r i - m) ≤ ∑ k, w k * (r k - m) := by
    exact Finset.single_le_sum (fun k _hk => hgap_nonneg k) (Finset.mem_univ i)
  have hterm_le_zero : w i * (r i - m) ≤ 0 := by
    simpa [hgap_sum_zero] using hterm_le_sum
  have hterm_eq_zero : w i * (r i - m) = 0 := by
    exact le_antisymm hterm_le_zero (hgap_nonneg i)
  have hgap_zero : r i - m = 0 := by
    rcases mul_eq_zero.mp hterm_eq_zero with hw_zero | hgap_zero
    · exact False.elim ((ne_of_gt (hw_pos i)) hw_zero)
    · exact hgap_zero
  nlinarith


end ChenGeorgiouPavon2021
