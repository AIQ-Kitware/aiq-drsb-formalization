/-
# Sequence Gaussian Cameron--Martin: finite and total energies

This module contains the finite-prefix, range-partial, and total
Cameron--Martin energy bookkeeping for iid Gaussian sequences.
-/

import ForMathlib.MeasureTheory.GaussianCameronMartin.Basic

set_option autoImplicit false

open MeasureTheory Real InformationTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace ForMathlib.MeasureTheory

/-- Finite-prefix Cameron--Martin energy for the deterministic shift `c`, restricted to
the first `n + 1` sequence coordinates.  This is the finite-dimensional quantity that
converges to `½‖c‖²` in the eventual sequence-model theorem. -/
noncomputable def cmPrefixEnergy (c : RealSeq) (n : ℕ) : ℝ :=
  2⁻¹ * ∑ i : Finset.Iic n, (prefixRestrict n c i) ^ 2

/-- Finite-prefix Cameron--Martin energy is nonnegative. -/
theorem cmPrefixEnergy_nonneg (c : RealSeq) (n : ℕ) :
    0 ≤ cmPrefixEnergy c n := by
  unfold cmPrefixEnergy
  positivity

/-- Total sequence Cameron--Martin energy, written as one half of the square series.
This is the target value for the sequence-model Cameron--Martin identity when the
shift vector is square-summable. -/
noncomputable def cmTotalEnergy (c : RealSeq) : ℝ :=
  2⁻¹ * ∑' n : ℕ, c n ^ 2

/-- Range-indexed partial Cameron--Martin energies.  This spelling intentionally uses
`Finset.sum` directly.  It sums the first `n` coordinates, i.e. indices in
`Finset.range n`. -/
noncomputable def cmPartialEnergy (c : RealSeq) (n : ℕ) : ℝ :=
  2⁻¹ * (Finset.range n).sum (fun i => c i ^ 2)

/-- Total sequence Cameron--Martin energy is nonnegative. -/
theorem cmTotalEnergy_nonneg (c : RealSeq) :
    0 ≤ cmTotalEnergy c := by
  unfold cmTotalEnergy
  exact mul_nonneg (by positivity) (tsum_nonneg (fun n => sq_nonneg (c n)))

/-- Range-indexed partial Cameron--Martin energies are nonnegative. -/
theorem cmPartialEnergy_nonneg (c : RealSeq) (n : ℕ) :
    0 ≤ cmPartialEnergy c n := by
  unfold cmPartialEnergy
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => sq_nonneg (c i)))

/-- The empty range has zero Cameron--Martin energy. -/
theorem cmPartialEnergy_zero (c : RealSeq) :
    cmPartialEnergy c 0 = 0 := by
  simp [cmPartialEnergy]

/-- Successor equation for range-indexed partial Cameron--Martin energies. -/
theorem cmPartialEnergy_succ (c : RealSeq) (n : ℕ) :
    cmPartialEnergy c (n + 1) = cmPartialEnergy c n + 2⁻¹ * c n ^ 2 := by
  unfold cmPartialEnergy
  rw [Finset.sum_range_succ]
  ring

/-- Range-indexed partial Cameron--Martin energies are increasing one step at a time. -/
theorem cmPartialEnergy_le_succ (c : RealSeq) (n : ℕ) :
    cmPartialEnergy c n ≤ cmPartialEnergy c (n + 1) := by
  rw [cmPartialEnergy_succ]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg (c n)))

/-- Pure-series convergence of range-indexed partial Cameron--Martin energies.
This is the square-summable side of the eventual sequence-model identity; a later bridge
identifies the `Finset.Iic n` prefix energy with these shifted range partial sums. -/
theorem cmPartialEnergy_tendsto_total_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    Tendsto (cmPartialEnergy c) atTop (nhds (cmTotalEnergy c)) := by
  unfold cmPartialEnergy cmTotalEnergy
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((hsum.hasSum.tendsto_sum_nat).const_mul (2⁻¹))

/-- Lower intervals in `ℕ` have the same sum as the corresponding successor range.
This small finite-set bridge keeps the sequence-model Cameron--Martin file from depending
on a particular spelling of the Mathlib `Iic = range` theorem. -/
theorem sum_Iic_eq_sum_range_succ (f : ℕ → ℝ) (n : ℕ) :
    (Finset.Iic n).sum f = (Finset.range (n + 1)).sum f := by
  have hIic : Finset.Iic n = Finset.range (n + 1) := by
    ext i
    simp
  rw [hIic]

/-- The `Finset.Iic n` finite-prefix energy is the same as the range-indexed
partial energy through coordinate `n`, i.e. the first `n + 1` coordinates.  This
is the pure finite-set bridge between the Gaussian-prefix layer and the ordinary
series API on `ℕ`. -/
theorem cmPrefixEnergy_eq_cmPartialEnergy_succ (c : RealSeq) (n : ℕ) :
    cmPrefixEnergy c n = cmPartialEnergy c (n + 1) := by
  unfold cmPrefixEnergy cmPartialEnergy prefixRestrict
  calc
    2⁻¹ * (∑ i : Finset.Iic n, c ↑i ^ 2)
        = 2⁻¹ * (Finset.Iic n).sum (fun i => c i ^ 2) := by
          congr 1
          simpa using
            (Finset.sum_attach (s := Finset.Iic n) (f := fun i : ℕ => c i ^ 2))
    _ = 2⁻¹ * (Finset.range (n + 1)).sum (fun i => c i ^ 2) := by
          rw [sum_Iic_eq_sum_range_succ]

/-- Finite-prefix energies are monotone in the prefix length. -/
theorem cmPrefixEnergy_le_succ (c : RealSeq) (n : ℕ) :
    cmPrefixEnergy c n ≤ cmPrefixEnergy c (n + 1) := by
  rw [cmPrefixEnergy_eq_cmPartialEnergy_succ c n,
    cmPrefixEnergy_eq_cmPartialEnergy_succ c (n + 1)]
  exact cmPartialEnergy_le_succ c (n + 1)

/-- If range-indexed partial energies are unbounded, then the finite-prefix energies are
unbounded as well.  The only missing range index is `0`, whose partial energy is `0`; all
successor range indices are prefix energies by `cmPrefixEnergy_eq_cmPartialEnergy_succ`. -/
theorem not_bddAbove_cmPrefixEnergy_of_not_bddAbove_cmPartialEnergy (c : RealSeq)
    (hunbdd : ¬ BddAbove (Set.range (cmPartialEnergy c))) :
    ¬ BddAbove (Set.range (cmPrefixEnergy c)) := by
  intro hpre
  rcases hpre with ⟨B, hB⟩
  refine hunbdd ⟨max B 0, ?_⟩
  intro y hy
  rcases hy with ⟨n, rfl⟩
  cases n with
  | zero =>
      rw [cmPartialEnergy_zero]
      exact le_max_right B 0
  | succ n =>
      rw [← cmPrefixEnergy_eq_cmPartialEnergy_succ c n]
      exact le_trans (hB ⟨n, rfl⟩) (le_max_left B 0)

end ForMathlib.MeasureTheory
