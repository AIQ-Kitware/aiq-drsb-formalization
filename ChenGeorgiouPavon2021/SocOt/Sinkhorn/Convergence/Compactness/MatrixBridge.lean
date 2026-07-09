/-
# Finite Sinkhorn matrix-normalization bridge

This file connects the four phase-sequence formulation of finite Sinkhorn iterates with the
row/column-normalized positive matrices used in Franklin--Lorenz Section 3.  It is separated from
`ProjectiveLag.lean` so the Birkhoff/Hilbert contraction development can import these bridge lemmas
without depending on the downstream lag assembly.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.RatioSpread

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- The implicit Franklin--Lorenz row-normalized matrix at Sinkhorn step `n`.

In Section 3 of Franklin--Lorenz, the row-normalized matrix `A'_k` has prescribed row sums `p` and
column sums `c^(k)`.  In the phase notation used here, the corresponding matrix has entries
`φhat0Iter (n + 1) i * G i j * φ1Iter n j`. -/
abbrev sinkhornRowNormalizedMatrix {ι : Type*}
    (G : ι → ι → ℝ) (φhat0 φ1 : ι → ℝ) : ι → ι → ℝ :=
  fun i j => φhat0 i * G i j * φ1 j

/-- The implicit row-normalized matrix has row sums `p`. -/
theorem sinkhorn_rowNormalizedMatrix_row_sum {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (n : ℕ) (i : ι) :
    (∑ j, sinkhornRowNormalizedMatrix G (φhat0Iter (n + 1)) (φ1Iter n) i j) = p i := by
  calc
    (∑ j, sinkhornRowNormalizedMatrix G (φhat0Iter (n + 1)) (φ1Iter n) i j)
        = φhat0Iter (n + 1) i * ∑ j, G i j * φ1Iter n j := by
          rw [Finset.mul_sum]
          simp [sinkhornRowNormalizedMatrix, mul_assoc]
    _ = φhat0Iter (n + 1) i * φ0Iter n i := by
          rw [← hiter.forward n i]
    _ = p i := hiter.normalize_left n i

/-- The column sums of the implicit row-normalized matrix are
`φ1Iter n j * φhat1Iter (n + 1) j`, i.e. the Franklin--Lorenz column-error vector before the next
column normalization. -/
theorem sinkhorn_rowNormalizedMatrix_column_sum {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (n : ℕ) (j : ι) :
    (∑ i, sinkhornRowNormalizedMatrix G (φhat0Iter (n + 1)) (φ1Iter n) i j) =
      φhat1Iter (n + 1) j * φ1Iter n j := by
  calc
    (∑ i, sinkhornRowNormalizedMatrix G (φhat0Iter (n + 1)) (φ1Iter n) i j)
        = (∑ i, G i j * φhat0Iter (n + 1) i) * φ1Iter n j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = φhat1Iter (n + 1) j * φ1Iter n j := by
          rw [← hiter.backward (n + 1) j]

/-- The implicit Franklin--Lorenz column-normalized matrix following the row-normalized matrix at
step `n`.

It has entries `φhat0Iter (n + 1) i * G i j * φ1Iter (n + 2) j`, so its column sums are the
prescribed marginal `q`. -/
abbrev sinkhornColumnNormalizedMatrix {ι : Type*}
    (G : ι → ι → ℝ) (φhat0 φ1 : ι → ℝ) : ι → ι → ℝ :=
  fun i j => φhat0 i * G i j * φ1 j

/-- The implicit column-normalized matrix has column sums `q`. -/
theorem sinkhorn_columnNormalizedMatrix_column_sum {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (n : ℕ) (j : ι) :
    (∑ i, sinkhornColumnNormalizedMatrix G (φhat0Iter (n + 1)) (φ1Iter (n + 2)) i j) = q j := by
  calc
    (∑ i, sinkhornColumnNormalizedMatrix G (φhat0Iter (n + 1)) (φ1Iter (n + 2)) i j)
        = (∑ i, G i j * φhat0Iter (n + 1) i) * φ1Iter (n + 2) j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = φhat1Iter (n + 1) j * φ1Iter (n + 2) j := by
          rw [← hiter.backward (n + 1) j]
    _ = q j := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm, mul_left_comm, mul_assoc]
            using hiter.normalize_right (n + 1) j

end ChenGeorgiouPavon2021
