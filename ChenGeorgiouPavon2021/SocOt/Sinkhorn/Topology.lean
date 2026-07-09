/-
# Finite-function topology support for Sinkhorn convergence

This module isolates the generic topology/order lemmas used by the finite Sinkhorn convergence
capstone.  These lemmas are intentionally independent of the Sinkhorn equations: they say how
finite-dimensional convergence can be proved by excluding bad subsequences and using unique
subsequential cluster points.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Ratio

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- If the absolute composed subsequence `subseq (subsub n)` is strictly increasing, then the
inner index selector `subsub` is cofinal.  This is the small order-theoretic bridge needed by the
bad-subsequence compactness argument: a bad outer subsequence remains bad after passing to a
cofinal further subsequence. -/
theorem sinkhorn_subsub_tendsto_atTop_of_strictMono_comp
    (subseq subsub : ℕ → ℕ)
    (_hsubseq : StrictMono subseq)
    (_hcomp : StrictMono (fun n => subseq (subsub n))) :
    Filter.Tendsto subsub Filter.atTop Filter.atTop := by
  sorry

/-- Coordinatewise convergence implies convergence in the finite function space.

This is the product-topology bridge behind the bad-coordinate extraction.  For finite `ι`, a sequence
in `ι → ℝ` converges exactly when all scalar coordinate projections converge. -/
theorem finite_function_tendsto_of_coordinate_tendsto {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hcoord : ∀ i : ι, Filter.Tendsto (fun n => x n i) Filter.atTop (nhds (xLim i))) :
    Filter.Tendsto x Filter.atTop (nhds xLim) := by
  exact tendsto_pi_nhds.2 hcoord

/-- Scalar nonconvergence at `atTop` produces a frequently bad epsilon-neighborhood.

This is the one-dimensional sequential-topology core used by the finite-product bad-coordinate
argument. -/
theorem scalar_not_tendsto_has_frequently_bad_epsilon
    (x : ℕ → ℝ) (xLim : ℝ)
    (hnot : ¬ Filter.Tendsto x Filter.atTop (nhds xLim)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |x n - xLim| := by
  rw [Metric.tendsto_atTop] at hnot
  push_neg at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  refine ⟨ε, hε, ?_⟩
  intro N
  obtain ⟨n, hnN, hbad⟩ := hfreq N
  refine ⟨n, hnN, ?_⟩
  simpa [Real.dist_eq] using hbad

/-- If a finite-function sequence does not converge, then some coordinate is frequently
separated from the candidate limit.

This is now a wrapper around two purer topology seams: finite product convergence is coordinatewise,
and scalar nonconvergence produces a frequently bad epsilon-neighborhood. -/
theorem finite_function_not_tendsto_has_frequently_bad_coordinate {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hnot : ¬ Filter.Tendsto x Filter.atTop (nhds xLim)) :
    ∃ i : ι, ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |x n i - xLim i| := by
  by_contra hnone
  have hcoord : ∀ i : ι, Filter.Tendsto (fun n => x n i) Filter.atTop (nhds (xLim i)) := by
    intro i
    by_contra hnot_i
    obtain ⟨ε, hε, hfreq⟩ :=
      scalar_not_tendsto_has_frequently_bad_epsilon (fun n => x n i) (xLim i) hnot_i
    exact hnone ⟨i, ε, hε, hfreq⟩
  exact hnot (finite_function_tendsto_of_coordinate_tendsto x xLim hcoord)

/-- A scalar coordinate that is frequently bad admits a strictly increasing bad subsequence. -/
theorem finite_function_frequently_bad_coordinate_subsequence {ι : Type*}
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ) (i : ι) (ε : ℝ)
    (_hε : 0 < ε)
    (_hfreq : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |x n i - xLim i|) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∀ k : ℕ, ε ≤ |x (subseq k) i - xLim i| := by
  sorry

/-- A bad coordinate subsequence stays nonconvergent after every cofinal further subsequence. -/
theorem finite_function_bad_coordinate_blocks_cofinal_convergence {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ) (i : ι) (ε : ℝ)
    (_hε : 0 < ε) (subseq : ℕ → ℕ)
    (_hbad : ∀ k : ℕ, ε ≤ |x (subseq k) i - xLim i|)
    (subsub : ℕ → ℕ) (_hsubsub : Filter.Tendsto subsub Filter.atTop Filter.atTop) :
    ¬ Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim) := by
  sorry

/-- A nonconvergent finite-function sequence has a bad subsequence that no cofinal further
subsequence can make converge to the candidate limit.

This packages the standard contradiction setup used by the unique-cluster convergence theorem. -/
theorem finite_function_not_tendsto_produces_bad_subsequence {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hnot : ¬ Filter.Tendsto x Filter.atTop (nhds xLim)) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∀ subsub : ℕ → ℕ, Filter.Tendsto subsub Filter.atTop Filter.atTop →
        ¬ Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim) := by
  obtain ⟨i, ε, hε, hfreq⟩ := finite_function_not_tendsto_has_frequently_bad_coordinate x xLim hnot
  obtain ⟨subseq, hsubseq_mono, hbad⟩ :=
    finite_function_frequently_bad_coordinate_subsequence x xLim i ε hε hfreq
  refine ⟨subseq, hsubseq_mono, ?_⟩
  intro subsub hsubsub
  exact finite_function_bad_coordinate_blocks_cofinal_convergence
    x xLim i ε hε subseq hbad subsub hsubsub

/-- Generic finite-function topology seam: if every subsequence has a cofinal further subsequence
converging to the same candidate limit, then the original finite-dimensional sequence converges.

This theorem is now only the final contradiction wrapper.  The genuinely hard topology has been split
into the bad-coordinate extraction, bad-subsequence construction, and cofinal-obstruction lemmas above. -/
theorem finite_function_tendsto_of_unique_subseq_cluster {ι : Type*} [Fintype ι]
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hsubseq_cluster : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ subsub : ℕ → ℕ,
        Filter.Tendsto subsub Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim)) :
    Filter.Tendsto x Filter.atTop (nhds xLim) := by
  by_contra hnot
  obtain ⟨subseq, hsubseq_mono, hbad⟩ :=
    finite_function_not_tendsto_produces_bad_subsequence x xLim hnot
  obtain ⟨subsub, hsubsub, hconv⟩ := hsubseq_cluster subseq hsubseq_mono
  exact hbad subsub hsubsub hconv

end ChenGeorgiouPavon2021
