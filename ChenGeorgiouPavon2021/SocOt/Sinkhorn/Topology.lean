/-
# Product-topology support for Sinkhorn convergence

This module isolates the generic topology/order lemmas used by the finite Sinkhorn convergence
capstone.  These lemmas are intentionally independent of the Sinkhorn equations: they say how
convergence in `ι → ℝ` can be proved by excluding bad subsequences and using unique subsequential
cluster points.  They hold for arbitrary `ι` — the caller's `ι` happens to be finite.
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
    (hsubseq : StrictMono subseq)
    (hcomp : StrictMono (fun n => subseq (subsub n))) :
    Filter.Tendsto subsub Filter.atTop Filter.atTop := by
  have hsubsub_strict : StrictMono subsub := by
    intro a b hab
    by_contra hnot
    have hle : subsub b ≤ subsub a := Nat.le_of_not_gt hnot
    have hseq_le : subseq (subsub b) ≤ subseq (subsub a) := hsubseq.monotone hle
    have hseq_lt : subseq (subsub a) < subseq (subsub b) := hcomp hab
    exact (not_lt_of_ge hseq_le) hseq_lt
  exact hsubsub_strict.tendsto_atTop

/-- Coordinatewise convergence implies convergence in the function space.

This is the product-topology bridge behind the bad-coordinate extraction: a sequence in `ι → ℝ`
converges when all scalar coordinate projections do.  No finiteness of `ι` is needed — convergence in
the product topology *is* coordinatewise convergence — even though the Sinkhorn caller has `ι` finite. -/
theorem pi_tendsto_of_coordinate_tendsto {ι : Type*}
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
  push Not at hnot
  obtain ⟨ε, hε, hbad⟩ := hnot
  refine ⟨ε, hε, ?_⟩
  intro N
  obtain ⟨n, hn, hdist⟩ := hbad N
  refine ⟨n, hn, ?_⟩
  simpa [Real.dist_eq] using hdist

/-- If a sequence in `ι → ℝ` does not converge, then some coordinate is frequently separated from
the candidate limit.

A wrapper around two purer topology seams: product convergence is coordinatewise (for any `ι`), and
scalar nonconvergence produces a frequently bad epsilon-neighborhood. -/
theorem pi_not_tendsto_has_frequently_bad_coordinate {ι : Type*}
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
  exact hnot (pi_tendsto_of_coordinate_tendsto x xLim hcoord)

/-- A purely arithmetic extraction lemma: a property that occurs arbitrarily far out admits
an increasing subsequence along which it holds.

The proof uses recursive choice: choose `n₀` with `P n₀`, then choose
`nₖ₊₁ ≥ nₖ + 1` with `P nₖ₊₁`. -/
theorem nat_strictMono_subsequence_of_frequently
    (P : ℕ → Prop)
    (hfreq : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ ∀ k : ℕ, P (subseq k) := by
  classical
  let pick : ℕ → ℕ := fun N => Classical.choose (hfreq N)
  have hpick_ge : ∀ N : ℕ, N ≤ pick N := by
    intro N
    exact (Classical.choose_spec (hfreq N)).1
  have hpick_P : ∀ N : ℕ, P (pick N) := by
    intro N
    exact (Classical.choose_spec (hfreq N)).2
  let subseq : ℕ → ℕ := fun k =>
    Nat.recOn k (pick 0) (fun _ prev => pick (prev + 1))
  have hstep : ∀ k : ℕ, subseq k < subseq (k + 1) := by
    intro k
    have hge : subseq k + 1 ≤ pick (subseq k + 1) := hpick_ge (subseq k + 1)
    have hrec : subseq (k + 1) = pick (subseq k + 1) := by
      simp [subseq]
    rw [hrec]
    exact Nat.lt_of_succ_le hge
  have hmono : StrictMono subseq := strictMono_nat_of_lt_succ hstep
  have hP : ∀ k : ℕ, P (subseq k) := by
    intro k
    cases k with
    | zero =>
        simpa [subseq] using hpick_P 0
    | succ k =>
        have hrec : subseq (k + 1) = pick (subseq k + 1) := by
          simp [subseq]
        rw [hrec]
        exact hpick_P (subseq k + 1)
  exact ⟨subseq, hmono, hP⟩

/-- A scalar coordinate that is frequently bad admits a strictly increasing bad subsequence. -/
theorem pi_frequently_bad_coordinate_subsequence {ι : Type*}
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ) (i : ι) (ε : ℝ)
    (_hε : 0 < ε)
    (hfreq : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |x n i - xLim i|) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∀ k : ℕ, ε ≤ |x (subseq k) i - xLim i| := by
  exact nat_strictMono_subsequence_of_frequently
    (fun n => ε ≤ |x n i - xLim i|) hfreq

/-- A scalar sequence that stays outside a fixed epsilon-neighborhood cannot converge to its target.

This is the one-dimensional obstruction used by the finite-function bad-coordinate theorem.  It is
separated from the finite-function wrapper so the remaining proof is just the metric definition of
convergence on `ℝ`. -/
theorem scalar_bad_epsilon_blocks_tendsto
    (x : ℕ → ℝ) (xLim : ℝ) (ε : ℝ)
    (hε : 0 < ε)
    (hbad : ∀ k : ℕ, ε ≤ |x k - xLim|) :
    ¬ Filter.Tendsto x Filter.atTop (nhds xLim) := by
  intro hconv
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv ε hε
  have hnear : |x N - xLim| < ε := by
    simpa [Real.dist_eq] using hN N le_rfl
  exact (not_le_of_gt hnear) (hbad N)

/-- A bad coordinate subsequence stays nonconvergent after every cofinal further subsequence.

The function-space part is only projection to the bad coordinate, so `ι` need not be finite.  The
scalar metric obstruction is isolated in `scalar_bad_epsilon_blocks_tendsto`. -/
theorem pi_bad_coordinate_blocks_cofinal_convergence {ι : Type*}
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ) (i : ι) (ε : ℝ)
    (hε : 0 < ε) (subseq : ℕ → ℕ)
    (hbad : ∀ k : ℕ, ε ≤ |x (subseq k) i - xLim i|)
    (subsub : ℕ → ℕ) (_hsubsub : Filter.Tendsto subsub Filter.atTop Filter.atTop) :
    ¬ Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim) := by
  intro hconv
  have hcoord : Filter.Tendsto (fun n => x (subseq (subsub n)) i) Filter.atTop (nhds (xLim i)) := by
    exact ((continuous_apply i).tendsto xLim).comp hconv
  exact scalar_bad_epsilon_blocks_tendsto
    (fun n => x (subseq (subsub n)) i) (xLim i) ε hε (fun n => hbad (subsub n)) hcoord

/-- A nonconvergent sequence in `ι → ℝ` has a bad subsequence that no cofinal further
subsequence can make converge to the candidate limit.

This packages the standard contradiction setup used by the unique-cluster convergence theorem. -/
theorem pi_not_tendsto_produces_bad_subsequence {ι : Type*}
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hnot : ¬ Filter.Tendsto x Filter.atTop (nhds xLim)) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∀ subsub : ℕ → ℕ, Filter.Tendsto subsub Filter.atTop Filter.atTop →
        ¬ Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim) := by
  obtain ⟨i, ε, hε, hfreq⟩ := pi_not_tendsto_has_frequently_bad_coordinate x xLim hnot
  obtain ⟨subseq, hsubseq_mono, hbad⟩ :=
    pi_frequently_bad_coordinate_subsequence x xLim i ε hε hfreq
  refine ⟨subseq, hsubseq_mono, ?_⟩
  intro subsub hsubsub
  exact pi_bad_coordinate_blocks_cofinal_convergence
    x xLim i ε hε subseq hbad subsub hsubsub

/-- Generic finite-function topology seam: if every subsequence has a cofinal further subsequence
converging to the same candidate limit, then the original sequence converges.  This is the
subsequence principle; it needs no finiteness of `ι`, nor any compactness.

The proof combines the bad-coordinate extraction, bad-subsequence construction, and
cofinal-obstruction lemmas above in a final contradiction argument. -/
theorem pi_tendsto_of_unique_subseq_cluster {ι : Type*}
    (x : ℕ → ι → ℝ) (xLim : ι → ℝ)
    (hsubseq_cluster : ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ subsub : ℕ → ℕ,
        Filter.Tendsto subsub Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => x (subseq (subsub n))) Filter.atTop (nhds xLim)) :
    Filter.Tendsto x Filter.atTop (nhds xLim) := by
  by_contra hnot
  obtain ⟨subseq, hsubseq_mono, hbad⟩ :=
    pi_not_tendsto_produces_bad_subsequence x xLim hnot
  obtain ⟨subsub, hsubsub, hconv⟩ := hsubseq_cluster subseq hsubseq_mono
  exact hbad subsub hsubsub hconv

end ChenGeorgiouPavon2021
