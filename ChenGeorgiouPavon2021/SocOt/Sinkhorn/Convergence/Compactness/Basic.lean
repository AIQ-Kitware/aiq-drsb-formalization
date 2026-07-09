/-
# Basic predicates for finite Sinkhorn compactness

This file contains only data shapes and target predicates shared by the compactness fanout files:
box bounds, raw six-phase preclusters, phase drift, denominator lag drift, and projective/scale lag.
It has no `sorry`s and should remain a stable dependency for all compactness subagents.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Bounds

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Shared box-bounds hypothesis for the four finite Sinkhorn phase sequences. -/
def SinkhornPhaseBoxBounds {ι : Type*}
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ) : Prop :=
  ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
    (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
    (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
    (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
    (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B)

/-- Raw six-phase cluster point along a concrete absolute subsequence.

This is the honest output of bounded finite-dimensional compactness.  The successor phases have
separate limit names because boundedness alone cannot force
`φhat0Iter (subseq n)` and `φhat0Iter (subseq n + 1)` to converge to the same function, and likewise
for `φ1Iter`. -/
structure IsFiniteSinkhornPhasePreclusterAlong {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ) : Prop where
  strict_mono : StrictMono subseq
  tendsto_φ0 : Filter.Tendsto (fun n => φ0Iter (subseq n)) Filter.atTop (nhds ψ0)
  tendsto_φhat0 : Filter.Tendsto (fun n => φhat0Iter (subseq n)) Filter.atTop (nhds ψhat0)
  tendsto_φhat0_succ :
    Filter.Tendsto (fun n => φhat0Iter (subseq n + 1)) Filter.atTop (nhds ψhat0Succ)
  tendsto_φ1 : Filter.Tendsto (fun n => φ1Iter (subseq n)) Filter.atTop (nhds ψ1)
  tendsto_φ1_succ :
    Filter.Tendsto (fun n => φ1Iter (subseq n + 1)) Filter.atTop (nhds ψ1Succ)
  tendsto_φhat1 : Filter.Tendsto (fun n => φhat1Iter (subseq n)) Filter.atTop (nhds ψhat1)
  positive :
    (∀ i, 0 < ψ0 i) ∧
    (∀ i, 0 < ψhat0 i) ∧
    (∀ i, 0 < ψhat0Succ i) ∧
    (∀ j, 0 < ψ1 j) ∧
    (∀ j, 0 < ψ1Succ j) ∧
    (∀ j, 0 < ψhat1 j)

/-- Vanishing drift target for the two mixed phases in the phase-compatible cluster predicate. -/
abbrev SinkhornPhaseDriftZeroAlong {ι : Type*}
    (φhat0Iter φ1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
      (fun n => fun i => φhat0Iter (subseq n + 1) i - φhat0Iter (subseq n) i)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun n => fun j => φ1Iter (subseq n + 1) j - φ1Iter (subseq n) j)
      Filter.atTop (nhds 0)

/-- Lag-drift target for the denominator phases that control the mixed phases.

For `k > 0`, the Sinkhorn normalization equations rewrite
`φhat0Iter (k + 1)` and `φhat0Iter k` using the denominators `φ0Iter k` and
`φ0Iter (k - 1)`, and similarly rewrite `φ1Iter (k + 1)` and `φ1Iter k` using
`φhat1Iter k` and `φhat1Iter (k - 1)`.  Thus the phase-drift theorem naturally
factors through vanishing lag drift for these denominator phases. -/
abbrev SinkhornDenominatorLagDriftZeroAlong {ι : Type*}
    (φ0Iter φhat1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
      (fun n => fun i => φ0Iter (subseq n) i - φ0Iter ((subseq n).pred) i)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun n => fun j => φhat1Iter (subseq n) j - φhat1Iter ((subseq n).pred) j)
      Filter.atTop (nhds 0)

/-- Projective lag collapse for one positive finite phase.

The cross-product component says consecutive denominator vectors are becoming projectively parallel.
It deliberately does not fix the scalar degree of freedom. -/
abbrev SinkhornPhaseProjectiveLagZeroAlong {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
    (fun n => fun ij : ι × ι =>
      u (subseq n) ij.1 * u ((subseq n).pred) ij.2 -
        u (subseq n) ij.2 * u ((subseq n).pred) ij.1)
    Filter.atTop (nhds (0 : ι × ι → ℝ))

/-- Scale lag collapse for one finite phase, stated as total-mass drift. -/
abbrev SinkhornPhaseScaleLagZeroAlong {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  Filter.Tendsto
    (fun n => (∑ i, u (subseq n) i) - ∑ i, u ((subseq n).pred) i)
    Filter.atTop (nhds (0 : ℝ))

/-- Projective-and-scale lag collapse for one positive finite phase.

The cross-product component says consecutive denominator vectors are becoming projectively parallel;
the total-mass component fixes the remaining scalar degree of freedom.  Together, under a uniform
positive finite box, these should imply ordinary coordinate lag drift. -/
abbrev SinkhornPhaseProjectiveScaleLagZeroAlong {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  SinkhornPhaseProjectiveLagZeroAlong u subseq ∧ SinkhornPhaseScaleLagZeroAlong u subseq

/-- Projective lag collapse for the two denominator phases. -/
abbrev SinkhornDenominatorProjectiveLagZeroAlong {ι : Type*} [Fintype ι]
    (φ0Iter φhat1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  SinkhornPhaseProjectiveLagZeroAlong φ0Iter subseq ∧
    SinkhornPhaseProjectiveLagZeroAlong φhat1Iter subseq

/-- Projective-and-scale lag collapse for the two denominator phases. -/
abbrev SinkhornDenominatorProjectiveScaleLagZeroAlong {ι : Type*} [Fintype ι]
    (φ0Iter φhat1Iter : ℕ → ι → ℝ) (subseq : ℕ → ℕ) : Prop :=
  SinkhornPhaseProjectiveScaleLagZeroAlong φ0Iter subseq ∧
    SinkhornPhaseProjectiveScaleLagZeroAlong φhat1Iter subseq


end ChenGeorgiouPavon2021
