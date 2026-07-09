/-
# Phase-compatible compactness seams for finite Sinkhorn convergence

This file isolates bounded finite-dimensional subsequence extraction.  The pure compactness theorem
only produces six possibly distinct phase limits: current `φhat0`, successor `φhat0`, current `φ1`,
and successor `φ1` need not agree for an arbitrary bounded sequence.  The remaining compatibility
seam is therefore stated separately and explicitly uses the Sinkhorn iterate structure.
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

/-- Pure bounded finite-dimensional extraction for every outer subsequence.

This is the true C2 compactness theorem.  It is pure topology/diagonal extraction: after choosing
any outer subsequence, one can pass to a further subsequence where all six bounded phase streams have
limits.  It deliberately does **not** assert phase compatibility of successor limits. -/
theorem sinkhorn_outer_phase_precluster_subsequence_from_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ),
        IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 := by
  sorry

/-- One-cluster corollary of the outer-subsequence raw compactness theorem. -/
theorem sinkhorn_phase_precluster_subsequence_of_bounds {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ),
      IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 := by
  have hid : StrictMono (fun n : ℕ => n) := by
    intro a b hab
    exact hab
  obtain ⟨subseq, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, hpre⟩ :=
    sinkhorn_outer_phase_precluster_subsequence_from_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds (fun n : ℕ => n) hid
  exact ⟨subseq, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, hpre⟩

/-- Convert a raw six-phase precluster into the phase-compatible cluster predicate once the two
successor limits are known to agree with their current-phase limits. -/
theorem sinkhorn_cluster_along_of_precluster_successor_eq {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hψhat0 : ψhat0Succ = ψhat0) (hψ1 : ψ1Succ = ψ1) :
    IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1 := by
  exact {
    strict_mono := hpre.strict_mono
    tendsto_φ0 := hpre.tendsto_φ0
    tendsto_φhat0 := hpre.tendsto_φhat0
    tendsto_φhat0_succ := by
      simpa [hψhat0] using hpre.tendsto_φhat0_succ
    tendsto_φ1 := hpre.tendsto_φ1
    tendsto_φ1_succ := by
      simpa [hψ1] using hpre.tendsto_φ1_succ
    tendsto_φhat1 := hpre.tendsto_φhat1
    positive := ⟨hpre.positive.1, hpre.positive.2.1,
      hpre.positive.2.2.2.1, hpre.positive.2.2.2.2.2⟩ }

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

/-- Projective/asymptotic-regularity core for the denominator phases.

This is the first genuinely hard Sinkhorn-dynamical seam.  It should be proved using the positive
kernel, the finite box bounds, and the two alternating positive linear maps, for example via
Hilbert-projective contraction, monotone-diameter decay, or an equivalent energy argument.  It only
controls projective shape; scale control is separated below. -/
theorem sinkhorn_denominator_projective_lag_tendsto_zero_from_gauge_iterates {ι : Type*}
    [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq := by
  sorry

/-- The `φ0` denominator scale lag is fixed exactly by the gauge normalization. -/
theorem sinkhorn_phi0_scale_lag_zero_from_gauge {ι : Type*} [Fintype ι]
    (φ0Iter _φhat0Iter _φ1Iter _φhat1Iter : ℕ → ι → ℝ)
    (φ0 _φhat0 _φ1 _φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter _φhat0Iter _φ1Iter _φhat1Iter
      φ0 _φhat0 _φ1 _φhat1) :
    SinkhornPhaseScaleLagZeroAlong φ0Iter subseq := by
  change Filter.Tendsto
    (fun n => (∑ i, φ0Iter (subseq n) i) - ∑ i, φ0Iter ((subseq n).pred) i)
    Filter.atTop (nhds (0 : ℝ))
  have hzero :
      (fun n => (∑ i, φ0Iter (subseq n) i) - ∑ i, φ0Iter ((subseq n).pred) i) =
        fun _ : ℕ => (0 : ℝ) := by
    funext n
    rw [hgauge.left_total (subseq n), hgauge.left_total ((subseq n).pred), sub_self]
  rw [hzero]
  exact (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))

/-- Scale/asymptotic-regularity core for the `φhat1` denominator phase.

The `φ0` scale drift is exactly zero by the gauge.  The remaining scale work is the total-mass drift
for `φhat1`; this should follow from the Sinkhorn equations, projective lag collapse, and the fixed
left gauge. -/
theorem sinkhorn_phihat1_scale_lag_tendsto_zero_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (_hproj : SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq) :
    SinkhornPhaseScaleLagZeroAlong φhat1Iter subseq := by
  sorry

/-- Projective/asymptotic-regularity plus scale control for the denominator phases.

This wrapper preserves the earlier projective-scale theorem name while exposing the two real
subproblems: projective shape collapse for both denominator phases, and scale control for the
non-gauge-fixed `φhat1` denominator.  The `φ0` scale component is discharged directly by the gauge. -/
theorem sinkhorn_denominator_projective_scale_lag_tendsto_zero_from_gauge_iterates {ι : Type*}
    [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    SinkhornDenominatorProjectiveScaleLagZeroAlong φ0Iter φhat1Iter subseq := by
  have hproj : SinkhornDenominatorProjectiveLagZeroAlong φ0Iter φhat1Iter subseq :=
    sinkhorn_denominator_projective_lag_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  have hφ0scale : SinkhornPhaseScaleLagZeroAlong φ0Iter subseq :=
    sinkhorn_phi0_scale_lag_zero_from_gauge
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq hgauge
  have hφhat1scale : SinkhornPhaseScaleLagZeroAlong φhat1Iter subseq :=
    sinkhorn_phihat1_scale_lag_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre hproj
  exact ⟨⟨hproj.1, hφ0scale⟩, ⟨hproj.2, hφhat1scale⟩⟩

/-- One-phase finite positive-box conversion from projective-and-scale lag collapse to
coordinate lag drift.

This is the finite-dimensional algebra core: if two consecutive uniformly positive vectors have all
cross-products asymptotically flat and their totals asymptotically agree, then each coordinate
asymptotically agrees.  It is independent of the Sinkhorn equations. -/
theorem finite_phase_lag_drift_zero_of_projective_scale_lag {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (subseq : ℕ → ℕ)
    (_hbox : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ n i, ε ≤ u n i ∧ u n i ≤ B)
    (_hprojscale : SinkhornPhaseProjectiveScaleLagZeroAlong u subseq) :
    Filter.Tendsto
      (fun n => fun i => u (subseq n) i - u ((subseq n).pred) i)
      Filter.atTop (nhds (0 : ι → ℝ)) := by
  sorry

/-- Finite positive-box conversion from projective-and-scale lag collapse to coordinate lag drift.

This Sinkhorn-denominator wrapper is now just two applications of the one-phase finite-dimensional
conversion above, one for `φ0` and one for `φhat1`. -/
theorem sinkhorn_denominator_lag_drift_zero_of_projective_scale_lag {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hprojscale : SinkhornDenominatorProjectiveScaleLagZeroAlong φ0Iter φhat1Iter subseq) :
    SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq := by
  rcases hbounds with ⟨ε, B, hε, hB, hφ0, _hφhat0, _hφ1, hφhat1⟩
  have hφ0box : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B :=
    ⟨ε, B, hε, hB, hφ0⟩
  have hφhat1box : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ n i, ε ≤ φhat1Iter n i ∧ φhat1Iter n i ≤ B :=
    ⟨ε, B, hε, hB, hφhat1⟩
  exact ⟨
    finite_phase_lag_drift_zero_of_projective_scale_lag φ0Iter subseq hφ0box hprojscale.1,
    finite_phase_lag_drift_zero_of_projective_scale_lag φhat1Iter subseq hφhat1box hprojscale.2⟩

/-- Denominator lag drift follows from the projective/scale collapse plus finite positive-box
conversion.  This wrapper preserves the earlier public C2 seam while exposing the two real subproblems
above. -/
theorem sinkhorn_denominator_lag_drift_tendsto_zero_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq := by
  have hprojscale : SinkhornDenominatorProjectiveScaleLagZeroAlong φ0Iter φhat1Iter subseq :=
    sinkhorn_denominator_projective_scale_lag_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_denominator_lag_drift_zero_of_projective_scale_lag
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hbounds hprojscale

/-- Quotient-update algebra converting denominator lag drift into mixed-phase drift.

Once the denominator phases have vanishing lag drift and remain in a uniform positive finite box,
normalization equations
`φhat0Iter (n + 1) * φ0Iter n = p` and
`φ1Iter (n + 1) * φhat1Iter n = q` convert denominator lag drift into drift of the quotient-updated
mixed phases.  This seam should be mostly finite-dimensional algebra and continuity of inversion on
`[ε, B]`. -/
theorem sinkhorn_phase_drift_zero_of_denominator_lag_drift {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hdenom : SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq) :
    SinkhornPhaseDriftZeroAlong φhat0Iter φ1Iter subseq := by
  sorry

/-- Asymptotic-regularity seam for the two mixed phases.

The hard content is factored through two lower-level surfaces: first prove vanishing lag drift for
the denominator phases from the positive Sinkhorn dynamics and gauge, then use the normalization
quotient equations and the uniform finite box to transfer that drift to the mixed phases. -/
theorem sinkhorn_phase_drift_tendsto_zero_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    SinkhornPhaseDriftZeroAlong φhat0Iter φ1Iter subseq := by
  have hdenom : SinkhornDenominatorLagDriftZeroAlong φ0Iter φhat1Iter subseq :=
    sinkhorn_denominator_lag_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_phase_drift_zero_of_denominator_lag_drift p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq hiter hbounds hdenom

/-- Vanishing phase drift identifies the current and successor limits in a raw precluster.

This is a generic topology wrapper: if the successor-minus-current stream tends to zero and both
streams already have named limits, then those limits agree. -/
theorem sinkhorn_precluster_successor_limits_eq_of_phase_drift {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1)
    (hφhat0_drift :
      Filter.Tendsto
        (fun n => fun i => φhat0Iter (subseq n + 1) i - φhat0Iter (subseq n) i)
        Filter.atTop (nhds 0))
    (hφ1_drift :
      Filter.Tendsto
        (fun n => fun j => φ1Iter (subseq n + 1) j - φ1Iter (subseq n) j)
        Filter.atTop (nhds 0)) :
    ψhat0Succ = ψhat0 ∧ ψ1Succ = ψ1 := by
  have hφhat0_limit : ψhat0Succ - ψhat0 = 0 :=
    tendsto_nhds_unique
      (hpre.tendsto_φhat0_succ.sub hpre.tendsto_φhat0)
      hφhat0_drift
  have hφ1_limit : ψ1Succ - ψ1 = 0 :=
    tendsto_nhds_unique
      (hpre.tendsto_φ1_succ.sub hpre.tendsto_φ1)
      hφ1_drift
  exact ⟨sub_eq_zero.mp hφhat0_limit, sub_eq_zero.mp hφ1_limit⟩

/-- Sinkhorn-specific compatibility seam for raw six-phase preclusters.

The hard content is now isolated as asymptotic regularity of the two phase drifts.  This wrapper only
turns that drift statement into equality of current and successor limits. -/
theorem sinkhorn_precluster_successor_limits_eq_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    ψhat0Succ = ψhat0 ∧ ψ1Succ = ψ1 := by
  obtain ⟨hφhat0_drift, hφ1_drift⟩ :=
    sinkhorn_phase_drift_tendsto_zero_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_precluster_successor_limits_eq_of_phase_drift
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hpre hφhat0_drift hφ1_drift

/-- Upgrade a raw precluster to a phase-compatible cluster using gauge-normalized Sinkhorn iterate
structure. -/
theorem sinkhorn_cluster_along_of_precluster_from_gauge_iterates {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hpre : IsFiniteSinkhornPhasePreclusterAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1) :
    IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨hψhat0, hψ1⟩ :=
    sinkhorn_precluster_successor_limits_eq_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre
  exact sinkhorn_cluster_along_of_precluster_successor_eq
    φ0Iter φhat0Iter φ1Iter φhat1Iter subseq
    ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hpre hψhat0 hψ1

/-- Explicit subsequence form of bounded finite-dimensional compactness, upgraded to the
phase-compatible Sinkhorn cluster predicate using gauge-normalized iterate structure. -/
theorem sinkhorn_phase_compatible_subsequence_along_of_gauge_iterates_and_bounds {ι : Type*}
    [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
      IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
        subseq ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨subseq, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, hpre⟩ :=
    sinkhorn_phase_precluster_subsequence_of_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds
  exact ⟨subseq, ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_along_of_precluster_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 subseq
      ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1 hiter hgauge hbounds hpre⟩

/-- Bounded finite-dimensional sequences admit phase-compatible cluster subsequences after using the
gauge-normalized Sinkhorn iterate structure to identify current and successor limits. -/
theorem sinkhorn_phase_compatible_subsequence_of_gauge_iterates_and_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨subseq, ψ0, ψhat0, ψ1, ψhat1, halong⟩ :=
    sinkhorn_phase_compatible_subsequence_along_of_gauge_iterates_and_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hiter hgauge hbounds
  exact ⟨ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_point_of_along
      φ0Iter φhat0Iter φ1Iter φhat1Iter subseq ψ0 ψhat0 ψ1 ψhat1 halong⟩

/-- Bounded phase-compatible compactness for every outer subsequence, upgraded from a raw precluster
by the Sinkhorn iterate equations. -/
theorem sinkhorn_outer_subsequence_cluster_from_gauge_iterates_and_bounds {ι : Type*}
    [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 := by
  intro subseq hsubseq
  obtain ⟨subsub, ψ0, ψhat0, ψhat0Succ, ψ1, ψ1Succ, ψhat1, hpre⟩ :=
    sinkhorn_outer_phase_precluster_subsequence_from_bounds
      φ0Iter φhat0Iter φ1Iter φhat1Iter hbounds subseq hsubseq
  exact ⟨subsub, ψ0, ψhat0, ψ1, ψhat1,
    sinkhorn_cluster_along_of_precluster_from_gauge_iterates p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      (fun n => subseq (subsub n)) ψ0 ψhat0 ψhat0Succ ψ1 ψ1Succ ψhat1
      hiter hgauge hbounds hpre⟩

/-- Every outer subsequence has a further phase-compatible cluster subsequence.

This is the sequential-compactness form needed for the final convergence theorem.  The compactness
part now produces only a raw six-phase precluster; gauge-normalized Sinkhorn iterate structure supplies the separate
successor-limit compatibility seam. -/
theorem sinkhorn_gauge_normalized_every_subsequence_has_cluster {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∀ subseq : ℕ → ℕ, StrictMono subseq →
      ∃ (subsub : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ),
        IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
          (fun n => subseq (subsub n)) ψ0 ψhat0 ψ1 ψhat1 := by
  have hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter :=
    sinkhorn_gauge_normalized_uniform_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hp hq hG hiter hgauge
  exact sinkhorn_outer_subsequence_cluster_from_gauge_iterates_and_bounds p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hiter hgauge hbounds

/-- Compactness/subsequence seam for gauge-normalized finite Sinkhorn iterates.

This target-facing theorem is the one-cluster corollary of the uniform-bounds, raw compactness, and
successor-limit compatibility seams. -/
theorem sinkhorn_gauge_normalized_subsequence_exists {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∃ ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 := by
  have hbounds : SinkhornPhaseBoxBounds φ0Iter φhat0Iter φ1Iter φhat1Iter :=
    sinkhorn_gauge_normalized_uniform_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
      hp hq hG hiter hgauge
  exact sinkhorn_phase_compatible_subsequence_of_gauge_iterates_and_bounds p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hiter hgauge hbounds

end ChenGeorgiouPavon2021
