/-
# Projective lag collapse for Sinkhorn denominator phases

This file owns the hardest projective-shape asymptotic-regularity seam.  It should be attacked with a
Hilbert-projective contraction, monotone-diameter decay, or equivalent positive-kernel energy argument.
It does not need to prove any scale/total-mass facts.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.Precluster

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021


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


end ChenGeorgiouPavon2021
