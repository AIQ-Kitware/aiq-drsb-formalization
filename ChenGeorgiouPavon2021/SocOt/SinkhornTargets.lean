/-
# Ideal theorem targets for finite Sinkhorn uniqueness/convergence
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- A finite Schrödinger/Sinkhorn potential system for prescribed marginals and positive kernel.

This packages the four positivity and four equation blocks so the uniqueness and convergence targets
speak about the same mathematical object.  Kernel positivity is intentionally kept as a theorem
hypothesis, not as a field here, because it is a condition on the reference kernel rather than on an
individual candidate solution. -/
structure IsFiniteSinkhornPotentialSystem {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ) : Prop where
  φ0_pos : ∀ i, 0 < φ0 i
  φhat0_pos : ∀ i, 0 < φhat0 i
  φ1_pos : ∀ j, 0 < φ1 j
  φhat1_pos : ∀ j, 0 < φhat1 j
  forward : ∀ i, φ0 i = ∑ j, G i j * φ1 j
  backward : ∀ j, φhat1 j = ∑ i, G i j * φhat0 i
  normalize_left : ∀ i, φ0 i * φhat0 i = p i
  normalize_right : ∀ j, φ1 j * φhat1 j = q j

/-- Pointwise ratio between two positive Sinkhorn potentials.  It is intentionally just the raw
quotient; nonzero denominators are supplied by the positivity fields at use sites. -/
noncomputable def sinkhornRatio {ι : Type*} (ψ φ : ι → ℝ) : ι → ℝ :=
  fun i => ψ i / φ i

/-- The next local maximum-principle target for finite Sinkhorn uniqueness.

Assume the finite index type is nonempty.  The proof should choose a right-side extremizer
`jstar` for the ratio `ψ1 / φ1`, use the Sinkhorn equations to bridge left and right ratios through
strictly positive finite weighted averages, and then use strict positivity of `G` to propagate equality
from that extremizer to every index.

This is deliberately sharper than the public scaling theorem below: it names the ratio witness
`sinkhornRatio ψ1 φ1 jstar` and asks only for all left and right ratios to equal that witness.  Once
this bridge is proved, the public existential scaling statement is just packaging plus positivity of
the witness ratio. -/
theorem finite_sinkhorn_ratio_bridge_all_indices {ι : Type*} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hG : ∀ i j, 0 < G i j)
    (_hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (_hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1) :
    ∃ jstar : ι,
      (∀ i, sinkhornRatio ψ0 φ0 i = sinkhornRatio ψ1 φ1 jstar) ∧
      (∀ j, sinkhornRatio ψ1 φ1 j = sinkhornRatio ψ1 φ1 jstar) := by
  sorry

/-- Finite ratio-collapse seam for the uniqueness proof.

The remaining maximum-principle work has been isolated in
`finite_sinkhorn_ratio_bridge_all_indices`.  This theorem now handles the empty-index edge case and
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

/-- Abstract Fortet--IPF/Sinkhorn update equations for the finite target theorem.

This is intentionally an iterate specification, not a convergence assumption: it records that the
four displayed sequences are generated by the finite Sinkhorn update against marginals `p`, `q` and
positive kernel `G`.  Positivity is carried as part of the iterate package because the raw displayed
equations alone do not remember the positive seed needed for the finite Sinkhorn iteration. -/
structure IsFiniteSinkhornIterateSystem {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ) : Prop where
  φ0_pos : ∀ n i, 0 < φ0Iter n i
  φhat0_pos : ∀ n i, 0 < φhat0Iter n i
  φ1_pos : ∀ n j, 0 < φ1Iter n j
  φhat1_pos : ∀ n j, 0 < φhat1Iter n j
  forward : ∀ n i, φ0Iter n i = ∑ j, G i j * φ1Iter n j
  backward : ∀ n j, φhat1Iter n j = ∑ i, G i j * φhat0Iter n i
  normalize_left : ∀ n i, φhat0Iter (n + 1) i * φ0Iter n i = p i
  normalize_right : ∀ n j, φ1Iter (n + 1) j * φhat1Iter n j = q j

/-- Gauge choice for a particular representative of the scaling class.

Without some normalization, Sinkhorn potentials are determined only up to
`φ ↦ c • φ`, `φhat ↦ c⁻¹ • φhat`, so convergence to a named representative is over-specified.  This
predicate fixes the gauge by matching the total mass of the left forward potential at every iterate. -/
structure IsFiniteSinkhornGaugeNormalized {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ) : Prop where
  left_total : ∀ n, ∑ i, φ0Iter n i = ∑ i, φ0 i

/-- Phase-compatible subsequence cluster-point assertion for finite Sinkhorn iterates.

The Sinkhorn normalizations couple the `n`th forward/hatted-right vectors to the successor
`(n+1)`st hatted-left/right-forward vectors.  A cluster point that is useful for passing the
update equations to the limit therefore needs more than convergence of the four vectors along the
same raw subsequence: it also needs the successor phases that occur in the normalization equations
to converge to the same limiting hatted/forward potentials.  Positivity is included as a separate
nondegeneracy datum because pointwise-positive iterates can converge to zero without a uniform lower
bound.

This remains `Prop`-valued: the subsequence itself is carried under an existential proof field rather
than as structure data, since Lean does not allow computational fields in a `Prop` structure. -/
structure IsFiniteSinkhornClusterPoint {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ) : Prop where
  exists_subseq : ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
    Filter.Tendsto (fun n => φ0Iter (subseq n)) Filter.atTop (nhds ψ0) ∧
    Filter.Tendsto (fun n => φhat0Iter (subseq n)) Filter.atTop (nhds ψhat0) ∧
    Filter.Tendsto (fun n => φhat0Iter (subseq n + 1)) Filter.atTop (nhds ψhat0) ∧
    Filter.Tendsto (fun n => φ1Iter (subseq n)) Filter.atTop (nhds ψ1) ∧
    Filter.Tendsto (fun n => φ1Iter (subseq n + 1)) Filter.atTop (nhds ψ1) ∧
    Filter.Tendsto (fun n => φhat1Iter (subseq n)) Filter.atTop (nhds ψhat1)
  positive :
    (∀ i, 0 < ψ0 i) ∧
    (∀ i, 0 < ψhat0 i) ∧
    (∀ j, 0 < ψ1 j) ∧
    (∀ j, 0 < ψhat1 j)

/-- Positivity seam for the finite Sinkhorn iteration.

With positivity included in `IsFiniteSinkhornIterateSystem`, this is a projection lemma.  If the
iterate package is later refactored to carry only a positive seed, this is the theorem that should
be replaced by the actual induction proving positivity preservation. -/
theorem sinkhorn_iterates_positive {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    (∀ n i, 0 < φ0Iter n i) ∧
    (∀ n i, 0 < φhat0Iter n i) ∧
    (∀ n j, 0 < φ1Iter n j) ∧
    (∀ n j, 0 < φhat1Iter n j) := by
  exact ⟨hiter.φ0_pos, hiter.φhat0_pos, hiter.φ1_pos, hiter.φhat1_pos⟩

/-- Compactness/subsequence seam for gauge-normalized finite Sinkhorn iterates.

The intended proof is finite-dimensional: gauge normalization and strict positivity bound the
iterates in a product of closed intervals after extracting the usual projective coordinates, so every
sequence admits a convergent subsequence. -/
theorem sinkhorn_gauge_normalized_subsequence_exists {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (_hp : ∀ i, 0 < p i) (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∃ ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ,
      IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
        ψ0 ψhat0 ψ1 ψhat1 := by
  sorry

/-- Limit-passage seam for the equations satisfied by a phase-compatible cluster point.

The remaining analytic/topological content is continuity of finite sums and products along the
subsequence phases recorded in `IsFiniteSinkhornClusterPoint`: forward/backward equations pass along
`subseq n`, while marginal normalizations pass along the mixed phases `subseq n` and `subseq n + 1`.
-/
theorem sinkhorn_cluster_point_equations {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (_hp : ∀ i, 0 < p i) (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    (∀ i, ψ0 i = ∑ j, G i j * ψ1 j) ∧
    (∀ j, ψhat1 j = ∑ i, G i j * ψhat0 i) ∧
    (∀ i, ψ0 i * ψhat0 i = p i) ∧
    (∀ j, ψ1 j * ψhat1 j = q j) := by
  sorry

/-- Cluster-point fixed-point theorem for finite Sinkhorn iterates.

With phase compatibility and strict positivity recorded in the cluster predicate, the fixed-point
wrapper is now purely packaging: positivity is projected from the cluster datum and the four equations
come from the finite-dimensional limit-passage seam. -/
theorem sinkhorn_cluster_point_is_potential {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hcluster : IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1) :
    IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1 := by
  obtain ⟨hψ0_pos, hψhat0_pos, hψ1_pos, hψhat1_pos⟩ := hcluster.positive
  obtain ⟨hforward, hbackward, hnormalize_left, hnormalize_right⟩ :=
    sinkhorn_cluster_point_equations p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter ψ0 ψhat0 ψ1 ψhat1
      hp hq hG hiter hcluster
  exact {
    φ0_pos := hψ0_pos
    φhat0_pos := hψhat0_pos
    φ1_pos := hψ1_pos
    φhat1_pos := hψhat1_pos
    forward := hforward
    backward := hbackward
    normalize_left := hnormalize_left
    normalize_right := hnormalize_right
  }

/-- Gauge uniqueness seam for cluster points.

Once a cluster point is known to solve the Sinkhorn equations, uniqueness up to common scaling plus
the chosen gauge should identify it with the selected representative. -/
theorem sinkhorn_gauge_fixed_point_unique {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hφsys : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1)
    (hψsys : IsFiniteSinkhornPotentialSystem p q G ψ0 ψhat0 ψ1 ψhat1)
    (hgauge : ∑ i, ψ0 i = ∑ i, φ0 i) :
    ψ0 = φ0 ∧ ψhat0 = φhat0 ∧ ψ1 = φ1 ∧ ψhat1 = φhat1 := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> exact isEmptyElim i
  · obtain ⟨c, hc, hψ0, hψhat0, hψ1, hψhat1⟩ :=
      sinkhorn_potentials_unique_up_to_scaling p q G
        φ0 φhat0 φ1 φhat1 ψ0 ψhat0 ψ1 ψhat1 hG hφsys hψsys
    have hsumφ0_pos : 0 < ∑ i, φ0 i := by
      exact Finset.sum_pos (fun i _ => hφsys.φ0_pos i) (by
        rcases hne with ⟨i⟩
        exact ⟨i, Finset.mem_univ i⟩)
    have hsumφ0_ne : (∑ i, φ0 i) ≠ 0 := ne_of_gt hsumφ0_pos
    have hsumψ0 : ∑ i, ψ0 i = c * ∑ i, φ0 i := by
      calc
        ∑ i, ψ0 i = ∑ i, c * φ0 i := by
          exact Finset.sum_congr rfl (fun i _ => hψ0 i)
        _ = c * ∑ i, φ0 i := by rw [Finset.mul_sum]
    have hc_eq_one : c = 1 := by
      apply mul_right_cancel₀ hsumφ0_ne
      calc
        c * (∑ i, φ0 i) = ∑ i, ψ0 i := hsumψ0.symm
        _ = ∑ i, φ0 i := hgauge
        _ = 1 * (∑ i, φ0 i) := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext i
      simpa [hc_eq_one] using hψ0 i
    · funext i
      simpa [hc_eq_one] using hψhat0 i
    · funext j
      simpa [hc_eq_one] using hψ1 j
    · funext j
      simpa [hc_eq_one] using hψhat1 j

/-- Finite-dimensional convergence seam after gauge normalization.

This is the standard compactness-plus-unique-cluster-point argument: every subsequence has a further
cluster point, cluster points satisfy the fixed-point equations, the gauge-normalized fixed point is
unique, hence the whole finite-dimensional sequence converges to that representative. -/
theorem sinkhorn_gauge_normalized_convergence_core {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (_hp : ∀ i, 0 < p i) (_hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < G i j)
    (_hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (_hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (_hpotentials : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) ∧
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) ∧
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) ∧
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  sorry

/-- Algorithmic convergence target for Fortet-IPF/Sinkhorn iterates.

The old scaffold was overstrong: arbitrary sequences do not converge to arbitrary named potentials,
and even genuine finite Sinkhorn iterates only converge to a selected representative after fixing the
multiplicative gauge.  The repaired target states convergence for positive finite Sinkhorn update
sequences that satisfy an explicit gauge normalization, against positive marginals and a strictly
positive kernel, and toward an actual finite Sinkhorn potential system.  No convergence hypothesis is
assumed. -/
theorem sinkhorn_iterates_converge_to_potentials {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1)
    (hpotentials : IsFiniteSinkhornPotentialSystem p q G φ0 φhat0 φ1 φhat1) :
    Filter.Tendsto φ0Iter Filter.atTop (nhds φ0) ∧
    Filter.Tendsto φhat0Iter Filter.atTop (nhds φhat0) ∧
    Filter.Tendsto φ1Iter Filter.atTop (nhds φ1) ∧
    Filter.Tendsto φhat1Iter Filter.atTop (nhds φhat1) := by
  exact sinkhorn_gauge_normalized_convergence_core p q G
    φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1
    hp hq hG hiter hgauge hpotentials

end ChenGeorgiouPavon2021
