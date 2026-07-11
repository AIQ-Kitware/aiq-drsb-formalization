/-
# Uniform-bounds front end for finite Sinkhorn convergence

This file contains the explicit-cluster packaging lemma and the gauge-normalized boundedness
interface.  The boundedness argument is split into independent directional estimates: the fixed-gauge forward potential box, hatted-left bounds from normalization,
hatted-right bounds from the backward equation, and right-potential bounds from normalization.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Topology

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- A uniform positive finite box for one finite family of Sinkhorn phases. -/
def SinkhornPhaseInUniformBox {ι : Type*} (u : ℕ → ι → ℝ) (ε B : ℝ) : Prop :=
  ∀ n i, ε ≤ u n i ∧ u n i ≤ B

/-- A common uniform positive finite box for all four finite Sinkhorn iterate phases. -/
def SinkhornIteratesInUniformBox {ι : Type*}
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ) (ε B : ℝ) : Prop :=
  SinkhornPhaseInUniformBox φ0Iter ε B ∧
  SinkhornPhaseInUniformBox φhat0Iter ε B ∧
  SinkhornPhaseInUniformBox φ1Iter ε B ∧
  SinkhornPhaseInUniformBox φhat1Iter ε B

/-- Convert an explicit phase-compatible cluster point into the existential cluster predicate.

The compactness and bad-subsequence arguments naturally produce cluster points along named absolute
subsequences.  The uniqueness theorem, however, is stated against the target-facing existential
cluster predicate.  This bridge isolates that packaging step from the real topology. -/
theorem sinkhorn_cluster_point_of_along {ι : Type*} [Fintype ι]
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (subseq : ℕ → ℕ) (ψ0 ψhat0 ψ1 ψhat1 : ι → ℝ)
    (halong : IsFiniteSinkhornClusterPointAlong φ0Iter φhat0Iter φ1Iter φhat1Iter
      subseq ψ0 ψhat0 ψ1 ψhat1) :
    IsFiniteSinkhornClusterPoint φ0Iter φhat0Iter φ1Iter φhat1Iter
      ψ0 ψhat0 ψ1 ψhat1 := by
  exact {
    exists_subseq := ⟨subseq, halong⟩
    positive := halong.positive
  }

/-- Projective-diameter bound for the forward left potentials.

Mathematical content: the positive finite kernel has a global lower and upper coefficient bound.
Since `φ0Iter n i = ∑ j, G i j * φ1Iter n j` and the summands `φ1Iter n j` are positive, every
coordinate of `φ0Iter n` is bounded above by a single constant multiple of every other coordinate.
This is the kernel-comparison part of the fixed-gauge estimate, independent of the gauge. -/
theorem sinkhorn_left_forward_projective_bound {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hp : ∀ i, 0 < p i) (_hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter) :
    ∃ R : ℝ, 0 < R ∧ ∀ n i k, φ0Iter n i ≤ R * φ0Iter n k := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · refine ⟨1, by norm_num, ?_⟩
    intro n i
    exact isEmptyElim i
  · letI : Nonempty ι := hne
    obtain ⟨i0⟩ := hne
    letI : Nonempty (ι × ι) := ⟨(i0, i0)⟩
    obtain ⟨pair_min, _hpair_min_mem, hpair_min⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (ι × ι))
        (fun pair : ι × ι => G pair.1 pair.2) Finset.univ_nonempty
    obtain ⟨pair_max, _hpair_max_mem, hpair_max⟩ :=
      Finset.exists_max_image (Finset.univ : Finset (ι × ι))
        (fun pair : ι × ι => G pair.1 pair.2) Finset.univ_nonempty
    let gmin : ℝ := G pair_min.1 pair_min.2
    let gmax : ℝ := G pair_max.1 pair_max.2
    have hgmin_pos : 0 < gmin := by
      dsimp [gmin]
      exact hG pair_min.1 pair_min.2
    have hgmax_pos : 0 < gmax := by
      dsimp [gmax]
      exact hG pair_max.1 pair_max.2
    have hgmin_le : ∀ i j, gmin ≤ G i j := by
      intro i j
      dsimp [gmin]
      exact hpair_min (i, j) (Finset.mem_univ (i, j))
    have hle_gmax : ∀ i j, G i j ≤ gmax := by
      intro i j
      dsimp [gmax]
      exact hpair_max (i, j) (Finset.mem_univ (i, j))
    let R : ℝ := gmax / gmin
    have hRpos : 0 < R := by
      dsimp [R]
      exact div_pos hgmax_pos hgmin_pos
    refine ⟨R, hRpos, ?_⟩
    intro n i k
    have hφ1_nonneg : ∀ j, 0 ≤ φ1Iter n j := fun j => le_of_lt (hiter.φ1_pos n j)
    have hupper : φ0Iter n i ≤ gmax * ∑ j, φ1Iter n j := by
      calc
        φ0Iter n i = ∑ j, G i j * φ1Iter n j := hiter.forward n i
        _ ≤ ∑ j, gmax * φ1Iter n j := by
          exact Finset.sum_le_sum (fun j _hj =>
            mul_le_mul_of_nonneg_right (hle_gmax i j) (hφ1_nonneg j))
        _ = gmax * ∑ j, φ1Iter n j := by
          rw [Finset.mul_sum]
    have hlower : gmin * ∑ j, φ1Iter n j ≤ φ0Iter n k := by
      calc
        gmin * ∑ j, φ1Iter n j = ∑ j, gmin * φ1Iter n j := by
          rw [Finset.mul_sum]
        _ ≤ ∑ j, G k j * φ1Iter n j := by
          exact Finset.sum_le_sum (fun j _hj =>
            mul_le_mul_of_nonneg_right (hgmin_le k j) (hφ1_nonneg j))
        _ = φ0Iter n k := by
          rw [hiter.forward n k]
    have hscale : R * (gmin * ∑ j, φ1Iter n j) = gmax * ∑ j, φ1Iter n j := by
      dsimp [R]
      field_simp [ne_of_gt hgmin_pos]
    have hscaled_lower : gmax * ∑ j, φ1Iter n j ≤ R * φ0Iter n k := by
      rw [← hscale]
      exact mul_le_mul_of_nonneg_left hlower (le_of_lt hRpos)
    exact le_trans hupper hscaled_lower

/-- Turn a fixed total mass and a projective-diameter bound into a common finite box.

Mathematical content: positivity and `∑ i, u n i = S` give the upper bound.  The projective bound
`u n k ≤ R * u n i`, summed over `k`, gives `S ≤ card ι * R * u n i`, hence a positive lower
bound when the type is nonempty.  The empty finite type satisfies the bound trivially. -/
theorem sinkhorn_phase_bounds_from_total_and_projective_bound {ι : Type*} [Fintype ι]
    (u : ℕ → ι → ℝ) (S : ℝ)
    (hpos : ∀ n i, 0 < u n i)
    (htotal : ∀ n, ∑ i, u n i = S)
    (hprojective : ∃ R : ℝ, 0 < R ∧ ∀ n i k, u n i ≤ R * u n k) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox u ε B := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro n i
    exact isEmptyElim i
  · letI : Nonempty ι := hne
    obtain ⟨R, hRpos, hRbound⟩ := hprojective
    have hcard_nat : 0 < (Finset.univ : Finset ι).card :=
      Finset.card_pos.mpr Finset.univ_nonempty
    have hcard_pos : 0 < ((Finset.univ : Finset ι).card : ℝ) := by
      exact_mod_cast hcard_nat
    have hS_pos : 0 < S := by
      rw [← htotal 0]
      exact Finset.sum_pos (fun i _hi => hpos 0 i) Finset.univ_nonempty
    let denom : ℝ := ((Finset.univ : Finset ι).card : ℝ) * R
    have hdenom_pos : 0 < denom := by
      dsimp [denom]
      exact mul_pos hcard_pos hRpos
    let ε : ℝ := S / denom
    let B : ℝ := S
    have hε_pos : 0 < ε := by
      dsimp [ε]
      exact div_pos hS_pos hdenom_pos
    refine ⟨ε, B, hε_pos, hS_pos, ?_⟩
    intro n i
    have hupper : u n i ≤ S := by
      have hsingle : u n i ≤ ∑ k : ι, u n k := by
        exact Finset.single_le_sum
          (fun k _hk => le_of_lt (hpos n k))
          (Finset.mem_univ i)
      exact le_trans hsingle (le_of_eq (htotal n))
    have hsum_projective : S ≤ denom * u n i := by
      have hsum_le : (∑ k : ι, u n k) ≤ ∑ k : ι, R * u n i := by
        exact Finset.sum_le_sum (fun k _hk => hRbound n k i)
      rw [htotal n] at hsum_le
      have hsum_const : (∑ _k : ι, R * u n i) = ((Finset.univ : Finset ι).card : ℝ) * (R * u n i) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      dsimp [denom]
      rw [hsum_const] at hsum_le
      simpa [mul_assoc] using hsum_le
    have hlower : ε ≤ u n i := by
      dsimp [ε]
      have hscale : (S / denom) * denom = S := by
        field_simp [ne_of_gt hdenom_pos]
      by_contra hnot
      have hlt : u n i < S / denom := lt_of_not_ge hnot
      have hmul_lt : denom * u n i < S := by
        have htmp : denom * u n i < denom * (S / denom) := by
          exact mul_lt_mul_of_pos_left hlt hdenom_pos
        have hdenom_scale : denom * (S / denom) = S := by
          rw [mul_comm]
          exact hscale
        simpa [hdenom_scale] using htmp
      exact (not_lt_of_ge hsum_projective) hmul_lt
    exact ⟨hlower, hupper⟩

/-- Fixed-gauge bounds for the forward left potentials.

This wrapper separates the two mathematical ingredients: first prove a projective-diameter bound
from the positive kernel and forward equation, then use the gauge-fixed total mass to convert that
projective bound into an absolute finite box. -/
theorem sinkhorn_gauge_normalized_left_forward_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 _φhat0 _φ1 _φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 _φhat0 _φ1 _φhat1) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ0Iter ε B := by
  exact sinkhorn_phase_bounds_from_total_and_projective_bound φ0Iter (∑ i, φ0 i)
    hiter.φ0_pos hgauge.left_total
    (sinkhorn_left_forward_projective_bound p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter hp hq hG hiter)

/-- Generic successor-quotient bound for one Sinkhorn phase.

If a positive target phase is related to a uniformly boxed denominator by
`target (n + 1) i * denom n i = a i`, then all successor values of `target` are bounded by
`a i / B` and `a i / ε`, while the finitely many initial values `target 0 i` are absorbed into the
same global finite box.  This lemma is intentionally Sinkhorn-free except for reusing the local box
predicate, so it can discharge both the left-hatted and right-forward normalization estimates. -/
theorem sinkhorn_successor_quotient_phase_bounds {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (denom target : ℕ → ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (htarget_pos : ∀ n i, 0 < target n i)
    (hdenom_bounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox denom ε B)
    (hupdate : ∀ n i, target (n + 1) i * denom n i = a i) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox target ε B := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro n i
    exact isEmptyElim i
  · letI : Nonempty ι := hne
    obtain ⟨εd, Bd, hεd, hBd, hdenom_box⟩ := hdenom_bounds
    obtain ⟨i_init_min, _hi_init_min_mem, hinit_min⟩ :=
      Finset.exists_min_image (Finset.univ : Finset ι) (fun i => target 0 i) Finset.univ_nonempty
    obtain ⟨i_init_max, _hi_init_max_mem, hinit_max⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι) (fun i => target 0 i) Finset.univ_nonempty
    obtain ⟨i_a_min, _hi_a_min_mem, ha_min⟩ :=
      Finset.exists_min_image (Finset.univ : Finset ι) a Finset.univ_nonempty
    obtain ⟨i_a_max, _hi_a_max_mem, ha_max⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι) a Finset.univ_nonempty
    let εtarget : ℝ := min (target 0 i_init_min) (a i_a_min / Bd)
    let Btarget : ℝ := max (target 0 i_init_max) (a i_a_max / εd)
    have hamin_pos : 0 < a i_a_min := ha i_a_min
    have hamax_pos : 0 < a i_a_max := ha i_a_max
    have hεtarget_pos : 0 < εtarget := by
      dsimp [εtarget]
      exact lt_min (htarget_pos 0 i_init_min) (div_pos hamin_pos hBd)
    have hBtarget_pos : 0 < Btarget := by
      dsimp [Btarget]
      exact lt_of_lt_of_le (htarget_pos 0 i_init_max)
        (le_max_left (target 0 i_init_max) (a i_a_max / εd))
    refine ⟨εtarget, Btarget, hεtarget_pos, hBtarget_pos, ?_⟩
    intro n i
    cases n with
    | zero =>
        have hlower : εtarget ≤ target 0 i := by
          dsimp [εtarget]
          exact le_trans (min_le_left (target 0 i_init_min) (a i_a_min / Bd))
            (hinit_min i (Finset.mem_univ i))
        have hupper : target 0 i ≤ Btarget := by
          dsimp [Btarget]
          exact le_trans (hinit_max i (Finset.mem_univ i))
            (le_max_left (target 0 i_init_max) (a i_a_max / εd))
        exact ⟨hlower, hupper⟩
    | succ n =>
        have hdenom_pos : 0 < denom n i := lt_of_lt_of_le hεd (hdenom_box n i).1
        have htarget_nonneg : 0 ≤ target (n + 1) i := le_of_lt (htarget_pos (n + 1) i)
        have ha_min_le : a i_a_min ≤ a i := ha_min i (Finset.mem_univ i)
        have ha_le_max : a i ≤ a i_a_max := ha_max i (Finset.mem_univ i)
        have htarget_mul_B : a i_a_min ≤ target (n + 1) i * Bd := by
          have hprod_le : target (n + 1) i * denom n i ≤ target (n + 1) i * Bd := by
            exact mul_le_mul_of_nonneg_left (hdenom_box n i).2 htarget_nonneg
          exact le_trans (le_trans ha_min_le (le_of_eq (Eq.symm (hupdate n i)))) hprod_le
        have htarget_lower_succ : a i_a_min / Bd ≤ target (n + 1) i := by
          have hscale : (a i_a_min / Bd) * Bd = a i_a_min := by
            field_simp [ne_of_gt hBd]
          nlinarith
        have htarget_mul_ε : target (n + 1) i * εd ≤ a i_a_max := by
          have hprod_lower : target (n + 1) i * εd ≤ target (n + 1) i * denom n i := by
            exact mul_le_mul_of_nonneg_left (hdenom_box n i).1 htarget_nonneg
          exact le_trans hprod_lower (le_trans (le_of_eq (hupdate n i)) ha_le_max)
        have htarget_upper_succ : target (n + 1) i ≤ a i_a_max / εd := by
          have hscale : (a i_a_max / εd) * εd = a i_a_max := by
            field_simp [ne_of_gt hεd]
          nlinarith
        have hlower : εtarget ≤ target (n + 1) i := by
          dsimp [εtarget]
          exact le_trans (min_le_right (target 0 i_init_min) (a i_a_min / Bd)) htarget_lower_succ
        have hupper : target (n + 1) i ≤ Btarget := by
          dsimp [Btarget]
          exact le_trans htarget_upper_succ
            (le_max_right (target 0 i_init_max) (a i_a_max / εd))
        exact ⟨hlower, hupper⟩

/-- Generic weighted-sum bound for one Sinkhorn phase.

If `source` is uniformly boxed and `target n j = ∑ i, G i j * source n i` with a strictly positive
finite kernel, then `target` is uniformly boxed.  The lower bound comes from any one strictly positive
summand; the upper bound comes from the finite sum of kernel coefficients times the source upper
bound. -/
theorem sinkhorn_weighted_sum_phase_bounds {ι : Type*} [Fintype ι]
    (G : ι → ι → ℝ) (source target : ℕ → ι → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hsource_bounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox source ε B)
    (hupdate : ∀ n j, target n j = ∑ i, G i j * source n i) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox target ε B := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro n j
    exact isEmptyElim j
  · letI : Nonempty ι := hne
    obtain ⟨ε, B, hε, hB, hbox⟩ := hsource_bounds
    obtain ⟨i0⟩ := hne
    obtain ⟨jmin, _hjmin_mem, hjmin⟩ :=
      Finset.exists_min_image (Finset.univ : Finset ι) (fun j => G i0 j) Finset.univ_nonempty
    let εtarget : ℝ := G i0 jmin * ε
    let C : ℝ := ∑ i, ∑ k, G i k
    have hεtarget_pos : 0 < εtarget := by
      dsimp [εtarget]
      exact mul_pos (hG i0 jmin) hε
    have hC_pos : 0 < C := by
      dsimp [C]
      exact Finset.sum_pos
        (fun i _hi => Finset.sum_pos (fun k _hk => hG i k) Finset.univ_nonempty)
        Finset.univ_nonempty
    refine ⟨εtarget, C * B, hεtarget_pos, mul_pos hC_pos hB, ?_⟩
    intro n j
    have hcoeff_j_le_C : (∑ i, G i j) ≤ C := by
      dsimp [C]
      exact Finset.sum_le_sum (fun i _hi =>
        Finset.single_le_sum (fun k _hk => le_of_lt (hG i k)) (Finset.mem_univ j))
    have htarget_lower_term : εtarget ≤ G i0 j * source n i0 := by
      dsimp [εtarget]
      exact mul_le_mul (hjmin j (Finset.mem_univ j)) (hbox n i0).1
        (le_of_lt hε) (le_of_lt (hG i0 j))
    have htarget_term_le_sum : G i0 j * source n i0 ≤ ∑ i, G i j * source n i := by
      exact Finset.single_le_sum
        (fun i _hi => mul_nonneg (le_of_lt (hG i j)) (le_trans (le_of_lt hε) (hbox n i).1))
        (Finset.mem_univ i0)
    have htarget_lower : εtarget ≤ target n j := by
      rw [hupdate n j]
      exact le_trans htarget_lower_term htarget_term_le_sum
    have htarget_upper : target n j ≤ C * B := by
      calc
        target n j = ∑ i, G i j * source n i := hupdate n j
        _ ≤ ∑ i, G i j * B := by
          exact Finset.sum_le_sum (fun i _hi =>
            mul_le_mul_of_nonneg_left (hbox n i).2 (le_of_lt (hG i j)))
        _ = (∑ i, G i j) * B := by
          rw [Finset.sum_mul]
        _ ≤ C * B := by
          exact mul_le_mul_of_nonneg_right hcoeff_j_le_C (le_of_lt hB)
    exact ⟨htarget_lower, htarget_upper⟩

/-- Hatted-left bounds from left-forward bounds and the left marginal normalization.

For successor phases this is the algebraic estimate
`φhat0Iter (n + 1) i = p i / φ0Iter n i`; the finitely many initial values
`φhat0Iter 0 i` are absorbed into the final finite box using positivity. -/
theorem sinkhorn_hatted_left_bounds_from_left_forward_bounds {ι : Type*} [Fintype ι]
    (p _q : ι → ℝ) (_G : ι → ι → ℝ)
    (φ0Iter φhat0Iter _φ1Iter _φhat1Iter : ℕ → ι → ℝ)
    (hp : ∀ i, 0 < p i)
    (_hq : ∀ j, 0 < _q j) (_hG : ∀ i j, 0 < _G i j)
    (hiter : IsFiniteSinkhornIterateSystem p _q _G φ0Iter φhat0Iter _φ1Iter _φhat1Iter)
    (hφ0bounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ0Iter ε B) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat0Iter ε B := by
  exact sinkhorn_successor_quotient_phase_bounds p φ0Iter φhat0Iter
    hp hiter.φhat0_pos hφ0bounds hiter.normalize_left

/-- Hatted-right bounds from hatted-left bounds and the backward equation.

The backward equation writes each `φhat1Iter n j` as a positive finite weighted sum of the already
bounded hatted-left phase.  Positivity of `G` supplies a positive lower bound, and finiteness supplies
an upper bound. -/
theorem sinkhorn_hatted_right_bounds_from_hatted_left_bounds {ι : Type*} [Fintype ι]
    (_p _q : ι → ℝ) (G : ι → ι → ℝ)
    (_φ0Iter φhat0Iter _φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hp : ∀ i, 0 < _p i)
    (_hq : ∀ j, 0 < _q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem _p _q G _φ0Iter φhat0Iter _φ1Iter φhat1Iter)
    (hφhat0bounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat0Iter ε B) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat1Iter ε B := by
  exact sinkhorn_weighted_sum_phase_bounds G φhat0Iter φhat1Iter
    hG hφhat0bounds hiter.backward

/-- Right-forward bounds from hatted-right bounds and the right marginal normalization.

For successor phases this is the algebraic estimate
`φ1Iter (n + 1) j = q j / φhat1Iter n j`; the finitely many initial values `φ1Iter 0 j` are
absorbed into the final finite box using positivity. -/
theorem sinkhorn_right_forward_bounds_from_hatted_right_bounds {ι : Type*} [Fintype ι]
    (_p q : ι → ℝ) (_G : ι → ι → ℝ)
    (_φ0Iter _φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (_hp : ∀ i, 0 < _p i)
    (hq : ∀ j, 0 < q j) (_hG : ∀ i j, 0 < _G i j)
    (hiter : IsFiniteSinkhornIterateSystem _p q _G _φ0Iter _φhat0Iter φ1Iter φhat1Iter)
    (hφhat1bounds : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat1Iter ε B) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ1Iter ε B := by
  exact sinkhorn_successor_quotient_phase_bounds q φhat1Iter φ1Iter
    hq hiter.φ1_pos hφhat1bounds hiter.normalize_right

/-- Combine four positive finite boxes into one common box.

This is a bookkeeping lemma: take the minimum of the four positive lower bounds and the maximum of
the four positive upper bounds.  Keeping this separate prevents the main Sinkhorn estimate from being
cluttered by lattice arithmetic over `min` and `max`. -/
theorem sinkhorn_common_box_of_phase_boxes {ι : Type*}
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (hφ0 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ0Iter ε B)
    (hφhat0 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat0Iter ε B)
    (hφ1 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ1Iter ε B)
    (hφhat1 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat1Iter ε B) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      SinkhornIteratesInUniformBox φ0Iter φhat0Iter φ1Iter φhat1Iter ε B := by
  obtain ⟨ε0, B0, hε0, hB0, hbox0⟩ := hφ0
  obtain ⟨εhat0, Bhat0, hεhat0, hBhat0, hboxhat0⟩ := hφhat0
  obtain ⟨ε1, B1, hε1, hB1, hbox1⟩ := hφ1
  obtain ⟨εhat1, Bhat1, hεhat1, hBhat1, hboxhat1⟩ := hφhat1
  let ε : ℝ := min (min ε0 εhat0) (min ε1 εhat1)
  let B : ℝ := max (max B0 Bhat0) (max B1 Bhat1)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min (lt_min hε0 hεhat0) (lt_min hε1 hεhat1)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le hB0
      (le_trans (le_max_left B0 Bhat0) (le_max_left (max B0 Bhat0) (max B1 Bhat1)))
  have hε_le_ε0 : ε ≤ ε0 := by
    dsimp [ε]
    exact le_trans (min_le_left (min ε0 εhat0) (min ε1 εhat1)) (min_le_left ε0 εhat0)
  have hε_le_εhat0 : ε ≤ εhat0 := by
    dsimp [ε]
    exact le_trans (min_le_left (min ε0 εhat0) (min ε1 εhat1)) (min_le_right ε0 εhat0)
  have hε_le_ε1 : ε ≤ ε1 := by
    dsimp [ε]
    exact le_trans (min_le_right (min ε0 εhat0) (min ε1 εhat1)) (min_le_left ε1 εhat1)
  have hε_le_εhat1 : ε ≤ εhat1 := by
    dsimp [ε]
    exact le_trans (min_le_right (min ε0 εhat0) (min ε1 εhat1)) (min_le_right ε1 εhat1)
  have hB0_le_B : B0 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left B0 Bhat0) (le_max_left (max B0 Bhat0) (max B1 Bhat1))
  have hBhat0_le_B : Bhat0 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right B0 Bhat0) (le_max_left (max B0 Bhat0) (max B1 Bhat1))
  have hB1_le_B : B1 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left B1 Bhat1) (le_max_right (max B0 Bhat0) (max B1 Bhat1))
  have hBhat1_le_B : Bhat1 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right B1 Bhat1) (le_max_right (max B0 Bhat0) (max B1 Bhat1))
  refine ⟨ε, B, hε_pos, hB_pos, ?_⟩
  dsimp [SinkhornIteratesInUniformBox]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    exact ⟨le_trans hε_le_ε0 (hbox0 n i).1, le_trans (hbox0 n i).2 hB0_le_B⟩
  · intro n i
    exact ⟨le_trans hε_le_εhat0 (hboxhat0 n i).1, le_trans (hboxhat0 n i).2 hBhat0_le_B⟩
  · intro n i
    exact ⟨le_trans hε_le_ε1 (hbox1 n i).1, le_trans (hbox1 n i).2 hB1_le_B⟩
  · intro n i
    exact ⟨le_trans hε_le_εhat1 (hboxhat1 n i).1, le_trans (hboxhat1 n i).2 hBhat1_le_B⟩

/-- Uniform upper/lower bounds for gauge-normalized finite Sinkhorn iterates.

This is the first compactness input.  Strict positivity of the data and the gauge give a single
finite box containing all four iterate families.  The proof is factored through four directional
estimates so follow-on agents can attack the estimates independently. -/
theorem sinkhorn_gauge_normalized_uniform_bounds {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (G : ι → ι → ℝ)
    (φ0Iter φhat0Iter φ1Iter φhat1Iter : ℕ → ι → ℝ)
    (φ0 φhat0 φ1 φhat1 : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hG : ∀ i j, 0 < G i j)
    (hiter : IsFiniteSinkhornIterateSystem p q G φ0Iter φhat0Iter φ1Iter φhat1Iter)
    (hgauge : IsFiniteSinkhornGaugeNormalized φ0Iter φhat0Iter φ1Iter φhat1Iter
      φ0 φhat0 φ1 φhat1) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      (∀ n i, ε ≤ φ0Iter n i ∧ φ0Iter n i ≤ B) ∧
      (∀ n i, ε ≤ φhat0Iter n i ∧ φhat0Iter n i ≤ B) ∧
      (∀ n j, ε ≤ φ1Iter n j ∧ φ1Iter n j ≤ B) ∧
      (∀ n j, ε ≤ φhat1Iter n j ∧ φhat1Iter n j ≤ B) := by
  have hφ0 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ0Iter ε B :=
    sinkhorn_gauge_normalized_left_forward_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter φ0 φhat0 φ1 φhat1 hp hq hG hiter hgauge
  have hφhat0 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat0Iter ε B :=
    sinkhorn_hatted_left_bounds_from_left_forward_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter hp hq hG hiter hφ0
  have hφhat1 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φhat1Iter ε B :=
    sinkhorn_hatted_right_bounds_from_hatted_left_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter hp hq hG hiter hφhat0
  have hφ1 : ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ SinkhornPhaseInUniformBox φ1Iter ε B :=
    sinkhorn_right_forward_bounds_from_hatted_right_bounds p q G
      φ0Iter φhat0Iter φ1Iter φhat1Iter hp hq hG hiter hφhat1
  obtain ⟨ε, B, hε, hB, hbox⟩ :=
    sinkhorn_common_box_of_phase_boxes φ0Iter φhat0Iter φ1Iter φhat1Iter
      hφ0 hφhat0 hφ1 hφhat1
  exact ⟨ε, B, hε, hB, hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2⟩

end ChenGeorgiouPavon2021
