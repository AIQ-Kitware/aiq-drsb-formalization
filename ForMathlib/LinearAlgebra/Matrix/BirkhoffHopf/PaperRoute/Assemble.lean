/-
# Assembly theorem for the paper-route Birkhoff--Hopf proof

This file is the spine of the Eveson--Nussbaum route.  It matches the finite-dimensional chain
described in the modernization note:

positive matrix
  -> image cone is the nonnegative hull of its positive columns
  -> convex-hull diameter equals generator diameter
  -> positive-matrix diameter is the four-index cross-ratio formula
  -> reduce contraction to the normalized two-by-two calculation
  -> export the current `IsBirkhoffHopfContractionCoefficient` theorem.

It is an *independent* proof of the same seam that `ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf`
proves by the Doeblin/weighted-average route: nothing here imports that route's theorems.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.PositiveMatrixDiameter
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.TwoByTwo

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix
namespace BirkhoffHopf.PaperRoute

/-- Paper route Step 7: arbitrary finite positive matrices inherit the two-dimensional
Birkhoff--Hopf contraction.

Paper analogue: Eveson--Nussbaum Lemma 3.11, reduction to two-dimensional subspaces, together with
Theorem 5.3.

**Proof.**  Fix positive `x, y` and let `m`, `M` be the extreme values of the ratio `xⱼ / yⱼ`.  The
two vectors

  `p = G · (x - m y)`,  `q = G · (M y - x)`

lie in the image cone: they are nonnegative combinations of the columns of `G` with positive total
weight, so `hilbert_diameter_nonnegativeHull_le_generator_diameter` bounds their Hilbert distance by
the column diameter, hence by `log B`.  Moreover

  `p + q = (M - m) · (G y)`,  `M p + m q = (M - m) · (G x)`,

so the image cross-ratio of `G x` and `G y` at a pair `(i, i')` is the cross-ratio of the two-by-two
positive matrix `[[pᵢ, qᵢ], [pᵢ', qᵢ']]` applied to the vectors `(M, m)` and `(1, 1)`.  The
cross-ratio of that matrix is pinched between `1/B` and `B`, so
`positive_twoByTwo_birkhoff_contraction_of_crossRatio_le` contracts by `(B - 1)/B` — which is exactly
`positiveKernelBirkhoffCoefficient G` — and the Hilbert distance of `(M, m)` from `(1, 1)` is
`log (M/m) ≤ finiteHilbertProjectiveLogSpread x y`. -/
theorem positiveKernel_birkhoff_contraction_from_twoByTwo {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  classical
  intro x y hx hy
  set B : ℝ := positiveKernelCrossRatioBound G with hBdef
  have hB : 1 ≤ B := positiveKernelCrossRatioBound_one_le G hG
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hγ : positiveKernelBirkhoffCoefficient G = (B - 1) / B := rfl
  have hγ0 : 0 ≤ (B - 1) / B := div_nonneg (by linarith) hBpos.le
  set P : ι → ℝ := positiveKernelApply G x with hP
  set Q : ι → ℝ := positiveKernelApply G y with hQ
  have hPpos : ∀ i, 0 < P i := fun i => positiveKernelApply_pos G hG x hx i
  have hQpos : ∀ i, 0 < Q i := fun i => positiveKernelApply_pos G hG y hy i
  have hspread_xy_nonneg : 0 ≤ finiteHilbertProjectiveLogSpread x y :=
    finiteHilbertProjectiveLogSpread_nonneg_of_pos x y hx hy
  -- extremes of the ratio `x / y`
  obtain ⟨jm, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset κ) (fun j => x j / y j) Finset.univ_nonempty
  obtain ⟨jM, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset κ) (fun j => x j / y j) Finset.univ_nonempty
  set m : ℝ := x jm / y jm with hm
  set M : ℝ := x jM / y jM with hMdef
  have hmpos : 0 < m := div_pos (hx jm) (hy jm)
  have hmM : m ≤ M := hmin jM (Finset.mem_univ jM)
  have hxm : ∀ j, m * y j ≤ x j := by
    intro j; have h := hmin j (Finset.mem_univ j); rw [le_div_iff₀ (hy j)] at h; linarith
  have hxM : ∀ j, x j ≤ M * y j := by
    intro j; have h := hmax j (Finset.mem_univ j); rw [div_le_iff₀ (hy j)] at h; linarith
  rcases eq_or_lt_of_le hmM with hEq | hlt
  · -- degenerate: `x = m • y`, so the image rays coincide
    have hxy : ∀ j, x j = m * y j := by
      intro j
      have h1 := hxm j
      have h2 := hxM j
      rw [← hEq] at h2
      linarith
    have hPQ : ∀ i, P i = m * Q i := by
      intro i
      rw [hP, hQ]
      unfold positiveKernelApply
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [hxy j]; ring)
    apply finiteHilbertProjectiveLogSpread_le_of_forall_pair
    intro i i'
    rw [hPQ i, hPQ i']
    have hne : m * Q i' * Q i ≠ 0 := by
      have := hQpos i; have := hQpos i'; positivity
    have hone : (m * Q i * Q i') / (m * Q i' * Q i) = 1 := by
      rw [show m * Q i * Q i' = m * Q i' * Q i from by ring, div_self hne]
    rw [hone, Real.log_one, hγ]
    exact mul_nonneg hγ0 hspread_xy_nonneg
  · -- nondegenerate: `M - m > 0`
    have hMm : 0 < M - m := sub_pos.mpr hlt
    set w₁ : κ → ℝ := fun j => x j - m * y j with hw₁def
    set w₂ : κ → ℝ := fun j => M * y j - x j with hw₂def
    have hw₁ : ∀ j, 0 ≤ w₁ j := fun j => sub_nonneg.mpr (hxm j)
    have hw₂ : ∀ j, 0 ≤ w₂ j := fun j => sub_nonneg.mpr (hxM j)
    have hw₁jM : 0 < w₁ jM := by
      rw [hw₁def]
      have : m * y jM < x jM := by
        rw [hMdef] at hlt
        rw [lt_div_iff₀ (hy jM)] at hlt
        linarith
      linarith
    have hw₂jm : 0 < w₂ jm := by
      rw [hw₂def]
      have : x jm < M * y jm := by
        rw [hm] at hlt
        rw [div_lt_iff₀ (hy jm)] at hlt
        linarith
      linarith
    have hw₁sum : 0 < ∑ j : κ, w₁ j :=
      Finset.sum_pos' (fun j _ => hw₁ j) ⟨jM, Finset.mem_univ jM, hw₁jM⟩
    have hw₂sum : 0 < ∑ j : κ, w₂ j :=
      Finset.sum_pos' (fun j _ => hw₂ j) ⟨jm, Finset.mem_univ jm, hw₂jm⟩
    -- the two image-cone generators
    set p : ι → ℝ := fun i => ∑ j : κ, w₁ j * (fun j i => G i j) j i with hpdef
    set q : ι → ℝ := fun i => ∑ j : κ, w₂ j * (fun j i => G i j) j i with hqdef
    have hppos : ∀ i, 0 < p i := fun i =>
      nonneg_combination_pos (fun j i => G i j) (fun j i => hG i j) w₁ hw₁ hw₁sum i
    have hqpos : ∀ i, 0 < q i := fun i =>
      nonneg_combination_pos (fun j i => G i j) (fun j i => hG i j) w₂ hw₂ hw₂sum i
    -- they lie in the image cone, so their Hilbert distance is at most `log B`
    have hpq_spread : finiteHilbertProjectiveLogSpread p q ≤ Real.log B :=
      hilbert_diameter_nonnegativeHull_le_generator_diameter
        (fun j i => G i j) (fun j i => hG i j) (Real.log B)
        (positiveKernel_column_diameter_le_crossratio_bound G hG) w₁ w₂ hw₁ hw₂ hw₁sum hw₂sum
    -- the two cone identities
    have hpv : ∀ i, p i = P i - m * Q i := by
      intro i
      rw [hpdef, hP, hQ]
      unfold positiveKernelApply
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [hw₁def]; ring)
    have hqv : ∀ i, q i = M * Q i - P i := by
      intro i
      rw [hqdef, hP, hQ]
      unfold positiveKernelApply
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [hw₂def]; ring)
    have hsum : ∀ i, p i + q i = (M - m) * Q i := by
      intro i; rw [hpv i, hqv i]; ring
    have hcomb : ∀ i, M * p i + m * q i = (M - m) * P i := by
      intro i; rw [hpv i, hqv i]; ring
    -- the pairwise cross-ratio bound for `p, q`
    have hpq_cross : ∀ i i' : ι, p i * q i' ≤ B * (q i * p i') := by
      intro i i'
      have habs := finiteHilbertProjectiveLogSpread_abs_pair_le p q hppos hqpos i i'
      have hlog : Real.log ((p i * q i') / (p i' * q i)) ≤ Real.log B := by
        refine le_trans (le_trans (le_abs_self _) habs) hpq_spread
      have hratio_pos : 0 < (p i * q i') / (p i' * q i) :=
        div_pos (mul_pos (hppos i) (hqpos i')) (mul_pos (hppos i') (hqpos i))
      have := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log hratio_pos, Real.exp_log hBpos] at this
      rw [div_le_iff₀ (mul_pos (hppos i') (hqpos i))] at this
      nlinarith [this]
    have hpq_cross' : ∀ i i' : ι, q i * p i' ≤ B * (p i * q i') := by
      intro i i'
      have habs := finiteHilbertProjectiveLogSpread_abs_pair_le p q hppos hqpos i i'
      have hlog : Real.log ((p i' * q i) / (p i * q i')) ≤ Real.log B := by
        have hneg : Real.log ((p i' * q i) / (p i * q i'))
            = -Real.log ((p i * q i') / (p i' * q i)) := by
          rw [← Real.log_inv]
          congr 1
          have := (hppos i).ne'; have := (hppos i').ne'
          have := (hqpos i).ne'; have := (hqpos i').ne'
          field_simp
        rw [hneg]
        exact le_trans (le_trans (neg_le_abs _) habs) hpq_spread
      have hratio_pos : 0 < (p i' * q i) / (p i * q i') :=
        div_pos (mul_pos (hppos i') (hqpos i)) (mul_pos (hppos i) (hqpos i'))
      have := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log hratio_pos, Real.exp_log hBpos] at this
      rw [div_le_iff₀ (mul_pos (hppos i) (hqpos i'))] at this
      nlinarith [this]
    -- `log (M/m) ≤ spread x y`
    have hMm_log : Real.log (M / m) ≤ finiteHilbertProjectiveLogSpread x y := by
      have hpair := finiteHilbertProjectiveLogSpread_pair_le x y jM jm
      have heq : (x jM * y jm) / (x jm * y jM) = M / m := by
        rw [hMdef, hm]
        have := (hx jm).ne'; have := (hy jM).ne'; have := (hy jm).ne'
        field_simp
        try ring
      rwa [heq] at hpair
    -- the two-by-two reduction, pair by pair
    rw [hγ]
    apply finiteHilbertProjectiveLogSpread_le_of_forall_pair
    intro i i'
    set A : Fin 2 → Fin 2 → ℝ :=
      fun a b => if a = 0 then (if b = 0 then p i else q i) else (if b = 0 then p i' else q i')
      with hAdef
    have hA00 : A 0 0 = p i := by simp [hAdef]
    have hA01 : A 0 1 = q i := by simp [hAdef]
    have hA10 : A 1 0 = p i' := by simp [hAdef]
    have hA11 : A 1 1 = q i' := by simp [hAdef]
    have hApos : ∀ a b : Fin 2, 0 < A a b := by
      intro a b
      rw [hAdef]
      dsimp only
      split_ifs
      · exact hppos i
      · exact hqpos i
      · exact hppos i'
      · exact hqpos i'
    have hA1 : A 0 0 * A 1 1 ≤ B * (A 0 1 * A 1 0) := by
      rw [hA00, hA01, hA10, hA11]; exact hpq_cross i i'
    have hA2 : A 0 1 * A 1 0 ≤ B * (A 0 0 * A 1 1) := by
      rw [hA00, hA01, hA10, hA11]; exact hpq_cross' i i'
    set z : Fin 2 → ℝ := ![M, m] with hzdef
    set w : Fin 2 → ℝ := ![1, 1] with hwdef
    have hzpos : ∀ b : Fin 2, 0 < z b := by
      intro b; fin_cases b
      · show 0 < M; linarith
      · show 0 < m; exact hmpos
    have hwpos : ∀ b : Fin 2, 0 < w b := by
      intro b; fin_cases b
      · show (0:ℝ) < 1; norm_num
      · show (0:ℝ) < 1; norm_num
    have hcontr := positive_twoByTwo_birkhoff_contraction_of_crossRatio_le A hApos B hB hA1 hA2
      z w hzpos hwpos
    -- evaluate the images
    have hAz0 : positiveKernelApply A z 0 = (M - m) * P i := by
      unfold positiveKernelApply
      rw [Fin.sum_univ_two, hA00, hA01]
      show p i * M + q i * m = (M - m) * P i
      rw [← hcomb i]; ring
    have hAz1 : positiveKernelApply A z 1 = (M - m) * P i' := by
      unfold positiveKernelApply
      rw [Fin.sum_univ_two, hA10, hA11]
      show p i' * M + q i' * m = (M - m) * P i'
      rw [← hcomb i']; ring
    have hAw0 : positiveKernelApply A w 0 = (M - m) * Q i := by
      unfold positiveKernelApply
      rw [Fin.sum_univ_two, hA00, hA01]
      show p i * 1 + q i * 1 = (M - m) * Q i
      rw [← hsum i]; ring
    have hAw1 : positiveKernelApply A w 1 = (M - m) * Q i' := by
      unfold positiveKernelApply
      rw [Fin.sum_univ_two, hA10, hA11]
      show p i' * 1 + q i' * 1 = (M - m) * Q i'
      rw [← hsum i']; ring
    -- the target log cross-ratio is dominated by the image spread of the two-by-two problem
    have hpair := finiteHilbertProjectiveLogSpread_pair_le
      (positiveKernelApply A z) (positiveKernelApply A w) 0 1
    rw [hAz0, hAz1, hAw0, hAw1] at hpair
    have hcancel : ((M - m) * P i * ((M - m) * Q i')) / ((M - m) * P i' * ((M - m) * Q i))
        = (P i * Q i') / (P i' * Q i) := by
      have := hMm.ne'
      have := (hPpos i').ne'; have := (hQpos i).ne'
      field_simp
      try ring
    rw [hcancel] at hpair
    -- and the source spread of `(M, m)` versus `(1, 1)` is `log (M/m)`
    have hzw : finiteHilbertProjectiveLogSpread z w ≤ Real.log (M / m) := by
      refine le_trans (spread_fin_two_le z w hzpos hwpos) ?_
      have h0 : z 0 = M := rfl
      have h1 : z 1 = m := rfl
      have h2 : w 0 = (1:ℝ) := rfl
      have h3 : w 1 = (1:ℝ) := rfl
      rw [h0, h1, h2, h3]
      have hrw : (M * 1) / (m * 1) = M / m := by ring
      have hnn : 0 ≤ Real.log (M / m) := Real.log_nonneg ((one_le_div hmpos).mpr hmM)
      rw [hrw, abs_of_nonneg hnn]
    calc Real.log ((P i * Q i') / (P i' * Q i))
        ≤ finiteHilbertProjectiveLogSpread (positiveKernelApply A z) (positiveKernelApply A w) :=
          hpair
      _ ≤ ((B - 1) / B) * finiteHilbertProjectiveLogSpread z w := hcontr
      _ ≤ ((B - 1) / B) * Real.log (M / m) := mul_le_mul_of_nonneg_left hzw hγ0
      _ ≤ ((B - 1) / B) * finiteHilbertProjectiveLogSpread x y :=
          mul_le_mul_of_nonneg_left hMm_log hγ0

/-- Paper route Step 8: public finite positive-kernel Birkhoff--Hopf contraction theorem.

This is an independent second proof of the theorem that
`ForMathlib.Matrix.positive_kernel_birkhoff_hopf_contraction` proves by the Doeblin route. -/
theorem positive_kernel_birkhoff_hopf_contraction_paper_route {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  exact positiveKernel_birkhoff_contraction_from_twoByTwo G hG

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
