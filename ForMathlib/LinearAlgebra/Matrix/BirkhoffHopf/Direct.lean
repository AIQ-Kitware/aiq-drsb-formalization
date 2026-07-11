/-
# Birkhoff--Hopf projective contraction: the direct Doeblin / weighted-average proof

The AI-discovered elementary contraction proof for a strictly positive finite kernel.  It does
**not** follow Carroll's `n → 2` linear-programming reduction nor the Eveson--Nussbaum
two-dimensional subspace reduction (that is the separate `PaperRoute` development).  Instead it
sums the pairwise weight hypothesis into a pointwise *Doeblin condition*, from which two linear
facts force a scalar Möbius bound, converted by `log_mobius_le_one_sub_mul_log` into the
coarse coefficient `(B - 1) / B`.

All the shared projective-kernel vocabulary lives in `BirkhoffHopf.Basic`; this file imports it
and adds only the contraction chain, culminating in `positive_kernel_birkhoff_hopf_contraction`
and the certified-coefficient seams Franklin--Lorenz consumes.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.Basic

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix

/-- Scalar Möbius bound behind the weighted-average Birkhoff estimate.

For `R ≥ 1` and `0 < lam ≤ 1`, `(lam + R) / (1 + lam * R) ≤ R ^ (1 - lam)`, in log form.

The proof is calculus-free.  Weighted AM--GM on `(R⁻¹, 1)` with weights `(1 - lam, lam)` gives
`R / ((1 - lam) + lam * R) ≤ R ^ (1 - lam)`, and the remaining comparison is the polynomial identity
`R * (1 + lam * R) - (lam + R) * ((1 - lam) + lam * R) = lam * (R - 1) * (1 - lam)`. -/
theorem log_mobius_le_one_sub_mul_log {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hR : 1 ≤ R) :
    Real.log ((lam + R) / (1 + lam * R)) ≤ (1 - lam) * Real.log R := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hden : (0 : ℝ) < 1 + lam * R := by nlinarith
  have hd2 : (0 : ℝ) < (1 - lam) + lam * R := by nlinarith
  set ρ : ℝ := R ^ (1 - lam) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hRpos _
  have hAM := Real.geom_mean_le_arith_mean2_weighted
    (by linarith : (0 : ℝ) ≤ 1 - lam) (le_of_lt hlam0)
    (by positivity : (0 : ℝ) ≤ R⁻¹) (by norm_num : (0 : ℝ) ≤ 1) (by ring)
  rw [Real.inv_rpow (le_of_lt hRpos), Real.one_rpow] at hAM
  simp only [mul_one] at hAM
  have hAM2 : (1 - lam) * R⁻¹ + lam = ((1 - lam) + lam * R) / R := by field_simp
  rw [hAM2] at hAM
  have hAM3 : ρ⁻¹ * R ≤ (1 - lam) + lam * R := (le_div_iff₀ hRpos).mp hAM
  have hA : R ≤ ρ * ((1 - lam) + lam * R) := by
    have h := mul_le_mul_of_nonneg_left hAM3 (le_of_lt hρpos)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hρpos), one_mul] at h
    exact h
  have hpoly : (lam + R) * ((1 - lam) + lam * R) ≤ R * (1 + lam * R) := by
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt hlam0) (sub_nonneg.mpr hR))
      (sub_nonneg.mpr hlam1)]
  have hkey : (lam + R) / (1 + lam * R) ≤ ρ := by
    rw [div_le_iff₀ hden]
    have h1 : R * (1 + lam * R) ≤ (ρ * (1 + lam * R)) * ((1 - lam) + lam * R) := by
      nlinarith [mul_le_mul_of_nonneg_right hA (le_of_lt hden)]
    nlinarith [hpoly, h1, hd2]
  calc Real.log ((lam + R) / (1 + lam * R))
      ≤ Real.log ρ := Real.log_le_log (by positivity) hkey
    _ = (1 - lam) * Real.log R := by rw [hρ, Real.log_rpow hRpos]

/-- Finite-simplex weighted-average Birkhoff inequality with an abstract input diameter `D`.

This is the analytic core of the finite Birkhoff--Hopf contraction.  The projective spread of `x`
and `y` is supplied as pairwise log bounds `hxy`, and the row comparability of `a` and `b` is
supplied as `hweight`.

The proof does **not** go through Carroll's `n → 2` linear-programming reduction, nor through the
Eveson--Nussbaum two-dimensional subspace reduction.  Writing `t j = x j / y j` and normalizing
`p j ∝ a j * y j`, `q j ∝ b j * y j` into probability vectors, the goal reads
`log (E_p[t] / E_q[t]) ≤ ((B-1)/B) * D`, and:

1. **summing** `hweight` over one index collapses it to the pointwise *Doeblin condition*
   `a j * Q ≤ B * (b j * V)` and its mirror — this is what replaces the LP step;
2. hence `p - q/B` and `q - p/B` are nonnegative with total mass `1 - 1/B`, giving the two linear
   facts `u ≤ lam*v + (1-lam)*M` and `v ≥ lam*u + (1-lam)*m` for `lam = 1/B`, which alone force
   `u / v ≤ (lam + R) / (1 + lam * R)` with `R = M / m`;
3. `log_mobius_le_one_sub_mul_log` converts that into `(1 - lam) * log R ≤ (1 - lam) * D`.

The coarseness of `(B-1)/B` (versus the sharp Birkhoff constant `(B-1)/(B+1)`) is exactly what makes
step 3 elementary.

This `_core` form carries the *minimal* hypotheses actually used in the proof: notably it needs no
`0 ≤ D` sign condition. Under the pairwise hypotheses (`hweight`, `hxy`) and nonemptiness of `κ`, a
negative `D` may simply be impossible; the `_core` statement makes no positive claim about that
regime, it merely does not assume it. The source/context-facing wrapper
`finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound` retains `0 ≤ D`. -/
theorem finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound_core {κ : Type*}
    [Fintype κ] [Nonempty κ]
    (a b x y : κ → ℝ) (B D : ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hB : 1 ≤ B)
    (hweight : ∀ j j' : κ, a j * b j' ≤ B * (b j * a j'))
    (hxy : ∀ j j' : κ, Real.log ((x j * y j') / (x j' * y j)) ≤ D) :
    Real.log (((∑ j : κ, a j * x j) * (∑ j : κ, b j * y j)) /
        ((∑ j : κ, b j * x j) * (∑ j : κ, a j * y j))) ≤
      ((B - 1) / B) * D := by
  classical
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  set lam : ℝ := 1 / B with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hBpos]; exact hB
  have hcoef : (B - 1) / B = 1 - lam := by rw [hlam]; field_simp
  set U := ∑ j : κ, a j * x j with hU
  set V := ∑ j : κ, a j * y j with hV
  set P := ∑ j : κ, b j * x j with hP
  set Q := ∑ j : κ, b j * y j with hQ
  have hUpos : 0 < U := Finset.sum_pos (fun j _ => mul_pos (ha j) (hx j)) Finset.univ_nonempty
  have hVpos : 0 < V := Finset.sum_pos (fun j _ => mul_pos (ha j) (hy j)) Finset.univ_nonempty
  have hPpos : 0 < P := Finset.sum_pos (fun j _ => mul_pos (hb j) (hx j)) Finset.univ_nonempty
  have hQpos : 0 < Q := Finset.sum_pos (fun j _ => mul_pos (hb j) (hy j)) Finset.univ_nonempty
  -- The Doeblin conditions: sum the pairwise weight hypothesis against `y`.
  have hDoeb : ∀ j, a j * Q ≤ B * (b j * V) := by
    intro j
    calc a j * Q = ∑ j' : κ, (a j * b j') * y j' := by
          rw [hQ, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j' _ => by ring)
      _ ≤ ∑ j' : κ, (B * (b j * a j')) * y j' :=
          Finset.sum_le_sum (fun j' _ =>
            mul_le_mul_of_nonneg_right (hweight j j') (le_of_lt (hy j')))
      _ = B * (b j * V) := by
          rw [hV, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j' _ => by ring)
  have hDoeb' : ∀ j, b j * V ≤ B * (a j * Q) := by
    intro j
    calc b j * V = ∑ j' : κ, (a j' * b j) * y j' := by
          rw [hV, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j' _ => by ring)
      _ ≤ ∑ j' : κ, (B * (b j' * a j)) * y j' :=
          Finset.sum_le_sum (fun j' _ =>
            mul_le_mul_of_nonneg_right (hweight j' j) (le_of_lt (hy j')))
      _ = B * (a j * Q) := by
          rw [hQ, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j' _ => by ring)
  -- Extremes of the ratio `t = x / y`.
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
  set W : ℝ := V * Q with hW
  have hWpos : 0 < W := mul_pos hVpos hQpos
  have hc_nonneg : ∀ j, 0 ≤ a j * Q - lam * (b j * V) := by
    intro j
    have h2 : lam * (b j * V) ≤ lam * (B * (a j * Q)) :=
      mul_le_mul_of_nonneg_left (hDoeb' j) (le_of_lt hlam0)
    have h3 : lam * (B * (a j * Q)) = a j * Q := by rw [hlam]; field_simp
    rw [h3] at h2; linarith
  have hd_nonneg : ∀ j, 0 ≤ b j * V - lam * (a j * Q) := by
    intro j
    have h2 : lam * (a j * Q) ≤ lam * (B * (b j * V)) :=
      mul_le_mul_of_nonneg_left (hDoeb j) (le_of_lt hlam0)
    have h3 : lam * (B * (b j * V)) = b j * V := by rw [hlam]; field_simp
    rw [h3] at h2; linarith
  -- `u ≤ lam * v + (1 - lam) * M`, cleared of denominators.
  have step_i : U * Q - lam * (P * V) ≤ (1 - lam) * (M * W) := by
    have hsum : ∑ j : κ, x j * (a j * Q - lam * (b j * V))
        ≤ ∑ j : κ, (M * y j) * (a j * Q - lam * (b j * V)) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hxM j) (hc_nonneg j))
    have hL : ∑ j : κ, x j * (a j * Q - lam * (b j * V)) = U * Q - lam * (P * V) := by
      rw [hU, hP, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hRr : ∑ j : κ, (M * y j) * (a j * Q - lam * (b j * V)) = (1 - lam) * (M * W) := by
      rw [hW, hV, hQ]
      have e : ∀ j : κ, (M * y j) * (a j * (∑ j' : κ, b j' * y j')
            - lam * (b j * (∑ j' : κ, a j' * y j')))
          = (M * (∑ j' : κ, b j' * y j')) * (a j * y j)
            - (lam * M * (∑ j' : κ, a j' * y j')) * (b j * y j) := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [hL, hRr] at hsum
    exact hsum
  -- `v ≥ lam * u + (1 - lam) * m`, cleared of denominators.
  have step_ii : (1 - lam) * (m * W) ≤ P * V - lam * (U * Q) := by
    have hsum : ∑ j : κ, (m * y j) * (b j * V - lam * (a j * Q))
        ≤ ∑ j : κ, x j * (b j * V - lam * (a j * Q)) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hxm j) (hd_nonneg j))
    have hL : ∑ j : κ, (m * y j) * (b j * V - lam * (a j * Q)) = (1 - lam) * (m * W) := by
      rw [hW, hV, hQ]
      have e : ∀ j : κ, (m * y j) * (b j * (∑ j' : κ, a j' * y j')
            - lam * (a j * (∑ j' : κ, b j' * y j')))
          = (m * (∑ j' : κ, a j' * y j')) * (b j * y j)
            - (lam * m * (∑ j' : κ, b j' * y j')) * (a j * y j) := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    have hRr : ∑ j : κ, x j * (b j * V - lam * (a j * Q)) = P * V - lam * (U * Q) := by
      rw [hU, hP, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hL, hRr] at hsum
    exact hsum
  -- The two linear facts force the Möbius bound on `u / v`.
  set R : ℝ := M / m with hRdef
  have hR1 : 1 ≤ R := (one_le_div hmpos).mpr hmM
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hMeq : M = R * m := by rw [hRdef]; field_simp
  have hdenR : (0 : ℝ) < 1 + lam * R := by nlinarith
  have hcross : (U * Q) * (1 + lam * R) ≤ (P * V) * (lam + R) := by
    have hb2 : R * ((1 - lam) * (m * W)) ≤ R * (P * V - lam * (U * Q)) :=
      mul_le_mul_of_nonneg_left step_ii hR0
    have ha2 : U * Q - lam * (P * V) ≤ R * ((1 - lam) * (m * W)) := by
      calc U * Q - lam * (P * V) ≤ (1 - lam) * (M * W) := step_i
        _ = R * ((1 - lam) * (m * W)) := by rw [hMeq]; ring
    nlinarith [le_trans ha2 hb2]
  have hfrac : (U * Q) / (P * V) ≤ (lam + R) / (1 + lam * R) := by
    rw [div_le_div_iff₀ (mul_pos hPpos hVpos) hdenR]
    linarith [hcross]
  have hReq : R = (x jM * y jm) / (x jm * y jM) := by
    rw [hRdef, hMdef, hm]
    field_simp
  have hlogR : Real.log R ≤ D := by rw [hReq]; exact hxy jM jm
  rw [hcoef]
  calc Real.log ((U * Q) / (P * V))
      ≤ Real.log ((lam + R) / (1 + lam * R)) :=
        Real.log_le_log (div_pos (mul_pos hUpos hQpos) (mul_pos hPpos hVpos)) hfrac
    _ ≤ (1 - lam) * Real.log R := log_mobius_le_one_sub_mul_log hlam0 hlam1 hR1
    _ ≤ (1 - lam) * D := mul_le_mul_of_nonneg_left hlogR (by linarith)

/-- Source/context-facing wrapper for
`finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound_core`.

The extra `_hD : 0 ≤ D` is retained for compatibility and source fidelity — the elementary
Birkhoff--Hopf presentations state the pairwise-bounded scalar core with `D` a nonnegative diameter.
It is **not** a mathematical premise of the estimate: the proof lives entirely in the `_core` lemma,
which needs no sign condition on `D`. -/
theorem finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound {κ : Type*}
    [Fintype κ] [Nonempty κ]
    (a b x y : κ → ℝ) (B D : ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hB : 1 ≤ B) (_hD : 0 ≤ D)
    (hweight : ∀ j j' : κ, a j * b j' ≤ B * (b j * a j'))
    (hxy : ∀ j j' : κ, Real.log ((x j * y j') / (x j' * y j)) ≤ D) :
    Real.log (((∑ j : κ, a j * x j) * (∑ j : κ, b j * y j)) /
        ((∑ j : κ, b j * x j) * (∑ j : κ, a j * y j))) ≤
      ((B - 1) / B) * D :=
  finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound_core
    a b x y B D ha hb hx hy hB hweight hxy

/-- Two-point weighted-average Birkhoff inequality.

The elementary proofs of Birkhoff--Hopf treat this two-atom case as the irreducible scalar core, and
reduce the finite-simplex inequality to it. In the Doeblin development above, it follows by
instantiating the finite-simplex theorem at `κ = Fin 2`; `1 ≤ B` and `0 ≤ D` supply the diagonal
instances of its hypotheses. -/
theorem two_point_weighted_average_log_crossratio_contraction_of_crossratio_bound
    (a₀ a₁ b₀ b₁ x₀ x₁ y₀ y₁ B D : ℝ)
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁) (hy₀ : 0 < y₀) (hy₁ : 0 < y₁)
    (hB : 1 ≤ B) (hD : 0 ≤ D)
    (hweight₀₁ : a₀ * b₁ ≤ B * (b₀ * a₁))
    (hweight₁₀ : a₁ * b₀ ≤ B * (b₁ * a₀))
    (hxy₀₁ : Real.log ((x₀ * y₁) / (x₁ * y₀)) ≤ D)
    (hxy₁₀ : Real.log ((x₁ * y₀) / (x₀ * y₁)) ≤ D) :
    Real.log ((((a₀ * x₀ + a₁ * x₁) * (b₀ * y₀ + b₁ * y₁)) /
        ((b₀ * x₀ + b₁ * x₁) * (a₀ * y₀ + a₁ * y₁)))) ≤
      ((B - 1) / B) * D := by
  have key := finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound_core
    (κ := Fin 2) ![a₀, a₁] ![b₀, b₁] ![x₀, x₁] ![y₀, y₁] B D
    (by
      intro j
      fin_cases j
      · exact ha₀
      · exact ha₁)
    (by
      intro j
      fin_cases j
      · exact hb₀
      · exact hb₁)
    (by
      intro j
      fin_cases j
      · exact hx₀
      · exact hx₁)
    (by
      intro j
      fin_cases j
      · exact hy₀
      · exact hy₁)
    hB
    (by
      intro j j'
      fin_cases j <;> fin_cases j'
      · show a₀ * b₀ ≤ B * (b₀ * a₀); nlinarith [mul_pos hb₀ ha₀]
      · show a₀ * b₁ ≤ B * (b₀ * a₁); exact hweight₀₁
      · show a₁ * b₀ ≤ B * (b₁ * a₀); exact hweight₁₀
      · show a₁ * b₁ ≤ B * (b₁ * a₁); nlinarith [mul_pos hb₁ ha₁])
    (by
      intro j j'
      fin_cases j <;> fin_cases j'
      · show Real.log ((x₀ * y₀) / (x₀ * y₀)) ≤ D
        rw [div_self (by positivity), Real.log_one]; exact hD
      · show Real.log ((x₀ * y₁) / (x₁ * y₀)) ≤ D; exact hxy₀₁
      · show Real.log ((x₁ * y₀) / (x₀ * y₁)) ≤ D; exact hxy₁₀
      · show Real.log ((x₁ * y₁) / (x₁ * y₁)) ≤ D
        rw [div_self (by positivity), Real.log_one]; exact hD)
  simpa [Fin.sum_univ_two] using key

/-- Weighted-average form of the finite Birkhoff--Hopf scalar core.

This theorem specializes the abstract-diameter finite-simplex inequality with
`D = finiteHilbertProjectiveLogSpread x y`. -/
theorem finite_weighted_average_log_crossratio_contraction_of_crossratio_bound {κ : Type*}
    [Fintype κ] [Nonempty κ]
    (a b x y : κ → ℝ) (B : ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hB : 1 ≤ B)
    (hweight : ∀ j j' : κ, a j * b j' ≤ B * (b j * a j')) :
    Real.log (((∑ j : κ, a j * x j) * (∑ j : κ, b j * y j)) /
        ((∑ j : κ, b j * x j) * (∑ j : κ, a j * y j))) ≤
      ((B - 1) / B) * finiteHilbertProjectiveLogSpread x y := by
  exact finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound_core
    (a := a) (b := b) (x := x) (y := y)
    (B := B) (D := finiteHilbertProjectiveLogSpread x y)
    ha hb hx hy hB
    hweight
    (fun j j' => finiteHilbertProjectiveLogSpread_pair_le x y j j')

/-- Pointwise four-coordinate form of Birkhoff's oscillation estimate.

This is the matrix instantiation of the weighted-average scalar core above.  Its substantive input
is the finite weighted-average Birkhoff--Hopf inequality
`finite_weighted_average_log_crossratio_contraction_of_crossratio_bound`.

This `_of_crossratio_bound` form carries the minimal hypotheses: the estimate is proved from strict
positivity and the explicit pointwise cross-ratio bound
(`positive_kernel_pointwise_crossRatioBounded`), **not** from the Hilbert-log-diameter certificate
`PositiveKernelApplyHilbertLogDiameterBounded`. The source/context-facing wrapper
`..._of_apply_hilbert_log_diameter_bound` re-adds that certificate. -/
theorem positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_crossratio_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (x y : κ → ℝ)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (i i' : ι) :
    Real.log (((positiveKernelApply G x i) * (positiveKernelApply G y i')) /
        ((positiveKernelApply G x i') * (positiveKernelApply G y i))) ≤
      positiveKernelBirkhoffCoefficient G * finiteHilbertProjectiveLogSpread x y := by
  classical
  have hcore :=
    finite_weighted_average_log_crossratio_contraction_of_crossratio_bound
      (a := fun j : κ => G i j)
      (b := fun j : κ => G i' j)
      (x := x)
      (y := y)
      (B := positiveKernelCrossRatioBound G)
      (fun j => hG i j)
      (fun j => hG i' j)
      hx
      hy
      (positiveKernelCrossRatioBound_one_le G hG)
      (positive_kernel_pointwise_crossRatioBounded G hG i i')
  simpa [positiveKernelApply, positiveKernelBirkhoffCoefficient] using hcore

/-- Source/context-facing wrapper for
`positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_crossratio_bound`.

The `_hdiam : PositiveKernelApplyHilbertLogDiameterBounded ...` is compatibility/context data, **not**
a used mathematical premise: the pointwise estimate is derived from the explicit cross-ratio bound in
the `_of_crossratio_bound` core, not from the diameter certificate. -/
theorem positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_apply_hilbert_log_diameter_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (_hdiam : PositiveKernelApplyHilbertLogDiameterBounded G
      (Real.log (positiveKernelCrossRatioBound G)))
    (x y : κ → ℝ)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (i i' : ι) :
    Real.log (((positiveKernelApply G x i) * (positiveKernelApply G y i')) /
        ((positiveKernelApply G x i') * (positiveKernelApply G y i))) ≤
      positiveKernelBirkhoffCoefficient G * finiteHilbertProjectiveLogSpread x y :=
  positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_crossratio_bound
    G hG x y hx hy i i'

/-- Birkhoff's oscillation estimate from finite image diameter.

The only nontrivial ingredient is the pointwise four-coordinate oscillation estimate above.  This
wrapper just packages those pointwise inequalities into the finite supremum defining Hilbert
projective spread.  The coefficient here is the deliberately coarse explicit coefficient
`(B - 1) / B`, which is above the standard `tanh (Δ / 4)` coefficient when `B = exp Δ`.

The `hdiam` diameter certificate is threaded here as source-shaped API only.  The pointwise estimate
that does the real work is proved by the explicit cross-ratio machinery in
`..._pointwise_log_crossratio_contraction_of_crossratio_bound`, not from `hdiam`. -/
theorem positive_kernel_birkhoff_hopf_contraction_of_apply_hilbert_log_diameter_bound
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hdiam : PositiveKernelApplyHilbertLogDiameterBounded G
      (Real.log (positiveKernelCrossRatioBound G))) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  classical
  unfold IsBirkhoffHopfContractionCoefficient
  intro x y hx hy
  apply finiteHilbertProjectiveLogSpread_le_of_forall_pair
  intro i i'
  exact
    positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_apply_hilbert_log_diameter_bound
      G hG hdiam x y hx hy i i'

/-- Birkhoff's oscillation estimate once the image-cone cross-ratio is bounded.

This is the analytic/projective-metric subgoal: turn the finite image cross-ratio bound into
Hilbert projective contraction with the explicit coefficient. The proof composes the finite image
diameter bound from cross-ratio control with the Birkhoff--Hopf oscillation estimate for a finite
image diameter. -/
theorem positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j)
    (hbound : PositiveKernelApplyCrossRatioBounded G) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  exact positive_kernel_birkhoff_hopf_contraction_of_apply_hilbert_log_diameter_bound G hG
    (positive_kernel_apply_hilbert_log_diameter_bound_of_apply_crossratio_bound G hG hbound)

/-- The actual Birkhoff--Hopf contraction theorem for a strictly positive finite kernel.

This wrapper combines two results:

1. the finite double-sum image cross-ratio bound,
   `positive_kernel_apply_crossRatioBounded`;
2. the projective oscillation estimate,
   `positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound`.

This separates the algebraic image cross-ratio estimate from the analytic Hilbert-metric bound. -/
theorem positive_kernel_birkhoff_hopf_contraction {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  exact positive_kernel_birkhoff_hopf_contraction_of_apply_crossratio_bound G hG
    (positive_kernel_apply_crossRatioBounded G hG)

/-- The finite positive-kernel Birkhoff--Hopf contraction theorem without nonemptiness assumptions.

The substance is `positive_kernel_birkhoff_hopf_contraction`, which needs both index types nonempty.
An empty coordinate type is not a positive cone, and every degenerate branch below reduces to
`0 ≤ γ * 0`. -/
theorem positive_kernel_birkhoff_hopf_contraction_of_fintype {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j) :
    IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G) := by
  classical
  obtain ⟨hγ_nonneg, _⟩ := positiveKernelBirkhoffCoefficient_nonneg_lt_one G hG
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : IsEmpty ι := hι
    intro x y hx hy
    have hL : finiteHilbertProjectiveLogSpread
        (positiveKernelApply G x) (positiveKernelApply G y) = 0 := by
      unfold finiteHilbertProjectiveLogSpread
      rw [Set.range_eq_empty, Real.sSup_empty]
    rw [hL]
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · haveI : IsEmpty κ := hκ
      have hR : finiteHilbertProjectiveLogSpread x y = 0 := by
        unfold finiteHilbertProjectiveLogSpread
        rw [Set.range_eq_empty, Real.sSup_empty]
      rw [hR]
      simp
    · exact mul_nonneg hγ_nonneg (finiteHilbertProjectiveLogSpread_nonneg_of_pos x y hx hy)
  · haveI : Nonempty ι := hι
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · haveI : IsEmpty κ := hκ
      intro x y _hx _hy
      have hzx : positiveKernelApply G x = fun _ => (0 : ℝ) := by
        funext i; simp [positiveKernelApply]
      have hzy : positiveKernelApply G y = fun _ => (0 : ℝ) := by
        funext i; simp [positiveKernelApply]
      have hR : finiteHilbertProjectiveLogSpread x y = 0 := by
        unfold finiteHilbertProjectiveLogSpread
        rw [Set.range_eq_empty, Real.sSup_empty]
      rw [hzx, hzy, hR]
      unfold finiteHilbertProjectiveLogSpread
      simp
    · haveI : Nonempty κ := hκ
      exact positive_kernel_birkhoff_hopf_contraction G hG

/-- Certified Birkhoff--Hopf coefficient seam for a strictly positive finite kernel.

This is the theorem shape that Franklin--Lorenz consumes: the chosen `γ` is not merely a number in
`[0,1)`, but a genuine Hilbert-projective contraction coefficient for `G`.  It is parked here,
rather than in the Sinkhorn-specific files, so that the Birkhoff--Hopf work stays paper-agnostic
and Mathlib-facing. -/
theorem positive_kernel_strict_birkhoff_contraction_coefficient {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j) :
    ∃ γ : ℝ, IsStrictBirkhoffHopfContractionCoefficient G γ := by
  obtain ⟨hγ_nonneg, hγ_lt_one⟩ := positiveKernelBirkhoffCoefficient_nonneg_lt_one G hG
  exact ⟨positiveKernelBirkhoffCoefficient G, hγ_nonneg, hγ_lt_one,
    positive_kernel_birkhoff_hopf_contraction_of_fintype G hG⟩

/-- Certified Birkhoff--Hopf coefficient seam covering a kernel **and its transpose** at once.

Alternating scaling algorithms (Sinkhorn, Franklin--Lorenz) apply `G` on one half-step and `Gᵀ` on
the other, so a coefficient for `G` alone is not enough to run the contraction recursion.  It would
be circular to derive `Gᵀ`'s coefficient from `G`'s: that needs `γ` to be the *sharp* Birkhoff
constant.  Instead the explicit coefficient is transpose-invariant, so one number serves both. -/
theorem positive_kernel_strict_birkhoff_contraction_coefficient_transpose {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ)
    (hG : ∀ i j, 0 < G i j) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧
      IsBirkhoffHopfContractionCoefficient G γ ∧
      IsBirkhoffHopfContractionCoefficient (fun j i => G i j) γ := by
  obtain ⟨hγ_nonneg, hγ_lt_one⟩ := positiveKernelBirkhoffCoefficient_nonneg_lt_one G hG
  refine ⟨positiveKernelBirkhoffCoefficient G, hγ_nonneg, hγ_lt_one,
    positive_kernel_birkhoff_hopf_contraction_of_fintype G hG, ?_⟩
  have h := positive_kernel_birkhoff_hopf_contraction_of_fintype
    (fun j i => G i j) (fun j i => hG i j)
  rwa [positiveKernelBirkhoffCoefficient_transpose] at h

end ForMathlib.Matrix
