/-
# Normalized two-by-two Birkhoff computation

This file stages the concrete calculus core of Eveson--Nussbaum Section 5.  After reducing a
positive two-dimensional problem by cone automorphisms, the normalized matrix is

  A_α = [[α, 1], [1, α]],  α > 1.

The contraction constant is `(α - 1) / (α + 1) = tanh ((log α) / 2)`, obtained by maximizing the
one-variable function

  φ(t) = ((α^2 - 1) * t) / ((α + t) * (α * t + 1)).
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.PositiveConeHilbert

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib.Matrix
namespace BirkhoffHopf.PaperRoute

/-- The normalized symmetric positive two-by-two kernel from Eveson--Nussbaum Section 5. -/
noncomputable def symmetricTwoByTwoKernel (α : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then α else 1

/-- The one-variable function whose maximum gives the normalized two-by-two contraction ratio. -/
noncomputable def symmetricTwoByTwoPhi (α t : ℝ) : ℝ :=
  ((α ^ 2 - 1) * t) / ((α + t) * (α * t + 1))

/-- Positivity of the normalized symmetric two-by-two kernel. -/
theorem symmetricTwoByTwoKernel_pos {α : ℝ} (hα : 1 < α) :
    ∀ i j : Fin 2, 0 < symmetricTwoByTwoKernel α i j := by
  intro i j
  unfold symmetricTwoByTwoKernel
  by_cases hij : i = j
  · simp [hij, lt_trans zero_lt_one hα]
  · simp [hij]

/-- Paper route Step 5: the elementary calculus maximum in the normalized two-by-two case.

Paper analogue: Eveson--Nussbaum Theorem 5.3, where `φ'(t) = 0` iff `t = 1`, and the maximum value
is `(α - 1) / (α + 1)`.  This should be attacked as a pure real-algebra/calculus lemma. -/
theorem symmetricTwoByTwoPhi_le {α t : ℝ} (hα : 1 < α) (ht : 0 < t) :
    symmetricTwoByTwoPhi α t ≤ (α - 1) / (α + 1) := by
  unfold symmetricTwoByTwoPhi
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hαm_pos : 0 < α - 1 := sub_pos.mpr hα
  have hαp_pos : 0 < α + 1 := by linarith
  have hden₁ : 0 < α + t := by linarith
  have hden₂ : 0 < α * t + 1 := by nlinarith [mul_pos hα_pos ht]
  have hden : 0 < (α + t) * (α * t + 1) := mul_pos hden₁ hden₂
  have hmain : ((α ^ 2 - 1) * t) * (α + 1) ≤
      (α - 1) * ((α + t) * (α * t + 1)) := by
    have hdiff :
        (α - 1) * ((α + t) * (α * t + 1)) -
            ((α ^ 2 - 1) * t) * (α + 1) =
          α * (α - 1) * (t - 1) ^ 2 := by
      ring
    have hnonneg : 0 ≤ α * (α - 1) * (t - 1) ^ 2 := by
      exact mul_nonneg (mul_nonneg (le_of_lt hα_pos) (le_of_lt hαm_pos))
        (sq_nonneg (t - 1))
    nlinarith
  have hscaled : (α ^ 2 - 1) * t ≤
      ((α - 1) / (α + 1)) * ((α + t) * (α * t + 1)) := by
    have hdiv := (le_div_iff₀ hαp_pos).2 hmain
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  exact (div_le_iff₀ hden).2 hscaled

/-- The normalized two-by-two coefficient lies in the strict Birkhoff range. -/
theorem symmetricTwoByTwoCoefficient_nonneg_lt_one {α : ℝ} (hα : 1 < α) :
    0 ≤ (α - 1) / (α + 1) ∧ (α - 1) / (α + 1) < 1 := by
  have hden_pos : 0 < α + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr (le_of_lt hα)) (le_of_lt hden_pos)
  · exact (div_lt_iff₀ hden_pos).2 (by linarith)

/-- First row of the normalized two-by-two kernel, written as a finite weighted average. -/
theorem positiveKernelApply_symmetricTwoByTwo_zero (α : ℝ) (x : Fin 2 → ℝ) :
    positiveKernelApply (symmetricTwoByTwoKernel α) x (0 : Fin 2) =
      α * x (0 : Fin 2) + x (1 : Fin 2) := by
  rw [positiveKernelApply, Fin.sum_univ_two]
  simp [symmetricTwoByTwoKernel]

/-- Second row of the normalized two-by-two kernel, written as a finite weighted average. -/
theorem positiveKernelApply_symmetricTwoByTwo_one (α : ℝ) (x : Fin 2 → ℝ) :
    positiveKernelApply (symmetricTwoByTwoKernel α) x (1 : Fin 2) =
      x (0 : Fin 2) + α * x (1 : Fin 2) := by
  rw [positiveKernelApply, Fin.sum_univ_two]
  simp [symmetricTwoByTwoKernel, add_comm]

/-- On `Fin 2` the Hilbert projective spread is exactly the absolute log cross-ratio of the two
coordinates: the `sSup` ranges over four ordered pairs, two of which are `log 1 = 0` and the other
two of which are `±L`. -/
theorem spread_fin_two_le (u w : Fin 2 → ℝ) (hu : ∀ i, 0 < u i) (hw : ∀ i, 0 < w i) :
    finiteHilbertProjectiveLogSpread u w
      ≤ |Real.log ((u 0 * w 1) / (u 1 * w 0))| := by
  apply finiteHilbertProjectiveLogSpread_le_of_forall_pair
  intro i i'
  have hneg : Real.log ((u 1 * w 0) / (u 0 * w 1)) = -Real.log ((u 0 * w 1) / (u 1 * w 0)) := by
    rw [← Real.log_inv]
    congr 1
    have := (hu 0).ne'; have := (hu 1).ne'; have := (hw 0).ne'; have := (hw 1).ne'
    field_simp
  fin_cases i <;> fin_cases i'
  · show Real.log ((u 0 * w 0) / (u 0 * w 0)) ≤ _
    rw [div_self (mul_pos (hu 0) (hw 0)).ne', Real.log_one]; exact abs_nonneg _
  · show Real.log ((u 0 * w 1) / (u 1 * w 0)) ≤ _
    exact le_abs_self _
  · show Real.log ((u 1 * w 0) / (u 0 * w 1)) ≤ _
    rw [hneg]; exact neg_le_abs _
  · show Real.log ((u 1 * w 1) / (u 1 * w 1)) ≤ _
    rw [div_self (mul_pos (hu 1) (hw 1)).ne', Real.log_one]; exact abs_nonneg _

/-- The one-variable Lipschitz core behind Eveson--Nussbaum Theorem 5.3.

In the logarithmic coordinate `t = log (x₀ / x₁)` the map `A_α` acts as
`g t = log (α e^t + 1) - log (e^t + α)`, whose derivative is exactly `symmetricTwoByTwoPhi α (e^t)`.
So `symmetricTwoByTwoPhi_le` bounds `‖g'‖` by `(α - 1)/(α + 1)`, and the mean value inequality makes
`g` Lipschitz with that constant. -/
theorem symmetricTwoByTwo_log_lipschitz {α : ℝ} (hα : 1 < α) (u v : ℝ) :
    |(Real.log (α * Real.exp u + 1) - Real.log (Real.exp u + α))
        - (Real.log (α * Real.exp v + 1) - Real.log (Real.exp v + α))|
      ≤ ((α - 1) / (α + 1)) * |u - v| := by
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hα2 : (0 : ℝ) < α ^ 2 - 1 := by nlinarith
  set g : ℝ → ℝ := fun t => Real.log (α * Real.exp t + 1) - Real.log (Real.exp t + α) with hg
  set k : ℝ := (α - 1) / (α + 1) with hk
  have hderiv : ∀ t : ℝ, HasDerivAt g
      ((α * Real.exp t) / (α * Real.exp t + 1) - (Real.exp t) / (Real.exp t + α)) t := by
    intro t
    have het : (0 : ℝ) < Real.exp t := Real.exp_pos t
    have h1 : HasDerivAt (fun s => α * Real.exp s + 1) (α * Real.exp t) t := by
      simpa using ((Real.hasDerivAt_exp t).const_mul α).add_const 1
    have h2 : HasDerivAt (fun s => Real.exp s + α) (Real.exp t) t :=
      (Real.hasDerivAt_exp t).add_const α
    have hne1 : α * Real.exp t + 1 ≠ 0 := by positivity
    have hne2 : Real.exp t + α ≠ 0 := by positivity
    exact (h1.log hne1).sub (h2.log hne2)
  have hbound : ∀ t ∈ (Set.univ : Set ℝ),
      ‖(α * Real.exp t) / (α * Real.exp t + 1) - (Real.exp t) / (Real.exp t + α)‖ ≤ k := by
    intro t _
    have het : (0 : ℝ) < Real.exp t := Real.exp_pos t
    have hd1 : (0 : ℝ) < α * Real.exp t + 1 := by positivity
    have hd2 : (0 : ℝ) < α + Real.exp t := by positivity
    -- the derivative *is* `symmetricTwoByTwoPhi α (exp t)`
    have hkey : (α * Real.exp t) / (α * Real.exp t + 1) - (Real.exp t) / (Real.exp t + α)
        = symmetricTwoByTwoPhi α (Real.exp t) := by
      unfold symmetricTwoByTwoPhi
      field_simp
      ring
    have hnn : 0 ≤ symmetricTwoByTwoPhi α (Real.exp t) := by
      unfold symmetricTwoByTwoPhi
      exact div_nonneg (mul_nonneg hα2.le het.le) (mul_pos hd2 hd1).le
    rw [Real.norm_eq_abs, hkey, abs_of_nonneg hnn]
    exact symmetricTwoByTwoPhi_le hα het
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g)
    (f' := fun t => (α * Real.exp t) / (α * Real.exp t + 1) - (Real.exp t) / (Real.exp t + α))
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound convex_univ (Set.mem_univ v) (Set.mem_univ u)
  simpa [hg, Real.norm_eq_abs] using hmvt

/-- Paper route Step 5: normalized two-by-two Birkhoff contraction.

Paper analogue: Eveson--Nussbaum Theorem 5.3,
`N(A_α) = k(A_α) = (α - 1)/(α + 1)`.

Passing to the logarithmic coordinate turns the projective action of `A_α` into the scalar map `g`
of `symmetricTwoByTwo_log_lipschitz`, and on `Fin 2` the Hilbert spread is the absolute log
cross-ratio, so the contraction is exactly that map's Lipschitz bound. -/
theorem symmetricTwoByTwo_birkhoff_contraction {α : ℝ} (hα : 1 < α) :
    IsBirkhoffHopfContractionCoefficient
      (symmetricTwoByTwoKernel α) ((α - 1) / (α + 1)) := by
  intro x y hx hy
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hk0 : 0 ≤ (α - 1) / (α + 1) := (symmetricTwoByTwoCoefficient_nonneg_lt_one hα).1
  have hx0 := hx 0; have hx1 := hx 1; have hy0 := hy 0; have hy1 := hy 1
  -- the two image vectors
  have hAx : ∀ z : Fin 2 → ℝ,
      positiveKernelApply (symmetricTwoByTwoKernel α) z 0 = α * z 0 + z 1 :=
    fun z => positiveKernelApply_symmetricTwoByTwo_zero α z
  have hAx' : ∀ z : Fin 2 → ℝ,
      positiveKernelApply (symmetricTwoByTwoKernel α) z 1 = z 0 + α * z 1 :=
    fun z => positiveKernelApply_symmetricTwoByTwo_one α z
  have hAxpos : ∀ z : Fin 2 → ℝ, (∀ i, 0 < z i) →
      ∀ i, 0 < positiveKernelApply (symmetricTwoByTwoKernel α) z i := by
    intro z hz i
    exact positiveKernelApply_pos _ (symmetricTwoByTwoKernel_pos hα) z hz i
  -- the source and image log cross-ratios
  set u : ℝ := Real.log (x 0 / x 1) with hu
  set v : ℝ := Real.log (y 0 / y 1) with hv
  have hexpu : Real.exp u = x 0 / x 1 := Real.exp_log (div_pos hx0 hx1)
  have hexpv : Real.exp v = y 0 / y 1 := Real.exp_log (div_pos hy0 hy1)
  -- `g u = log (α x₀ + x₁) - log (x₀ + α x₁)`
  have hgu : Real.log (α * Real.exp u + 1) - Real.log (Real.exp u + α)
      = Real.log (α * x 0 + x 1) - Real.log (x 0 + α * x 1) := by
    rw [hexpu]
    have e1 : α * (x 0 / x 1) + 1 = (α * x 0 + x 1) / x 1 := by field_simp
    have e2 : x 0 / x 1 + α = (x 0 + α * x 1) / x 1 := by field_simp
    rw [e1, e2, Real.log_div (by positivity) hx1.ne', Real.log_div (by positivity) hx1.ne']
    ring
  have hgv : Real.log (α * Real.exp v + 1) - Real.log (Real.exp v + α)
      = Real.log (α * y 0 + y 1) - Real.log (y 0 + α * y 1) := by
    rw [hexpv]
    have e1 : α * (y 0 / y 1) + 1 = (α * y 0 + y 1) / y 1 := by field_simp
    have e2 : y 0 / y 1 + α = (y 0 + α * y 1) / y 1 := by field_simp
    rw [e1, e2, Real.log_div (by positivity) hy1.ne', Real.log_div (by positivity) hy1.ne']
    ring
  have hlip := symmetricTwoByTwo_log_lipschitz hα u v
  rw [hgu, hgv] at hlip
  -- rewrite both absolute values as log cross-ratios
  have hsrc : u - v = Real.log ((x 0 * y 1) / (x 1 * y 0)) := by
    rw [hu, hv, Real.log_div hx0.ne' hx1.ne', Real.log_div hy0.ne' hy1.ne',
      Real.log_div (mul_pos hx0 hy1).ne' (mul_pos hx1 hy0).ne',
      Real.log_mul hx0.ne' hy1.ne', Real.log_mul hx1.ne' hy0.ne']
    ring
  have himg : (Real.log (α * x 0 + x 1) - Real.log (x 0 + α * x 1))
      - (Real.log (α * y 0 + y 1) - Real.log (y 0 + α * y 1))
      = Real.log (((α * x 0 + x 1) * (y 0 + α * y 1)) / ((x 0 + α * x 1) * (α * y 0 + y 1))) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hsrc, himg] at hlip
  -- assemble: image spread ≤ |image log cross-ratio| ≤ k * |source| ≤ k * source spread
  calc finiteHilbertProjectiveLogSpread
        (positiveKernelApply (symmetricTwoByTwoKernel α) x)
        (positiveKernelApply (symmetricTwoByTwoKernel α) y)
      ≤ |Real.log
          ((positiveKernelApply (symmetricTwoByTwoKernel α) x 0
              * positiveKernelApply (symmetricTwoByTwoKernel α) y 1) /
            (positiveKernelApply (symmetricTwoByTwoKernel α) x 1
              * positiveKernelApply (symmetricTwoByTwoKernel α) y 0))| :=
        spread_fin_two_le _ _ (hAxpos x hx) (hAxpos y hy)
    _ = |Real.log (((α * x 0 + x 1) * (y 0 + α * y 1)) / ((x 0 + α * x 1) * (α * y 0 + y 1)))| := by
        rw [hAx x, hAx' x, hAx y, hAx' y]
    _ ≤ ((α - 1) / (α + 1)) * |Real.log ((x 0 * y 1) / (x 1 * y 0))| := hlip
    _ ≤ ((α - 1) / (α + 1)) * finiteHilbertProjectiveLogSpread x y :=
        mul_le_mul_of_nonneg_left
          (finiteHilbertProjectiveLogSpread_abs_pair_le x y hx hy 0 1) hk0

/-- Strict packaged version of the normalized two-by-two Birkhoff contraction theorem.

This is the Agent-5 interface that later assembly code should consume: the coefficient is not just
the analytic contraction constant, but also comes with the strict range facts needed for geometric
decay. -/
theorem symmetricTwoByTwo_strict_birkhoff_contraction {α : ℝ} (hα : 1 < α) :
    IsStrictBirkhoffHopfContractionCoefficient
      (symmetricTwoByTwoKernel α) ((α - 1) / (α + 1)) := by
  rcases symmetricTwoByTwoCoefficient_nonneg_lt_one hα with ⟨hγ_nonneg, hγ_lt_one⟩
  exact ⟨hγ_nonneg, hγ_lt_one, symmetricTwoByTwo_birkhoff_contraction hα⟩

/-- Paper route Step 6: positive two-by-two matrices reduce to the normalized symmetric case.

Paper analogue: Eveson--Nussbaum Lemma 5.1.  Positive diagonal row/column scalings, possibly
combined with a row swap, transform a positive nonsingular `2 × 2` matrix into
`[[α, 1], [1, α]]` with `α > 1`.  The existential data below records exactly the scaling and
permutation witnesses that later invariance lemmas must consume. -/
theorem twoByTwo_normal_form_of_one_lt_crossRatio
    (A : Fin 2 → Fin 2 → ℝ) (hA : ∀ i j, 0 < A i j)
    (hρ : 1 < (A 0 0 * A 1 1) / (A 0 1 * A 1 0)) :
    ∃ α : ℝ, ∃ rowScale colScale : Fin 2 → ℝ,
      1 < α ∧
        (∀ i, 0 < rowScale i) ∧
        (∀ j, 0 < colScale j) ∧
        (∀ i j : Fin 2, rowScale i * A i j * colScale j = symmetricTwoByTwoKernel α i j) := by
  have h00 := hA 0 0; have h01 := hA 0 1; have h10 := hA 1 0; have h11 := hA 1 1
  set ρ : ℝ := (A 0 0 * A 1 1) / (A 0 1 * A 1 0) with hρdef
  set σ : ℝ := (A 0 1 * A 1 1) / (A 0 0 * A 1 0) with hσdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  set c₀ : ℝ := Real.sqrt σ with hc₀
  have hc₀pos : 0 < c₀ := Real.sqrt_pos.mpr hσpos
  set α : ℝ := Real.sqrt ρ with hαdef
  have hαpos : 0 < α := Real.sqrt_pos.mpr hρpos
  have hα1 : 1 < α := by
    have h := Real.sqrt_lt_sqrt (by norm_num) hρ
    rwa [Real.sqrt_one] at h
  -- `α * c₀ = A 1 1 / A 1 0`, since `ρ * σ = (A 1 1 / A 1 0) ^ 2`
  have hαc₀ : α * c₀ = A 1 1 / A 1 0 := by
    rw [hαdef, hc₀, ← Real.sqrt_mul (le_of_lt hρpos)]
    have hrs : ρ * σ = (A 1 1 / A 1 0) ^ 2 := by
      rw [hρdef, hσdef]; field_simp; try ring
    rw [hrs, Real.sqrt_sq (by positivity)]
  refine ⟨α, ![1 / A 0 1, 1 / (A 1 0 * c₀)], ![c₀, 1], hα1, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · show 0 < 1 / A 0 1; positivity
    · show 0 < 1 / (A 1 0 * c₀); positivity
  · intro j; fin_cases j
    · show 0 < c₀; exact hc₀pos
    · show (0:ℝ) < 1; norm_num
  · intro i j
    fin_cases i <;> fin_cases j <;> simp only [symmetricTwoByTwoKernel]
    · -- (0,0): `(A 0 0 / A 0 1) * c₀ = α`
      show 1 / A 0 1 * A 0 0 * c₀ = (if (0 : Fin 2) = (0 : Fin 2) then α else 1)
      rw [if_pos rfl, hc₀, hαdef]
      have hcoef : A 0 0 / A 0 1 = Real.sqrt ((A 0 0 / A 0 1) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      have hprod : (A 0 0 / A 0 1) ^ 2 * σ = ρ := by
        rw [hρdef, hσdef]; field_simp; try ring
      calc 1 / A 0 1 * A 0 0 * Real.sqrt σ
          = (A 0 0 / A 0 1) * Real.sqrt σ := by ring
        _ = Real.sqrt ((A 0 0 / A 0 1) ^ 2) * Real.sqrt σ := by rw [← hcoef]
        _ = Real.sqrt ((A 0 0 / A 0 1) ^ 2 * σ) := (Real.sqrt_mul (sq_nonneg _) σ).symm
        _ = Real.sqrt ρ := by rw [hprod]
    · show 1 / A 0 1 * A 0 1 * 1 = (if (0 : Fin 2) = (1 : Fin 2) then α else 1)
      rw [if_neg (by decide)]; field_simp
    · show 1 / (A 1 0 * c₀) * A 1 0 * c₀ = (if (1 : Fin 2) = (0 : Fin 2) then α else 1)
      rw [if_neg (by decide)]; field_simp
    · -- (1,1): `A 1 1 / (A 1 0 * c₀) = α`, i.e. `α * (A 1 0 * c₀) = A 1 1`
      show 1 / (A 1 0 * c₀) * A 1 1 * 1 = (if (1 : Fin 2) = (1 : Fin 2) then α else 1)
      rw [if_pos rfl]
      have hne : A 1 0 * c₀ ≠ 0 := by positivity
      field_simp
      calc A 1 1 = A 1 0 * (A 1 1 / A 1 0) := by field_simp
        _ = A 1 0 * (α * c₀) := by rw [hαc₀]
        _ = A 1 0 * c₀ * α := by ring

/-- Paper route Step 6: positive two-by-two matrices reduce to the normalized symmetric case.

Paper analogue: Eveson--Nussbaum Lemma 5.1.  The paper argues via a doubly-stochastic normalization
and the intermediate value theorem; for the statement below that is unnecessary, because explicit
closed-form witnesses exist.  With `ρ = A₀₀A₁₁ / (A₀₁A₁₀)` — and `hdet` says exactly `ρ ≠ 1` — take
`α = √ρ`, `colScale = (√(A₀₁A₁₁ / (A₀₀A₁₀)), 1)` and `rowScale = (1/A₀₁, 1/(A₁₀ · colScale₀))`.
If `ρ < 1`, swapping the rows first sends `ρ ↦ 1/ρ > 1`. -/
theorem positive_twoByTwo_reduces_to_symmetric_normal_form
    (A : Fin 2 → Fin 2 → ℝ) (hA : ∀ i j, 0 < A i j)
    (hdet : A (0 : Fin 2) (0 : Fin 2) * A (1 : Fin 2) (1 : Fin 2) ≠
      A (0 : Fin 2) (1 : Fin 2) * A (1 : Fin 2) (0 : Fin 2)) :
    ∃ α : ℝ, ∃ rowScale colScale : Fin 2 → ℝ, ∃ rowPerm : Fin 2 ≃ Fin 2,
      1 < α ∧
        (∀ i, 0 < rowScale i) ∧
        (∀ j, 0 < colScale j) ∧
        (∀ i j : Fin 2,
          rowScale i * A (rowPerm i) j * colScale j = symmetricTwoByTwoKernel α i j) := by
  have h00 := hA 0 0; have h01 := hA 0 1; have h10 := hA 1 0; have h11 := hA 1 1
  have hden : (0:ℝ) < A 0 1 * A 1 0 := mul_pos h01 h10
  have hρne : (A 0 0 * A 1 1) / (A 0 1 * A 1 0) ≠ 1 := by
    intro h
    apply hdet
    field_simp at h
    exact h
  rcases lt_or_gt_of_ne hρne with hlt | hgt
  · -- `ρ < 1`: swap the rows, which sends `ρ ↦ 1/ρ > 1`
    set B : Fin 2 → Fin 2 → ℝ := fun i j => A (Equiv.swap (0 : Fin 2) 1 i) j with hB
    have hBpos : ∀ i j, 0 < B i j := fun i j => hA _ _
    have hB00 : B 0 0 = A 1 0 := by rw [hB]; simp
    have hB01 : B 0 1 = A 1 1 := by rw [hB]; simp
    have hB10 : B 1 0 = A 0 0 := by rw [hB]; simp
    have hB11 : B 1 1 = A 0 1 := by rw [hB]; simp
    have hBρ : 1 < (B 0 0 * B 1 1) / (B 0 1 * B 1 0) := by
      rw [hB00, hB01, hB10, hB11]
      rw [lt_div_iff₀ (by positivity)]
      have hρlt : A 0 0 * A 1 1 < A 0 1 * A 1 0 := by
        rw [div_lt_one hden] at hlt; exact hlt
      nlinarith [hρlt]
    obtain ⟨α, rowScale, colScale, hα, hr, hc, heq⟩ :=
      twoByTwo_normal_form_of_one_lt_crossRatio B hBpos hBρ
    exact ⟨α, rowScale, colScale, Equiv.swap (0 : Fin 2) 1, hα, hr, hc, heq⟩
  · obtain ⟨α, rowScale, colScale, hα, hr, hc, heq⟩ :=
      twoByTwo_normal_form_of_one_lt_crossRatio A hA hgt
    exact ⟨α, rowScale, colScale, Equiv.refl (Fin 2), hα, hr, hc, by simpa using heq⟩

end BirkhoffHopf.PaperRoute
end ForMathlib.Matrix
