/-
TwoPagerPACBayes.lean

Lean4 formalization of Theorem 4 in TwoPager.pdf (PAC-Bayes bound for the clipped
terminal-cost network g_θ).

Source statement (TwoPager, Eq. (116)/(126)):
  E_{X1~P1}[gθ(X1)] ≤ (1/n)∑ gθ(X1ᵢ) + (KL(P‖Q)+log(1/δ))/ε + ε C^2/(2n)
with probability ≥ 1-δ over an i.i.d. sample from P1.

We mirror the proof’s final structure:
  (A) an exponential-moment inequality (PAC-Bayes+Hoeffding+DV packaged),
  (B) exponential Markov (Chernoff) tail bound,
  (C) algebraic rearrangement and set-inclusion → probability lower bound.
-/

import Mathlib
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.InformationTheory.KullbackLeibler.Basic

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace TwoPagerPACBayes

variable {X : Type*} [MeasurableSpace X]

/-- Empirical mean of `g` over a sample `s : Fin n → X`. -/
noncomputable def empMean (n : ℕ) (g : X → ℝ) (s : Fin n → X) : ℝ :=
  (1 / (n : ℝ)) * (∑ i : Fin n, g (s i))

/-- Population mean of `g` under measure `μ`. -/
noncomputable def popMean (μ : Measure X) (g : X → ℝ) : ℝ :=
  ∫ x, g x ∂ μ

/-- i.i.d. sample measure: product measure on `Fin n → X` with all marginals `μ`. -/
noncomputable def iidsampleMeasure (μ : Measure X) (n : ℕ) : Measure (Fin n → X) :=
  Measure.pi (fun _ : Fin n => μ)

noncomputable instance iidsampleMeasure.instIsProbabilityMeasure
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (iidsampleMeasure μ n) := by
  classical
  refine ⟨by
    -- `simp` knows `Measure.pi` mass of `univ` is the (finite) product of masses of `univ`
    -- and each factor is `1` because `[IsProbabilityMeasure μ]`.
    simp [iidsampleMeasure]⟩

/-
The heavy analytic steps in the TwoPager proof.

(1) `pacBayes_exp_moment` is the “rearranged” exponential-moment inequality
    (the content of TwoPager Eq. (122) specialized to a fixed posterior P, i.e.
    without the outer `sup_P`).
    Intuitively:  E_S[ exp( ε(R-r(S)) - KL(P‖Q) - ε^2 C^2/(2n) ) ] ≤ 1.

(2) `exp_tail_of_moment_le_one` is exponential Markov/Chernoff:
    If E[exp(Z)] ≤ 1 then Pr(Z ≥ log(1/δ)) ≤ δ.

(3) `compl_ge_of_le` is the “turn tail bound into success probability” lemma.
-/

/-- PAC-Bayes exponential-moment inequality (TwoPager Eq. (122) specialized). -/
theorem pacBayes_exp_moment
  (μ : Measure X) [IsProbabilityMeasure μ]
  (g : X → ℝ) (C ε klPQ : ℝ) (n : ℕ)
  (hn : 0 < n) (hC : 0 ≤ C) (hε : 0 < ε)
  (hg_meas : Measurable g) (hg_bd : ∀ x, |g x| ≤ C) :
  (∫ s,
      Real.exp
        ( ε * (popMean μ g - empMean n g s)
          - klPQ
          - (ε^2 * C^2) / (2 * (n : ℝ)) )
    ∂ (iidsampleMeasure μ n)) ≤ 1 :=
    sorry

/-- Exponential Markov/Chernoff: from `E[exp(Z)] ≤ 1` get a tail probability. -/
theorem exp_tail_of_moment_le_one
  {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
  (Z : α → ℝ) (δ : ℝ) :
  0 < δ →
  (∫ a, Real.exp (Z a) ∂ μ) ≤ 1 →
  μ {a | Z a ≥ Real.log (1 / δ)} ≤ ENNReal.ofReal δ:=
  sorry

/-- If `μ(A) ≤ δ` and `μ` is a probability measure, then `μ(Aᶜ) ≥ 1-δ`. -/
theorem compl_ge_of_le
  {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
  (A : Set α) (δ : ℝ) :
  μ A ≤ ENNReal.ofReal δ →
  δ ≤ 1 →
  μ Aᶜ ≥ ENNReal.ofReal (1 - δ) :=
  sorry

/-
Main theorem: the exact inequality as written in the TwoPager (Eq. (116)/(126)).
-/
theorem pacBayes_generalization_bound
  (μ : Measure X) [IsProbabilityMeasure μ]
  (g : X → ℝ) (C ε δ klPQ : ℝ) (n : ℕ)
  (hn : 0 < n) (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 < δ ∧ δ < 1)
  (hg_meas : Measurable g) (hg_bd : ∀ x, |g x| ≤ C) :
  let μn := iidsampleMeasure μ n
  let R  := popMean μ g
  let r  := empMean n g
  let quad : ℝ := ε * C^2 / (2 * (n : ℝ))
  μn {s | R ≤ r s + (klPQ + Real.log (1 / δ)) / ε + quad}
    ≥ ENNReal.ofReal (1 - δ) := by
  classical
  intro μn R r quad

  -- Define the “PAC-Bayes exponent” Z(s) used for the tail bound.
  let Z : (Fin n → X) → ℝ :=
    fun s =>
      ε * (R - r s) - klPQ - (ε^2 * C^2) / (2 * (n : ℝ))

  -- Step (A): exponential-moment bound (≤ 1).
  have hMoment : (∫ s, Real.exp (Z s) ∂ μn) ≤ 1 := by
    -- unfold Z and rewrite to match the dependency
    -- note: R = popMean μ g, r = empMean n g, μn = iidsampleMeasure μ n
    simpa [μn, R, r, Z, iidsampleMeasure, popMean, empMean, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_add, mul_sub]
      using (pacBayes_exp_moment (X:=X) μ g C ε klPQ n hn hC hε hg_meas hg_bd)

  -- Step (B): Chernoff tail bound: bad-set prob ≤ δ.
  let bad : Set (Fin n → X) := {s | Z s ≥ Real.log (1 / δ)}
  have hBad : μn bad ≤ ENNReal.ofReal δ := by
    -- If typeclass search fails to find `IsProbabilityMeasure μn`, uncomment:
    -- haveI : IsProbabilityMeasure μn := by
    --   -- μn is definitional equal to `iidsampleMeasure μ n`
    --   -- and `iidsampleMeasure` is `Measure.pi` of prob measures
    --   simpa [μn, iidsampleMeasure] using
    --     (by
    --       infer_instance :
    --         IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
    simpa [bad] using
      (exp_tail_of_moment_le_one (μ := μn) (Z := Z) (δ := δ) hδ.1 hMoment)

  -- Step (C): convert to a good-set probability lower bound.
  have hGood : μn badᶜ ≥ ENNReal.ofReal (1 - δ) := by
    exact compl_ge_of_le (μ := μn) (A := bad) (δ := δ) hBad (le_of_lt hδ.2)


  -- Show: good-set ⊆ desired event-set, then use monotonicity of measure.
  have hSubset :
      badᶜ ⊆ {s | R ≤ r s + (klPQ + Real.log (1 / δ)) / ε + quad} := by
    intro s hs
    have hs_bad : ¬ (Z s ≥ Real.log (1 / δ)) := by
      simpa [bad] using hs
    have hsZ : Z s < Real.log (1 / δ) := lt_of_not_ge hs_bad

    -- Rearrange:
    --   ε*(R - r s) - klPQ - (ε^2 C^2)/(2n) < log(1/δ)
    -- → ε*(R - r s) < klPQ + (ε^2 C^2)/(2n) + log(1/δ)
    have h1 :
        ε * (R - r s)
          < klPQ + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / δ) := by
      dsimp [Z] at hsZ
      linarith

    -- Divide by ε > 0:
    --   R - r s < (klPQ + log(1/δ))/ε + (ε^2 C^2)/(2n)/ε
    -- and note ((ε^2 C^2)/(2n))/ε = ε*C^2/(2n) = quad.
    have h2 :
        (R - r s)
          < (klPQ + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / δ)) / ε := by
      -- use `le_div_iff`/`lt_div_iff` style lemma
      -- (a < b/ε) ↔ (a*ε < b) for ε>0
      have : (R - r s) * ε
              < klPQ + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / δ) := by
        -- (R - r s) * ε = ε * (R - r s)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h1
      exact (lt_div_iff₀ hε).mpr this

    have h2' :
        R ≤ r s
            + (klPQ + Real.log (1 / δ)) / ε
            + (ε^2 * C^2) / (2 * (n : ℝ)) / ε := by
      have : R - r s ≤ (klPQ + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / δ)) / ε :=
        le_of_lt h2
      -- split (a+b+c)/ε = a/ε + b/ε + c/ε and then add r s
      -- We keep it simple with `linarith` after rewriting by `add_div`.
      -- First rewrite RHS:
      have :
          (klPQ + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / δ)) / ε
            = (klPQ + Real.log (1 / δ)) / ε + ((ε^2 * C^2) / (2 * (n : ℝ))) / ε := by
        ring_nf
      -- now finish
      linarith

    -- Replace ((ε^2*C^2)/(2n))/ε with quad = ε*C^2/(2n).
    have hQuad :
        (ε^2 * C^2) / (2 * (n : ℝ)) / ε = quad := by
      -- quad was defined as ε*C^2/(2n)
      dsimp [quad]
      -- (ε^2*C^2)/(2n)/ε = (ε*C^2)/(2n)
      field_simp [hε.ne']

    simpa [hQuad] using h2'

  -- Measure monotonicity: μ(badᶜ) ≤ μ(event)
  have hMono : μn badᶜ ≤ μn {s | R ≤ r s + (klPQ + Real.log (1 / δ)) / ε + quad} :=
    measure_mono hSubset

  -- Combine lower bound on μ(badᶜ) with monotonicity.
  exact le_trans hGood hMono

end TwoPagerPACBayes
