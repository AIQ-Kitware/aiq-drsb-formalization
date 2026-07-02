/-
DKPS_Quench_ICML_2026/drsb-v3.lean

A "TwoPager"-style generalization bound (Hoeffding/Chernoff + KL term) specialized
for bounded functions `g : X → ℝ`.

This file is intended as *scaffolding* that matches the paper/TwoPager theorem:

  E[g] ≤ (1/n)∑ g(Xᵢ) + (KL(P‖Q)+log(1/δ))/ε + ε*C^2/(2n)

with probability ≥ 1-δ over i.i.d. samples from the terminal marginal.

Key fixes vs prior versions:
- Independence proof uses `ProbabilityTheory.iIndepFun_infinitePi` (not `iIndepFun_pi`),
  so it matches `Measure.infinitePi` exactly.
- `HasSubgaussianMGF.sum_of_iIndepFun` is called positionally (no fragile named args).
- `probReal_compl_eq_one_sub` is invoked with an explicit measurability witness.
- Everything is inside explicit namespaces / variables, compatible with `autoImplicit=false`.
-/

import Mathlib
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Real

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Topology

set_option autoImplicit false

-- mathlib linter currently trips on some simp-arg warnings in this scaffold; disable for now.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace TwoPagerPACBayes

variable {X : Type*} [MeasurableSpace X]

/-- Empirical mean of `g` over a sample `s : Fin n → X`. -/
noncomputable def empMean (n : ℕ) (g : X → ℝ) (s : Fin n → X) : ℝ :=
  (1 / (n : ℝ)) * (∑ i : Fin n, g (s i))

/-- Population mean of `g` under measure `μ`. -/
noncomputable def popMean (μ : Measure X) (g : X → ℝ) : ℝ :=
  ∫ x, g x ∂ μ

/-- i.i.d. sample measure on `Fin n → X`. -/
noncomputable def sampleMeasure (μ : Measure X) (n : ℕ) : Measure (Fin n → X) :=
  Measure.infinitePi (fun _ : Fin n => μ)

noncomputable instance sampleMeasure.instIsProbabilityMeasure
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (sampleMeasure (X := X) μ n) := by
  classical
  refine ⟨by simp [sampleMeasure]⟩

/--
Core TwoPager Hoeffding/Chernoff bound:

For bounded `g ∈ [-C, C]`, with `S ~ μ^n`,
`Pr( popMean μ g - empMean g S ≥ log(1/δ)/ε + ε*C^2/(2n) ) ≤ δ`.
-/
theorem hoeffding_twopager
    (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (g : X → ℝ) (hg : Measurable g)
    (C : NNReal) (hC : ∀ x, g x ∈ Set.Icc (-(C : ℝ)) (C : ℝ))
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    let μS : Measure (Fin n → X) := sampleMeasure (X := X) μ n
    let R : ℝ := popMean μ g
    let diff : (Fin n → X) → ℝ := fun s => R - empMean (X := X) n g s
    μS.real {s | (Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)) ≤ diff s} ≤ δ := by
  classical
  intro μS R diff

  have hC_ae : (∀ᵐ x ∂μ, g x ∈ Set.Icc (-(C : ℝ)) (C : ℝ)) := by
    exact ae_of_all μ hC
  have hg_ae : AEMeasurable g μ := hg.aemeasurable

  -- Centered subgaussian on base space.
  have hsg_center :
      HasSubgaussianMGF
        (fun x => g x - (∫ y, g y ∂μ))
        (((‖((C : ℝ) - (-(C : ℝ)))‖₊) / 2) ^ 2)
        μ :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := μ) (X := g) (a := (-(C : ℝ))) (b := (C : ℝ))
      hg_ae hC_ae

  -- Negation preserves the same subgaussian parameter via const_mul (-1).
  have hsg_base :
      HasSubgaussianMGF
        (fun x => (∫ y, g y ∂μ) - g x)
        (((‖((C : ℝ) - (-(C : ℝ)))‖₊) / 2) ^ 2)
        μ := by
    -- (∫g - g x) = - (g x - ∫g)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_sub] using
      (hsg_center.const_mul (r := (-1 : ℝ)))

  -- Coordinate marginal is μ.
  have hmap_eval (i : Fin n) :
      Measure.map (fun s : Fin n → X => s i) μS = μ := by
    -- Avoid relying on argument names (`μ` vs `P`) which have changed across mathlib versions.
    simpa [sampleMeasure] using
      (Measure.infinitePi_map_eval (fun _ : Fin n => μ) i)

  -- Lift subgaussianity to each coordinate in the product space.
  have hsg_coord (i : Fin n) :
      HasSubgaussianMGF
        (fun s : Fin n → X => R - g (s i))
        (((‖((C : ℝ) - (-(C : ℝ)))‖₊) / 2) ^ 2)
        μS := by
    have hsg_on_map :
        HasSubgaussianMGF
          (fun x : X => R - g x)
          (((‖((C : ℝ) - (-(C : ℝ)))‖₊) / 2) ^ 2)
          (Measure.map (fun s : Fin n → X => s i) μS) := by
      have : (Measure.map (fun s : Fin n → X => s i) μS) = μ := hmap_eval i
      simpa [R, popMean, this] using hsg_base

    have hY : AEMeasurable (fun s : Fin n → X => s i) μS :=
      (measurable_pi_apply i).aemeasurable

    simpa using
      (HasSubgaussianMGF.of_map (μ := μS) (Y := fun s : Fin n → X => s i) hY hsg_on_map)

  -- Independence of coordinates in the infinitePi product.
  have hindep :
      iIndepFun (fun i : Fin n => fun s : Fin n → X => (R - g (s i))) μS := by
    have hmeas : ∀ _i : Fin n, Measurable (fun x : X => R - g x) := by
      intro _i
      exact measurable_const.sub hg
    -- `iIndepFun_infinitePi` matches `Measure.infinitePi` exactly.
    simpa [μS, sampleMeasure] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : Fin n => μ)
        (X := fun _i : Fin n => fun x : X => R - g x)
        hmeas)

  -- Sum is subgaussian with parameter sum of parameters.
  let c0 : NNReal := (((‖((C : ℝ) - (-(C : ℝ)))‖₊) / 2) ^ 2)

  have hsg_sum :
      HasSubgaussianMGF
        (fun s : Fin n → X => ∑ i : Fin n, (R - g (s i)))
        (∑ _i : Fin n, c0)
        μS := by
    have hsg_family : ∀ i : Fin n, HasSubgaussianMGF (fun s => R - g (s i)) c0 μS := by
      intro i
      simpa [c0] using hsg_coord i
    -- Use the finset lemma, avoid named args that vary across versions.
    have h :=
      (ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun (μ := μS) hindep
        (c := fun _ : Fin n => c0)
        (s := (Finset.univ : Finset (Fin n)))
        (h_subG := by
          intro i hi
          simpa using hsg_family i))
    -- Rewrite the `∑ i ∈ univ` form into the binder form `∑ i`.
    simpa using h

  -- Averaged deviation and identify with diff.
  let avg : (Fin n → X) → ℝ :=
    fun s => (1 / (n : ℝ)) * (∑ i : Fin n, (R - g (s i)))

  have hsg_avg :
      HasSubgaussianMGF avg
        ((Real.nnabs (1 / (n : ℝ))) ^ 2 * (∑ _i : Fin n, c0))
        μS := by
    simpa [avg] using (hsg_sum.const_mul (r := (1 / (n : ℝ))))

  have havg_eq_diff : avg = diff := by
    funext s
    have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    calc
      avg s
          = (1 / (n : ℝ)) * (∑ i : Fin n, (R - g (s i))) := by rfl
      _   = (1 / (n : ℝ)) * ((∑ i : Fin n, R) - (∑ i : Fin n, g (s i))) := by
              simp [Finset.sum_sub_distrib]
      _   = (1 / (n : ℝ)) * ((n : ℝ) * R - (∑ i : Fin n, g (s i))) := by
              simp [Finset.sum_const, Finset.card_univ, mul_assoc]
      _   = R - (1 / (n : ℝ)) * (∑ i : Fin n, g (s i)) := by
              -- `field_simp` closes this goal in this development version.
              field_simp [hnne]
      _   = diff s := by
              simp [diff, empMean, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]

  have hsg_diff :
      HasSubgaussianMGF diff
        ((Real.nnabs (1 / (n : ℝ))) ^ 2 * (∑ _i : Fin n, c0))
        μS := by
    simpa [havg_eq_diff] using hsg_avg

  -- Chernoff bound with cgf.
  have hchernoff :
      μS.real
        {s | (Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)) ≤ diff s}
        ≤ Real.exp (-(ε) * ((Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)))
                    + cgf diff μS ε) := by
    have hint : Integrable (fun s => Real.exp (ε * diff s)) μS :=
      (hsg_diff.integrable_exp_mul ε)
    -- note: lemma requires `0 ≤ ε`.
    simpa [mul_assoc] using
      (ProbabilityTheory.measure_ge_le_exp_cgf (μ := μS) (X := diff) (t := ε)
        (ε := (Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)))
        (le_of_lt hε) hint)

  have hcgf_le :
      cgf diff μS ε ≤
        (( (Real.nnabs (1 / (n : ℝ))) ^ 2 * (∑ _i : Fin n, c0) : NNReal) : ℝ) * ε^2 / 2 := by
    simpa using (hsg_diff.cgf_le ε)

  -- Finish: exp( -ε*thr + cgf ) ≤ δ.
  have hfinal_exp :
      Real.exp (-(ε) * ((Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)))
                + cgf diff μS ε)
      ≤ δ := by
    have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hε

    have hc0_real : (c0 : ℝ) = (C : ℝ)^2 := by
      -- c0 = (‖(C - -C)‖₊/2)^2 = C^2
      have hnonneg : 0 ≤ (C : ℝ) + (C : ℝ) := by positivity
      -- Reduce to the real-algebraic identity `((C+C)/2)^2 = C^2`.
      calc
        (c0 : ℝ)
            = (((|(C : ℝ) - (-(C : ℝ))|) / 2) ^ 2) := by
                simp [c0, Real.coe_nnabs]
        _   = (((|(C : ℝ) + (C : ℝ)|) / 2) ^ 2) := by
                simp [sub_eq_add_neg]
        _   = ((((C : ℝ) + (C : ℝ)) / 2) ^ 2) := by
                simp [abs_of_nonneg hnonneg]
        _   = (C : ℝ)^2 := by
                -- `nlinarith` handles the polynomial identity over `ℝ`.
                nlinarith

    have hsum_c0 :
        ((∑ _i : Fin n, c0 : NNReal) : ℝ) = (n : ℝ) * (c0 : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, Nat.cast_id]

    have hparam :
        (( (Real.nnabs (1 / (n : ℝ))) ^ 2 * (∑ _i : Fin n, c0) : NNReal) : ℝ)
          = (C : ℝ)^2 / (n : ℝ) := by
      have habs : ((Real.nnabs (1 / (n : ℝ)) : NNReal) : ℝ) = (1 / (n : ℝ)) := by
        have : 0 < (1 / (n : ℝ)) := by positivity
        simpa [Real.coe_nnabs, abs_of_pos this]
      calc
        (( (Real.nnabs (1 / (n : ℝ))) ^ 2 * (∑ _i : Fin n, c0) : NNReal) : ℝ)
            = ((Real.nnabs (1 / (n : ℝ)) : NNReal) : ℝ)^2 * ((∑ _i : Fin n, c0 : NNReal) : ℝ) := by
                simp [pow_two, mul_assoc]
        _   = (1 / (n : ℝ))^2 * ((n : ℝ) * (c0 : ℝ)) := by
                simp [habs, hsum_c0, pow_two, mul_assoc]
        _   = (c0 : ℝ) / (n : ℝ) := by
                  -- Expand squares and cancel one factor of `n`.
                  have hnne' : (n : ℝ) ≠ 0 := hnne
                  calc
                    (1 / (n : ℝ)) ^ 2 * ((n : ℝ) * (c0 : ℝ))
                        = (1 / (n : ℝ)) * ((1 / (n : ℝ)) * ((n : ℝ) * (c0 : ℝ))) := by
                            simp [pow_two, mul_assoc]
                    _   = (1 / (n : ℝ)) * (((1 / (n : ℝ)) * (n : ℝ)) * (c0 : ℝ)) := by
                            -- reassociate and commute to expose `(1/n)*n`.
                            simp [mul_assoc, mul_left_comm, mul_comm]
                    _   = (1 / (n : ℝ)) * (1 * (c0 : ℝ)) := by
                            simp [one_div, hnne', mul_assoc]
                      _   = (c0 : ℝ) / (n : ℝ) := by
                              -- Clear denominators (this is the goal reported in the latest log).
                              -- pure rewriting avoids `field_simp`/`ring` goal-management issues.
                              simp [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm]
        _   = (C : ℝ)^2 / (n : ℝ) := by
                simp [hc0_real]

    have hcgf_le' :
        cgf diff μS ε ≤ ε^2 * (C : ℝ)^2 / (2 * (n : ℝ)) := by
      have hA :
          cgf diff μS ε ≤
            (( (Real.nnabs (1 / (n : ℝ))) ^ 2 * (∑ _i : Fin n, c0) : NNReal) : ℝ) * ε^2 / 2 :=
        hcgf_le
      have hparam' :
          (( (Real.nnabs (1 / (n : ℝ))) ^ 2 * (∑ _i : Fin n, c0) : NNReal) : ℝ)
            = (C : ℝ)^2 / (n : ℝ) := by
        -- `hparam` is stated using the same coercion; rewrite directly.
        simpa using hparam
      calc
        cgf diff μS ε
            ≤ (( (Real.nnabs (1 / (n : ℝ))) ^ 2 * (∑ _i : Fin n, c0) : NNReal) : ℝ) * ε^2 / 2 := hA
        _   = ((C : ℝ)^2 / (n : ℝ)) * ε^2 / 2 := by
              rw [hparam']
        _   = ε^2 * (C : ℝ)^2 / (2 * (n : ℝ)) := by
              ring_nf

    have hexp_le :
        (-(ε) * ((Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)))
            + cgf diff μS ε)
          ≤ -Real.log (1 / δ) := by
      have h1 :
          (-(ε) * ((Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)))
              + cgf diff μS ε)
            ≤ (-(ε) * ((Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)))
              + ε^2 * (C : ℝ)^2 / (2 * (n : ℝ))) := by
        linarith [hcgf_le']
      have h2 :
          (-(ε) * ((Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)))
              + ε^2 * (C : ℝ)^2 / (2 * (n : ℝ)))
            = -Real.log (1 / δ) := by
        field_simp [hεne, hnne] <;> ring_nf
      linarith [h1, h2]

    have hexp_id : Real.exp (-(Real.log (1 / δ))) = δ := by
      -- `exp(-x) = (exp x)⁻¹` and `exp(log x) = x`.
      have hpos : 0 < (1 / δ) := by positivity
      have hExpLog : Real.exp (Real.log (1 / δ)) = (1 / δ) := Real.exp_log hpos
      calc
        Real.exp (-(Real.log (1 / δ)))
            = (Real.exp (Real.log (1 / δ)))⁻¹ := by
                simpa using (Real.exp_neg (Real.log (1 / δ)))
        _ = (1 / δ)⁻¹ := by
                rw [hExpLog]
        _ = δ := by
              simp [one_div, one_mul]

    have hExp :
        Real.exp (-(ε) * ((Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)))
                  + cgf diff μS ε)
          ≤ Real.exp (-(Real.log (1 / δ))) :=
      (Real.exp_le_exp).2 hexp_le

    -- rename for clarity (optional)
    have hcgf_bound := hExp

    -- rearrange the exponent using the cgf bound
    -- Freeze the complicated A so we don't make ring/linarith fight division
    set A : ℝ := (-Real.log δ / ε + ε * ↑C ^ 2 / (2 * ↑n)) with hA

    have hcgf_bound' : cgf diff μS ε ≤ ε * A + Real.log δ := by
      simpa [hA] using hcgf_bound

    have hexp_le2 :
        (-(ε * A) + cgf diff μS ε) ≤ Real.log δ := by
      -- add -(ε*A) to both sides
      have h := add_le_add_left hcgf_bound' (-(ε * A))
      -- h : -(ε*A) + cgf ≤ -(ε*A) + (ε*A + log δ)
      have hsimp : (-(ε * A) + (ε * A + Real.log δ)) = Real.log δ := by
        ring  -- polynomial in ε, A, log δ (A is a variable now)
      have h' : cgf diff μS ε ≤ ε * A + Real.log δ := by
        simpa [add_comm, add_left_comm, add_assoc] using h
      have hcgf_bound' : cgf diff μS ε ≤ Real.log δ + ε * A := by
        simpa [hA, add_comm, add_left_comm, add_assoc] using hcgf_bound
      -- hcgf_bound' : cgf diff μS ε ≤ Real.log δ + ε * A
      have hcancel : (-(ε * A) + (Real.log δ + ε * A)) = Real.log δ := by ring
      have hexp_le' : -(ε * A) + cgf diff μS ε ≤ Real.log δ := by
        have h1 := add_le_add_left hcgf_bound' (-(ε * A))
        -- h1 : -(ε*A) + cgf ≤ -(ε*A) + (Real.log δ + ε*A)
        have hcancel : (-(ε * A) + (Real.log δ + ε * A)) = Real.log δ := by
          abel
        have h1' : cgf diff μS ε ≤ ε * A + Real.log δ := by
          simpa [add_comm, add_left_comm, add_assoc] using h1
        simpa [hcancel] using h1'
      simpa [add_comm, add_left_comm, add_assoc] using hcgf_bound'

    -- apply exp monotonicity
    have hExp' :
        Real.exp (-(ε * (-Real.log δ / ε + ε * ↑C ^ 2 / (2 * ↑n))) + cgf diff μS ε)
          ≤ Real.exp (Real.log δ) :=
      (Real.exp_le_exp).2 hexp_le2

    -- exp(log δ) = δ needs strict positivity in mathlib 4.28
    simpa [Real.exp_log hδ] using hExp'
  exact le_trans hchernoff hfinal_exp

/--
TwoPager-style bound with an extra nonnegative `k` term (intended as `k = KL(P‖Q)`).

Monotonicity step: increasing the threshold shrinks the bad event.
-/
theorem twopager_with_extra_term
    (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (g : X → ℝ) (hg : Measurable g)
    (C : NNReal) (hC : ∀ x, g x ∈ Set.Icc (-(C : ℝ)) (C : ℝ))
    {δ ε k : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hk : 0 ≤ k) :
    let μS : Measure (Fin n → X) := sampleMeasure (X := X) μ n
    let R : ℝ := popMean μ g
    let diff : (Fin n → X) → ℝ := fun s => R - empMean (X := X) n g s
    μS.real {s |
      (Real.log (1 / δ) + k) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)) ≤ diff s} ≤ δ := by
  intro μS R diff
  have hsubset :
      {s | (Real.log (1 / δ) + k) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)) ≤ diff s}
        ⊆
      {s | (Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)) ≤ diff s} := by
    intro s hs
    have hdiv :
        (Real.log (1 / δ)) / ε ≤ (Real.log (1 / δ) + k) / ε := by
      have : Real.log (1 / δ) ≤ Real.log (1 / δ) + k := by linarith
      exact div_le_div_of_nonneg_right this (le_of_lt hε)
    have :
        (Real.log (1 / δ)) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ))
          ≤ (Real.log (1 / δ) + k) / ε + ε * (C : ℝ)^2 / (2 * (n : ℝ)) := by
      linarith
    exact le_trans this hs

  have hcore :=
    hoeffding_twopager (X := X) (μ := μ) (n := n) (hn := hn) (g := g) (hg := hg)
      (C := C) (hC := hC) (δ := δ) (ε := ε) hδ hδ1 hε

  exact le_trans (MeasureTheory.measureReal_mono hsubset) hcore

/--
Main theorem (TwoPager Eq. (116)/(126) shape), proved from the TwoPager Hoeffding/Chernoff bound
plus the “extra term” monotonicity, and a complement/probability step.
-/
theorem pacBayes_generalization_bound
  (μ : Measure X) [IsProbabilityMeasure μ]
  (g : X → ℝ) (C ε δ klPQ : ℝ) (n : ℕ)
  (hn : 0 < n) (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 < δ ∧ δ < 1)
  (hk : 0 ≤ klPQ)
  (hg_meas : Measurable g) (hg_bd : ∀ x, |g x| ≤ C) :
  let μn := sampleMeasure (X := X) μ n
  let R  := popMean μ g
  let r  := empMean (X := X) n g
  let quad : ℝ := ε * C^2 / (2 * (n : ℝ))
  μn {s | R ≤ r s + (klPQ + Real.log (1 / δ)) / ε + quad}
    ≥ ENNReal.ofReal (1 - δ) := by
  classical
  intro μn R r quad

  let Cnn : NNReal := ⟨C, hC⟩

  have hCmem : ∀ x, g x ∈ Set.Icc (-(Cnn : ℝ)) (Cnn : ℝ) := by
    intro x
    have hx : -C ≤ g x ∧ g x ≤ C := abs_le.mp (hg_bd x)
    refine ⟨?_, ?_⟩
    · simpa [Cnn] using hx.1
    · simpa [Cnn] using hx.2

  let thr : ℝ := (Real.log (1 / δ) + klPQ) / ε + quad
  let bad : Set (Fin n → X) := {s | thr ≤ (R - r s)}
  let goodEvent : Set (Fin n → X) := {s | R ≤ r s + thr}

  have hBad : μn.real bad ≤ δ := by
    have : μn.real {s |
        (Real.log (1 / δ) + klPQ) / ε + ε * (Cnn : ℝ)^2 / (2 * (n : ℝ)) ≤ (R - empMean (X := X) n g s)} ≤ δ := by
      simpa [μn, R, Cnn, pow_two, thr, bad, r, quad, empMean, popMean] using
        (twopager_with_extra_term (X := X) (μ := μ) (n := n) (hn := hn)
          (g := g) (hg := hg_meas) (C := Cnn) (hC := hCmem)
          (δ := δ) (ε := ε) (k := klPQ) hδ.1 hδ.2 hε hk)
    simpa [bad, thr, r] using this

  -- Measurability of the bad event (needed for probReal_compl_eq_one_sub).
  have hbad_meas : MeasurableSet bad := by
    -- This should follow from measurability of `r` and algebraic closure under +,*,∑.
    -- We leave it as scaffolding for Aristotle to fill in if needed.
    unfold bad
    apply?
    sorry

  have hcompl : μn.real badᶜ = 1 - μn.real bad := by
    simpa [bad] using (MeasureTheory.probReal_compl_eq_one_sub (μ := μn) (s := bad) hbad_meas)

  have hGoodReal : (1 - δ) ≤ μn.real badᶜ := by
    have : (1 - δ) ≤ (1 - μn.real bad) := by linarith [hBad]
    simpa [hcompl] using this

  have hSubset : badᶜ ⊆ goodEvent := by
    intro s hs
    have hs' : ¬ (thr ≤ (R - r s)) := by
      simpa [bad] using hs
    have : (R - r s) < thr := lt_of_not_ge hs'
    have : R < r s + thr := by linarith
    exact le_of_lt this

  have hGoodEventReal : (1 - δ) ≤ μn.real goodEvent := by
    have hmono : μn.real badᶜ ≤ μn.real goodEvent := MeasureTheory.measureReal_mono hSubset
    exact le_trans hGoodReal hmono

  have hμn_good : ENNReal.ofReal (μn.real goodEvent) = μn goodEvent := by
    simpa using (MeasureTheory.ofReal_measureReal (μ := μn) (s := goodEvent))

  have hGoodENN : ENNReal.ofReal (1 - δ) ≤ μn goodEvent := by
    have : ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal (μn.real goodEvent) :=
      ENNReal.ofReal_le_ofReal hGoodEventReal
    simpa [hμn_good] using this

  have hGE :
      goodEvent ⊆ {s | R ≤ r s + (klPQ + Real.log (1 / δ)) / ε + quad} := by
    intro s hs
    have : R ≤ r s + thr := by simpa [goodEvent] using hs
    simpa [thr, add_comm, add_left_comm, add_assoc] using this

  have hmonoENN : μn goodEvent ≤ μn {s | R ≤ r s + (klPQ + Real.log (1 / δ)) / ε + quad} :=
    measure_mono hGE

  exact le_trans hGoodENN hmonoENN

/-- Theorem 4, in the same form as the TwoPager statement. -/
theorem theorem4_twopager
    (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (g : X → ℝ) (hg_meas : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hg_bd : ∀ x, |g x| ≤ C)
    {δ ε klPQ : ℝ} (hδ : 0 < δ ∧ δ < 1) (hε : 0 < ε) (hk : 0 ≤ klPQ) :
    let μn : Measure (Fin n → X) := sampleMeasure (X := X) μ n
    μn {s | popMean μ g ≤ empMean (X := X) n g s
            + (Real.log (1 / δ) + klPQ) / ε
            + ε * C^2 / (2 * (n : ℝ)) }
      ≥ ENNReal.ofReal (1 - δ) := by
  intro μn
  -- `pacBayes_generalization_bound` uses the algebraically equivalent ordering
  -- `(klPQ + log(1/δ)) / ε`; this theorem states `(log(1/δ) + klPQ) / ε`.
  -- In newer mathlib, `simp` may also rewrite `log(1/δ)` into `-log δ` using `hδ.1`.
  -- We therefore include commutativity/associativity lemmas in the `simpa`.
  simpa [μn, pow_two, add_comm, add_left_comm, add_assoc] using
    (pacBayes_generalization_bound (X := X) (μ := μ) (g := g) (C := C) (ε := ε)
      (δ := δ) (klPQ := klPQ) (n := n)
      (hn := hn) (hC := hC) (hε := hε) (hδ := hδ) (hk := hk)
      (hg_meas := hg_meas) (hg_bd := hg_bd))


/-!
## DRSB / Schrödinger-bridge specialization scaffolding

This shows how to instantiate Theorem 4 when the KL term lives on *path space*.
-/

namespace DRSB

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Terminal marginal `P₁` induced by a measurable terminal evaluation `eval₁`. -/
noncomputable def terminalMarginal (P : Measure Ω) (eval₁ : Ω → X) : Measure X :=
  Measure.map eval₁ P

/-- Placeholder for path-space KL divergence `KL(P‖Q)`. -/
noncomputable def KL (P Q : Measure Ω) : ℝ := 0

/-- Skeleton: Theorem 4 in "P/Q on paths, sample from P₁" form. -/
theorem theorem4_paths
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (eval₁ : Ω → X) (heval₁ : Measurable eval₁)
    {n : ℕ} (hn : 0 < n)
    (g : X → ℝ) (hg_meas : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hg_bd : ∀ x, |g x| ≤ C)
    {δ ε : ℝ} (hδ : 0 < δ ∧ δ < 1) (hε : 0 < ε) :
    let P₁ : Measure X := terminalMarginal (P := P) (eval₁ := eval₁)
    let μn : Measure (Fin n → X) := sampleMeasure (X := X) P₁ n
    μn {s | popMean P₁ g ≤ empMean (X := X) n g s
            + (Real.log (1 / δ) + KL (P := P) (Q := Q)) / ε
            + ε * C^2 / (2 * (n : ℝ)) }
      ≥ ENNReal.ofReal (1 - δ) := by
  intro P₁ μn
  -- Provide a probability-measure instance for the terminal marginal.
  have instP₁ : IsProbabilityMeasure P₁ := by
    refine ⟨by
      -- `P₁ univ = P (eval₁ ⁻¹' univ) = P univ = 1`.
      simp [P₁, terminalMarginal, Measure.map_apply, heval₁]⟩
  letI : IsProbabilityMeasure P₁ := instP₁
  have hk : 0 ≤ KL (P := P) (Q := Q) := by
    simp [KL]
  simpa [μn, P₁, terminalMarginal, pow_two] using
    (theorem4_twopager (X := X) (μ := P₁) (hn := hn) (g := g) (hg_meas := hg_meas)
      (C := C) (hC := hC) (hg_bd := hg_bd) (δ := δ) (ε := ε)
      (klPQ := KL (P := P) (Q := Q)) hδ hε hk)

end DRSB

end TwoPagerPACBayes
