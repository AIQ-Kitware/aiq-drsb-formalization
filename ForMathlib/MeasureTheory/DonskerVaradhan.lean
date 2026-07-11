/-
# Donsker–Varadhan variational formula (Mathlib-staging)

The change-of-measure inequality and the variational (Gibbs) identity for the
Kullback–Leibler divergence. For probability measures `μ ≪ ν` and `f : α → ℝ`
with `exp ∘ f` integrable under `ν`:

* inequality form:  `∫ f dμ ≤ KL(μ‖ν) + log ∫ exp f dν`;
* variational form: `log ∫ exp f dν = sup_μ (∫ f dμ − KL(μ‖ν))`, attained at the
  `f`-tilted (Gibbs) measure `ν.tilted f`.

These are the root fact under the Sinkhorn-DRO entropic dual (see
`../prose/kl-dro-gibbs-donsker-varadhan.md`). Mathlib has the
tilting infrastructure (`Measure.tilted`, `integral_llr_tilted_right`, …) but not
the Donsker–Varadhan statement itself.

The four theorems below port the corresponding proofs from `reference/WellKnown.lean`
(namespace `DRSB.WellKnown`) into the reusable `ForMathlib` namespace.
-/
import Mathlib

open MeasureTheory InformationTheory
open scoped ENNReal

namespace ForMathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Donsker–Varadhan inequality** (change-of-measure / Gibbs inequality form).
For probability measures `μ ≪ ν` and `f` with `exp ∘ f` integrable under `ν`,
`∫ f dμ ≤ (klDiv μ ν).toReal + log (∫ exp f dν)`.

Proof: tilt `ν` by `f`. Then `0 ≤ KL(μ ‖ ν.tilted f)` (Gibbs inequality), and by
`integral_llr_tilted_right` the right-hand side expands to
`∫ llr μ ν dμ − ∫ f dμ + log ∫ exp f dν`; rearranging gives the claim. -/
theorem integral_le_klDiv_add_log_integral_exp
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hμν : μ ≪ ν) (hfμ : Integrable f μ)
    (h_int : Integrable (llr μ ν) μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν) :
    ∫ x, f x ∂μ ≤ (klDiv μ ν).toReal + Real.log (∫ x, Real.exp (f x) ∂ν) := by
  have _hν' : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hμν' : μ ≪ ν.tilted f := hμν.trans (absolutelyContinuous_tilted hfν)
  have h_int' : Integrable (llr μ (ν.tilted f)) μ :=
    integrable_llr_tilted_right hμν hfμ h_int hfν
  -- Gibbs inequality: `KL(μ ‖ ν.tilted f) ≥ 0`.
  have hnonneg : 0 ≤ ∫ x, llr μ (ν.tilted f) x ∂μ := by
    have := integral_llr_add_sub_measure_univ_nonneg hμν' h_int'
    simpa using this
  rw [integral_llr_tilted_right hμν hfμ hfν h_int] at hnonneg
  -- `(klDiv μ ν).toReal = ∫ llr μ ν dμ` for equal-mass measures.
  rw [toReal_klDiv_of_measure_eq hμν (by simp)]
  linarith

/-- The Donsker–Varadhan bound is **attained at the tilted measure** `ν.tilted f`:
`∫ f d(ν.tilted f) − KL(ν.tilted f ‖ ν) = log (∫ exp f dν)`.

`llr (ν.tilted f) ν =ᵐ f − log Z` (the tilted log-density), so `KL` integrates to
`∫ f d(ν.tilted f) − log Z`, and the two `∫ f` terms cancel. -/
theorem integral_tilted_sub_klDiv_tilted
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hf_tilted : Integrable f (ν.tilted f)) :
    ∫ x, f x ∂(ν.tilted f) - (klDiv (ν.tilted f) ν).toReal
      = Real.log (∫ x, Real.exp (f x) ∂ν) := by
  have _hν' : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hac : ν.tilted f ≪ ν := tilted_absolutelyContinuous ν f
  have hae : llr (ν.tilted f) ν
      =ᵐ[ν.tilted f] fun x => f x - Real.log (∫ x, Real.exp (f x) ∂ν) :=
    hac.ae_le (log_rnDeriv_tilted_left_self (μ := ν) hfν)
  have hkl : (klDiv (ν.tilted f) ν).toReal = ∫ x, llr (ν.tilted f) ν x ∂(ν.tilted f) :=
    toReal_klDiv_of_measure_eq hac (by simp)
  rw [hkl, integral_congr_ae hae, integral_sub hf_tilted (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **Donsker–Varadhan variational principle** (Gibbs variational formula), as an
`IsGreatest`: over probability measures `μ ≪ ν` with `f`, `llr μ ν` integrable, the
functional `μ ↦ ∫ f dμ − KL(μ‖ν)` has maximum `log ∫ exp f dν`, attained at
`ν.tilted f`. -/
theorem isGreatest_donskerVaradhan
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hf_tilted : Integrable f (ν.tilted f)) :
    IsGreatest
      { r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ ≪ ν ∧
          Integrable f μ ∧ Integrable (llr μ ν) μ ∧
          r = ∫ x, f x ∂μ - (klDiv μ ν).toReal }
      (Real.log (∫ x, Real.exp (f x) ∂ν)) := by
  have _hν' : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hac : ν.tilted f ≪ ν := tilted_absolutelyContinuous ν f
  constructor
  · -- the value is achieved by the tilted measure
    refine ⟨ν.tilted f, _hν', hac, hf_tilted, ?_, ?_⟩
    · have hae : llr (ν.tilted f) ν
          =ᵐ[ν.tilted f] fun x => f x - Real.log (∫ x, Real.exp (f x) ∂ν) :=
        hac.ae_le (log_rnDeriv_tilted_left_self (μ := ν) hfν)
      exact (integrable_congr hae).mpr (hf_tilted.sub (integrable_const _))
    · exact (integral_tilted_sub_klDiv_tilted hfν hf_tilted).symm
  · -- every admissible value is bounded by it (the DV inequality)
    rintro r ⟨μ, hμ, hμν, hfμ, h_int, rfl⟩
    haveI := hμ
    have := integral_le_klDiv_add_log_integral_exp hμν hfμ h_int hfν
    linarith

/-- Donsker–Varadhan as a supremum identity. Immediate from
`isGreatest_donskerVaradhan`. -/
theorem log_integral_exp_eq_sSup
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hf_tilted : Integrable f (ν.tilted f)) :
    Real.log (∫ x, Real.exp (f x) ∂ν)
      = sSup { r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ ≪ ν ∧
          Integrable f μ ∧ Integrable (llr μ ν) μ ∧
          r = ∫ x, f x ∂μ - (klDiv μ ν).toReal } :=
  (isGreatest_donskerVaradhan hfν hf_tilted).csSup_eq.symm

/-- **A tilted measure has finite KL against its base.** `klDiv (ν.tilted g) ν ≠ ⊤` as soon as
`exp ∘ g` is `ν`-integrable and `g` is integrable against the tilt.

`klDiv ≠ ⊤` is `≪` plus integrability of the log-likelihood ratio, and `llr (ν.tilted g) ν` is
a.e. `g − log Z`. Needed to feed the KL chain rule, whose `h_fin` hypothesis is not optional. -/
theorem klDiv_tilted_ne_top {ν : Measure α} [IsProbabilityMeasure ν] {g : α → ℝ}
    (hexp : Integrable (fun x => Real.exp (g x)) ν) (hg : Integrable g (ν.tilted g)) :
    klDiv (ν.tilted g) ν ≠ ⊤ := by
  haveI : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted hexp
  have hac : ν.tilted g ≪ ν := tilted_absolutelyContinuous ν g
  refine klDiv_ne_top hac ?_
  have hae : llr (ν.tilted g) ν
      =ᵐ[ν.tilted g] fun x => g x - Real.log (∫ x, Real.exp (g x) ∂ν) :=
    hac.ae_le (log_rnDeriv_tilted_left_self (μ := ν) hexp)
  exact (hg.sub (integrable_const _)).congr hae.symm

/-- **The entropic Lagrangian's Gibbs supremum is attained at the tilted measure.**

For `λ, κ > 0`, cost slice `cx`, and `P = ν.tilted ((f − λ·cx)/(λκ))`,

`λκ · log ∫ exp((f − λ·cx)/(λκ)) dν  =  ∫ f dP − λ·(∫ cx dP + κ·KL(P‖ν))`.

This is the **pointwise converse Lagrangian bound** of Sinkhorn/entropic DRO duality, and unlike
its Wasserstein counterpart it is an *equality*, not an `ε`-approximation: the Donsker–Varadhan
supremum over measures (the Gibbs form) is attained, whereas the supremum over *functions* (the
dual form) is not. The left side is the per-point log-partition of the Wang–Gao–Xie dual.

Proof: rescale `integral_tilted_sub_klDiv_tilted` at `A = (f − λ·cx)/(λκ)` by `λκ`, then split
`λκ · ∫A dP = ∫f dP − λ ∫cx dP`. -/
theorem entropic_gibbs_attained_tilted {ν : Measure α} [IsProbabilityMeasure ν] {f cx : α → ℝ}
    {κ lam : ℝ} (hκ : 0 < κ) (hlam : 0 < lam)
    (hexp : Integrable (fun y => Real.exp ((f y - lam * cx y) / (lam * κ))) ν)
    (hf : Integrable f (ν.tilted fun y => (f y - lam * cx y) / (lam * κ)))
    (hc : Integrable cx (ν.tilted fun y => (f y - lam * cx y) / (lam * κ))) :
    lam * κ * Real.log (∫ y, Real.exp ((f y - lam * cx y) / (lam * κ)) ∂ν)
      = (∫ y, f y ∂(ν.tilted fun y => (f y - lam * cx y) / (lam * κ)))
        - lam * ((∫ y, cx y ∂(ν.tilted fun y => (f y - lam * cx y) / (lam * κ)))
          + κ * (klDiv (ν.tilted fun y => (f y - lam * cx y) / (lam * κ)) ν).toReal) := by
  set A : α → ℝ := fun y => (f y - lam * cx y) / (lam * κ) with hAdef
  set P : Measure α := ν.tilted A with hPdef
  have hlamκ : (0:ℝ) < lam * κ := mul_pos hlam hκ
  have hA_P : Integrable A P := (hf.sub (hc.const_mul lam)).div_const _
  have hkey := integral_tilted_sub_klDiv_tilted (ν := ν) (f := A) hexp hA_P
  have hAint : ∫ y, A y ∂P = (lam * κ)⁻¹ * ((∫ y, f y ∂P) - lam * ∫ y, cx y ∂P) := by
    simp only [hAdef, div_eq_mul_inv]
    rw [integral_mul_const, integral_sub hf (hc.const_mul lam), integral_const_mul]
    ring
  rw [hAint] at hkey
  have hmul := congrArg (fun r : ℝ => lam * κ * r) hkey
  rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlamκ), one_mul] at hmul
  rw [← hmul]
  ring

end ForMathlib.MeasureTheory
