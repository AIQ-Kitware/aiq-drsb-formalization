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

STATUS: PROVED. The four theorems below are axiom-clean ports of the proofs in
`reference/WellKnown.lean` (namespace `DRSB.WellKnown`), whose statements matched
these byte-for-byte. See `AGENTS.md` §6/§9 (the "free sorry removals" step).
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

end ForMathlib.MeasureTheory
