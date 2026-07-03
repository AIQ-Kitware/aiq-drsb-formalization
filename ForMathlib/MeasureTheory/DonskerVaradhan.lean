/-
# Donsker–Varadhan variational formula (Mathlib-staging)

The change-of-measure inequality and the variational (Gibbs) identity for the
Kullback–Leibler divergence. For probability measures `μ ≪ ν` and `f : α → ℝ`
with `exp ∘ f` integrable under `ν`:

* inequality form:  `∫ f dμ ≤ KL(μ‖ν) + log ∫ exp f dν`;
* variational form: `log ∫ exp f dν = sup_μ (∫ f dμ − KL(μ‖ν))`, attained at the
  `f`-tilted (Gibbs) measure `ν.tilted f`.

These are the root facts under the Sinkhorn-DRO entropic dual and the PAC-Bayes
change of measure (see `../prose/kl-dro-gibbs-donsker-varadhan.md`). Mathlib has the
tilting infrastructure (`Measure.tilted`, `integral_llr_tilted_right`, …) but not
the Donsker–Varadhan statement itself.

STATUS: statements only (`sorry`). Complete, axiom-clean proofs already exist in
`reference/WellKnown.lean` — port them after the statements are reviewed against the
prose. Do NOT trust the `reference/` versions blindly (they may carry extra
side-conditions); this file is the intended canonical statement.
-/
import Mathlib

open MeasureTheory InformationTheory
open scoped ENNReal

namespace ForMathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Donsker–Varadhan inequality** (change-of-measure / Gibbs inequality form).
For probability measures `μ ≪ ν` and `f` with `exp ∘ f` integrable under `ν`,
`∫ f dμ ≤ (klDiv μ ν).toReal + log (∫ exp f dν)`. -/
theorem integral_le_klDiv_add_log_integral_exp
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hμν : μ ≪ ν) (hfμ : Integrable f μ)
    (h_int : Integrable (llr μ ν) μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν) :
    ∫ x, f x ∂μ ≤ (klDiv μ ν).toReal + Real.log (∫ x, Real.exp (f x) ∂ν) := by
  sorry

/-- The Donsker–Varadhan bound is **attained at the tilted measure** `ν.tilted f`:
`∫ f d(ν.tilted f) − KL(ν.tilted f ‖ ν) = log (∫ exp f dν)`. -/
theorem integral_tilted_sub_klDiv_tilted
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hf_tilted : Integrable f (ν.tilted f)) :
    ∫ x, f x ∂(ν.tilted f) - (klDiv (ν.tilted f) ν).toReal
      = Real.log (∫ x, Real.exp (f x) ∂ν) := by
  sorry

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
  sorry

/-- Donsker–Varadhan as a supremum identity. -/
theorem log_integral_exp_eq_sSup
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hf_tilted : Integrable f (ν.tilted f)) :
    Real.log (∫ x, Real.exp (f x) ∂ν)
      = sSup { r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ ≪ ν ∧
          Integrable f μ ∧ Integrable (llr μ ν) μ ∧
          r = ∫ x, f x ∂μ - (klDiv μ ν).toReal } := by
  sorry

end ForMathlib.MeasureTheory
