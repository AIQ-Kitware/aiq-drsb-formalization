/-
# Convexity of the Kullback–Leibler divergence in its first argument (Mathlib-staging)

`klDiv (a•μ₁ + b•μ₂) ν ≤ a·klDiv μ₁ ν + b·klDiv μ₂ ν`, in `ℝ≥0∞` — no finiteness hypotheses.

Mathlib has `klDiv_smul_same` and `klDiv_smul_right_eq_smul_left`, but **no convexity of `klDiv` in
its first argument**, in either `ℝ` or `ℝ≥0∞`. Both ingredients of the standard proof are present,
though: `klDiv_eq_lintegral_klFun_of_ac` writes `klDiv μ ν = ∫⁻ ofReal (klFun (dμ/dν))`, and
`convexOn_klFun` is the convexity of `klFun x = x log x + 1 − x` on `[0, ∞)`. So the divergence
inherits convexity pointwise from `klFun`, through the Radon–Nikodym derivative.

## Why the `ℝ≥0∞` form is the one to have

The `toReal` form of this inequality is *false* without knowing the mixture's KL is finite: `toReal`
sends `⊤` to the junk value `0`. Stating it in `ℝ≥0∞` removes the bad branch, so finiteness need not
be hypothesised — it is **derived** (`klDiv_mix_ne_top`), and the `toReal` form
(`toReal_klDiv_mix_le`) falls out as a corollary rather than carrying the extra assumptions.

(The same inequality is also a two-line consequence of the Donsker–Varadhan *dual* variational
formula — `KL(·‖ν)` is a supremum of affine functionals, and a supremum of affine functions is
convex; see `ForMathlib.MeasureTheory.toReal_klDiv_eq_sSup_dvDualSet`. That route yields only the
`toReal` statement, and only under the mixture's finiteness, so it does not supersede this one.)

This is what the entropic-DRO value function needs, to know its constraint set
`{γ : 𝔼_γ[c] + κ·KL(γ‖μ̂⊗ν) ≤ t}` is convex.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace ForMathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **`klDiv` is convex in its first argument** (`ℝ≥0∞`-valued, no finiteness hypotheses).

Proof: with both `μᵢ ≪ ν`, `klDiv μᵢ ν = ∫⁻ ofReal (klFun (dμᵢ/dν)) dν`. The mixture's
Radon–Nikodym derivative is the mixture of the derivatives (`Measure.rnDeriv_add'`,
`Measure.rnDeriv_smul_left'`), and `klFun` is convex on `[0, ∞)` (`convexOn_klFun`), so the
integrands compare pointwise; integrate. -/
theorem klDiv_mix_le (a b : ℝ≥0) (hab : a + b = 1)
    (μ₁ μ₂ ν : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν]
    (hac₁ : μ₁ ≪ ν) (hac₂ : μ₂ ≪ ν) :
    klDiv (a • μ₁ + b • μ₂) ν ≤ a * klDiv μ₁ ν + b * klDiv μ₂ ν := by
  have hac : a • μ₁ + b • μ₂ ≪ ν := by
    intro s hs
    simp [Measure.coe_add, Measure.coe_smul, hac₁ hs, hac₂ hs]
  have hmeas₁ : Measurable fun x => ENNReal.ofReal (klFun ((μ₁.rnDeriv ν x).toReal)) :=
    (measurable_klFun.comp (μ₁.measurable_rnDeriv ν).ennreal_toReal).ennreal_ofReal
  have hmeas₂ : Measurable fun x => ENNReal.ofReal (klFun ((μ₂.rnDeriv ν x).toReal)) :=
    (measurable_klFun.comp (μ₂.measurable_rnDeriv ν).ennreal_toReal).ennreal_ofReal
  have hr : (a • μ₁ + b • μ₂).rnDeriv ν
      =ᵐ[ν] fun x => (a : ℝ≥0∞) * μ₁.rnDeriv ν x + (b : ℝ≥0∞) * μ₂.rnDeriv ν x := by
    filter_upwards [Measure.rnDeriv_add' (a • μ₁) (b • μ₂) ν,
      Measure.rnDeriv_smul_left' μ₁ ν a, Measure.rnDeriv_smul_left' μ₂ ν b] with x h1 h2 h3
    rw [h1]
    simp only [Pi.add_apply, h2, h3, Pi.smul_apply]
    simp only [ENNReal.smul_def, smul_eq_mul]
  have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast congrArg NNReal.toReal hab
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (klFun (((a • μ₁ + b • μ₂).rnDeriv ν x).toReal))
      ≤ (a : ℝ≥0∞) * ENNReal.ofReal (klFun ((μ₁.rnDeriv ν x).toReal))
        + (b : ℝ≥0∞) * ENNReal.ofReal (klFun ((μ₂.rnDeriv ν x).toReal)) := by
    filter_upwards [hr, μ₁.rnDeriv_ne_top ν, μ₂.rnDeriv_ne_top ν] with x hx h1 h2
    set r₁ := (μ₁.rnDeriv ν x).toReal with hr₁
    set r₂ := (μ₂.rnDeriv ν x).toReal with hr₂
    have hr₁0 : 0 ≤ r₁ := ENNReal.toReal_nonneg
    have hr₂0 : 0 ≤ r₂ := ENNReal.toReal_nonneg
    have htoReal : ((a • μ₁ + b • μ₂).rnDeriv ν x).toReal = (a : ℝ) * r₁ + (b : ℝ) * r₂ := by
      rw [hx, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
    rw [htoReal]
    have k1 : 0 ≤ klFun r₁ := klFun_nonneg hr₁0
    have k2 : 0 ≤ klFun r₂ := klFun_nonneg hr₂0
    have hconv := convexOn_klFun.2 (Set.mem_Ici.mpr hr₁0) (Set.mem_Ici.mpr hr₂0)
      a.coe_nonneg b.coe_nonneg hab'
    simp only [smul_eq_mul] at hconv
    calc ENNReal.ofReal (klFun ((a : ℝ) * r₁ + (b : ℝ) * r₂))
        ≤ ENNReal.ofReal ((a : ℝ) * klFun r₁ + (b : ℝ) * klFun r₂) :=
          ENNReal.ofReal_le_ofReal hconv
      _ = (a : ℝ≥0∞) * ENNReal.ofReal (klFun r₁) + (b : ℝ≥0∞) * ENNReal.ofReal (klFun r₂) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  rw [klDiv_eq_lintegral_klFun_of_ac hac, klDiv_eq_lintegral_klFun_of_ac hac₁,
    klDiv_eq_lintegral_klFun_of_ac hac₂, ← lintegral_const_mul _ hmeas₁,
    ← lintegral_const_mul _ hmeas₂, ← lintegral_add_left (hmeas₁.const_mul _)]
  exact lintegral_mono_ae hpt


/-- **A convex combination of measures with finite KL has finite KL.** Immediate from
`klDiv_mix_le`, and *not* obtainable from the Donsker–Varadhan dual formula, which yields the
`toReal` inequality only after finiteness is already known. -/
theorem klDiv_mix_ne_top (a b : ℝ≥0) (hab : a + b = 1)
    (μ₁ μ₂ ν : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν]
    (hac₁ : μ₁ ≪ ν) (hac₂ : μ₂ ≪ ν)
    (h₁ : klDiv μ₁ ν ≠ ⊤) (h₂ : klDiv μ₂ ν ≠ ⊤) :
    klDiv (a • μ₁ + b • μ₂) ν ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (klDiv_mix_le a b hab μ₁ μ₂ ν hac₁ hac₂)

/-- **Relative entropy is convex in its first argument** (`ℝ`-valued). The `toReal` form of
`klDiv_mix_le`, with the mixture's finiteness *derived* rather than assumed. -/
theorem toReal_klDiv_mix_le (a b : ℝ≥0) (hab : a + b = 1)
    (μ₁ μ₂ ν : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν]
    (hac₁ : μ₁ ≪ ν) (hac₂ : μ₂ ≪ ν)
    (h₁ : klDiv μ₁ ν ≠ ⊤) (h₂ : klDiv μ₂ ν ≠ ⊤) :
    (klDiv (a • μ₁ + b • μ₂) ν).toReal
      ≤ (a : ℝ) * (klDiv μ₁ ν).toReal + (b : ℝ) * (klDiv μ₂ ν).toReal := by
  have hle := klDiv_mix_le a b hab μ₁ μ₂ ν hac₁ hac₂
  have hfin : (a : ℝ≥0∞) * klDiv μ₁ ν + (b : ℝ≥0∞) * klDiv μ₂ ν ≠ ⊤ := by finiteness
  calc (klDiv (a • μ₁ + b • μ₂) ν).toReal
      ≤ ((a : ℝ≥0∞) * klDiv μ₁ ν + (b : ℝ≥0∞) * klDiv μ₂ ν).toReal :=
        ENNReal.toReal_mono hfin hle
    _ = (a : ℝ) * (klDiv μ₁ ν).toReal + (b : ℝ) * (klDiv μ₂ ν).toReal := by
        rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
          ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]

end ForMathlib.MeasureTheory
