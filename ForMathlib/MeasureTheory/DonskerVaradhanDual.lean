/-
# The Donsker–Varadhan *dual* variational formula (Mathlib-staging)

`ForMathlib.MeasureTheory.DonskerVaradhan` proves the **Gibbs** variational formula,

`log ∫ eᶠ dν = sup_μ (∫ f dμ − KL(μ‖ν))`,

whose supremum runs over *measures* and is attained at `ν.tilted f`. This file proves the **other**
Legendre transform,

`KL(μ‖ν) = sup_f (∫ f dμ − log ∫ eᶠ dν)`,

whose supremum runs over *bounded measurable functions* and is **not** attained in general.

They are different theorems, and only this one gives **lower semicontinuity of `klDiv`**: each
functional `μ ↦ ∫ f dμ − log ∫ eᶠ dν` is affine and weakly continuous in `μ` (for bounded continuous
`f`), so their supremum is lsc. That is the missing ingredient for weak closedness of an entropic
(Sinkhorn) ambiguity ball, hence for worst-case-measure attainment in entropic DRO.

The `≥` half is `integral_le_klDiv_add_log_integral_exp` (already proved). The content here is
**achievability**: a sequence of bounded `f` whose values converge to `KL(μ‖ν)`.

## The trap this file is built around

Lean's `llr μ ν x = Real.log ((μ.rnDeriv ν x).toReal)` and `Real.log 0 = 0`, so
`exp (llr μ ν x) = 1` — *not* `0` — on the set `{dμ/dν = 0}`. Truncating `llr` naively therefore
sends `∫ exp (llr) dν` to `1 + ν {dμ/dν = 0}`, and the resulting bound is off by
`log (1 + ν {dμ/dν = 0}) > 0`. The fix is to use the family

`truncLLR μ ν n x = if 0 < dμ/dν x then clamp (llr μ ν x) (-n) n else -n`,

which is `-n` (not `0`) on the bad set. Its `ν`-integral of `exp` then tends to exactly `1`, while
`∫ truncLLR n dμ` is unaffected because `{dμ/dν = 0}` is `μ`-null.

Mathlib has `klDiv`, `Measure.tilted` and the `rnDeriv` API, but neither this formula nor lower
semicontinuity of `klDiv`.
-/
import Mathlib
import ForMathlib.MeasureTheory.DonskerVaradhan

set_option autoImplicit false

open MeasureTheory InformationTheory Filter
open scoped ENNReal Topology

namespace ForMathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The truncation family driving the Donsker–Varadhan dual formula: clamp `llr μ ν` to `[-n, n]`
on `{dμ/dν > 0}`, and take the value `-n` on `{dμ/dν = 0}`.

Using `-n` rather than `0` on the bad set is essential; see the module docstring. -/
noncomputable def truncLLR (μ ν : Measure α) (n : ℕ) (x : α) : ℝ :=
  if 0 < μ.rnDeriv ν x then max (min (llr μ ν x) n) (-n) else -n

variable (μ ν : Measure α)

theorem measurable_truncLLR [SigmaFinite μ] [SigmaFinite ν] (n : ℕ) :
    Measurable (truncLLR μ ν n) := by
  unfold truncLLR
  have hllr : Measurable (llr μ ν) := (Measure.measurable_rnDeriv μ ν).ennreal_toReal.log
  exact Measurable.ite (measurableSet_lt measurable_const (Measure.measurable_rnDeriv μ ν))
    ((hllr.min measurable_const).max measurable_const) measurable_const

/-- `truncLLR μ ν n` is bounded by `n`; in particular it is bounded, so it is integrable against
any probability measure and its exponential is too. -/
theorem abs_truncLLR_le (n : ℕ) (x : α) : |truncLLR μ ν n x| ≤ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold truncLLR
  split
  · rw [abs_le]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩
  · rw [abs_le]; constructor <;> linarith

/-- On `{dμ/dν > 0}` the exponential of the truncation is a clamp of `dμ/dν`. -/
theorem exp_truncLLR_of_pos (n : ℕ) (x : α) (h : 0 < μ.rnDeriv ν x) (hx : μ.rnDeriv ν x ≠ ⊤) :
    Real.exp (truncLLR μ ν n x)
      = max (min (μ.rnDeriv ν x).toReal (Real.exp n)) (Real.exp (-n)) := by
  unfold truncLLR
  rw [if_pos h, Real.exp_monotone.map_max, Real.exp_monotone.map_min, llr, Real.exp_log]
  exact ENNReal.toReal_pos h.ne' hx

/-- On `{dμ/dν = 0}` the exponential of the truncation is `exp (-n)`, which tends to `0`. -/
theorem exp_truncLLR_of_not_pos (n : ℕ) (x : α) (h : ¬ (0 < μ.rnDeriv ν x)) :
    Real.exp (truncLLR μ ν n x) = Real.exp (-n) := by
  unfold truncLLR; rw [if_neg h]

/-- `exp (truncLLR n) ≤ dμ/dν + 1`, an integrable `ν`-envelope. -/
theorem exp_truncLLR_le (n : ℕ) (x : α) (hx : μ.rnDeriv ν x ≠ ⊤) :
    Real.exp (truncLLR μ ν n x) ≤ (μ.rnDeriv ν x).toReal + 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : (0 : ℝ) ≤ (μ.rnDeriv ν x).toReal := ENNReal.toReal_nonneg
  have he : Real.exp (-(n : ℝ)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  by_cases h : 0 < μ.rnDeriv ν x
  · rw [exp_truncLLR_of_pos μ ν n x h hx]
    exact max_le (le_trans (min_le_left _ _) (by linarith)) (by linarith)
  · rw [exp_truncLLR_of_not_pos μ ν n x h]; linarith

/-- `ν`-a.e., `exp (truncLLR n) → dμ/dν`. -/
theorem tendsto_exp_truncLLR [SigmaFinite μ] [SigmaFinite ν] :
    ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => Real.exp (truncLLR μ ν n x)) atTop
      (𝓝 ((μ.rnDeriv ν x).toReal)) := by
  filter_upwards [μ.rnDeriv_lt_top ν] with x hx
  by_cases h : 0 < μ.rnDeriv ν x
  · have hpos : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos h.ne' hx.ne
    have heq : (fun n : ℕ => Real.exp (truncLLR μ ν n x))
        =ᶠ[atTop] (fun _ => (μ.rnDeriv ν x).toReal) := by
      have h1 : ∀ᶠ n : ℕ in atTop, (μ.rnDeriv ν x).toReal ≤ Real.exp n := by
        filter_upwards [eventually_ge_atTop ⌈(μ.rnDeriv ν x).toReal⌉₊] with n hn
        calc (μ.rnDeriv ν x).toReal ≤ (⌈(μ.rnDeriv ν x).toReal⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ Real.exp n := (Real.add_one_le_exp _).trans' (by linarith)
      have h2 : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) ≤ (μ.rnDeriv ν x).toReal := by
        have := Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop)
        exact (this.eventually (eventually_le_nhds hpos)).mono fun n hn => hn
      filter_upwards [h1, h2] with n hn1 hn2
      rw [exp_truncLLR_of_pos μ ν n x h hx.ne, min_eq_left hn1, max_eq_left hn2]
    exact Tendsto.congr' heq.symm tendsto_const_nhds
  · have hz : (μ.rnDeriv ν x).toReal = 0 := by
      simp only [not_lt, nonpos_iff_eq_zero] at h; simp [h]
    simp only [exp_truncLLR_of_not_pos μ ν _ x h, hz]
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop)

/-- **The partition functions converge to `1`.** This is exactly where the `-n`-on-the-bad-set
choice pays: the mass `ν {dμ/dν = 0}` is carried to `0` by `exp (-n)`, instead of contributing
`ν {dμ/dν = 0}` as it would for the naive truncation. -/
theorem tendsto_integral_exp_truncLLR [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    Tendsto (fun n : ℕ => ∫ x, Real.exp (truncLLR μ ν n x) ∂ν) atTop (𝓝 1) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x => Real.exp (truncLLR μ ν n x)) ν :=
    fun n => ((measurable_truncLLR μ ν n).exp).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂ν, ‖Real.exp (truncLLR μ ν n x)‖ ≤ (μ.rnDeriv ν x).toReal + 1 := by
    intro n
    filter_upwards [μ.rnDeriv_lt_top ν] with x hx
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact exp_truncLLR_le μ ν n x hx.ne
  have henv : Integrable (fun x => (μ.rnDeriv ν x).toReal + 1) ν :=
    Measure.integrable_toReal_rnDeriv.add (integrable_const 1)
  have hdct := tendsto_integral_of_dominated_convergence _ hmeas henv hbound
    (tendsto_exp_truncLLR μ ν)
  have hone : ∫ x, (μ.rnDeriv ν x).toReal ∂ν = 1 := by
    have := integral_toReal_rnDeriv_mul (μ := μ) (ν := ν) hac (f := fun _ => (1 : ℝ))
    simpa using this
  rwa [hone] at hdct

/-- `μ`-a.e., `truncLLR n → llr μ ν`, dominated by `|llr μ ν|`. -/
theorem tendsto_integral_truncLLR [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) :
    Tendsto (fun n : ℕ => ∫ x, truncLLR μ ν n x ∂μ) atTop (𝓝 (∫ x, llr μ ν x ∂μ)) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (truncLLR μ ν n) μ :=
    fun n => (measurable_truncLLR μ ν n).aestronglyMeasurable
  -- on the `μ`-full set `{dμ/dν > 0}` the truncation is the plain clamp of `llr`
  have hpos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := Measure.rnDeriv_pos hac
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂μ, ‖truncLLR μ ν n x‖ ≤ |llr μ ν x| := by
    intro n
    filter_upwards [hpos] with x hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [Real.norm_eq_abs, truncLLR, if_pos hx, abs_le]
    have habs : (0 : ℝ) ≤ |llr μ ν x| := abs_nonneg _
    -- `-|l| ≤ min l n` (both branches), and `min l n ≤ max (min l n) (-n)`
    have hmin : -|llr μ ν x| ≤ min (llr μ ν x) (n : ℝ) :=
      le_min (neg_abs_le _) (by linarith)
    refine ⟨le_trans hmin (le_max_left _ _), ?_⟩
    exact max_le (le_trans (min_le_left _ _) (le_abs_self _)) (by linarith)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => truncLLR μ ν n x) atTop (𝓝 (llr μ ν x)) := by
    filter_upwards [hpos] with x hx
    have heq : (fun n : ℕ => truncLLR μ ν n x) =ᶠ[atTop] (fun _ => llr μ ν x) := by
      filter_upwards [eventually_ge_atTop ⌈|llr μ ν x|⌉₊] with n hn
      have hb : |llr μ ν x| ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn)
      rw [truncLLR, if_pos hx, min_eq_left ((le_abs_self _).trans hb),
        max_eq_left (by linarith [neg_abs_le (llr μ ν x)])]
    exact Tendsto.congr' heq.symm tendsto_const_nhds
  exact tendsto_integral_of_dominated_convergence _ hmeas hllr.abs hbound hlim

/-- The set of achievable values `∫ f dμ − log ∫ eᶠ dν`, over bounded measurable `f`. -/
def dvDualSet (μ ν : Measure α) : Set ℝ :=
  { r : ℝ | ∃ f : α → ℝ, Measurable f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧
      r = ∫ x, f x ∂μ - Real.log (∫ x, Real.exp (f x) ∂ν) }

theorem dvDualSet_nonempty [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (dvDualSet μ ν).Nonempty :=
  ⟨0, fun _ => 0, measurable_const, ⟨0, by simp⟩, by simp⟩

/-- Every achievable value is `≤ KL(μ‖ν)`: the Donsker–Varadhan inequality. -/
theorem dvDualSet_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) :
    ∀ r ∈ dvDualSet μ ν, r ≤ (klDiv μ ν).toReal := by
  rintro r ⟨f, hf, ⟨C, hC⟩, rfl⟩
  have hfμ : Integrable f μ :=
    Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hfν : Integrable (fun x => Real.exp (f x)) ν := by
    refine Integrable.mono' (integrable_const (Real.exp C)) hf.exp.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hC x))
  have := integral_le_klDiv_add_log_integral_exp hac hfμ hllr hfν
  linarith

/-- **Donsker–Varadhan, dual variational formula.**
`KL(μ‖ν) = sup { ∫ f dμ − log ∫ eᶠ dν : f bounded measurable }`.

The `≥` half is the Donsker–Varadhan inequality. The `≤` half is achievability, witnessed by the
truncated log-likelihood ratios `truncLLR μ ν n`: their values converge to `KL(μ‖ν)` because
`∫ truncLLR n dμ → ∫ llr dμ = KL(μ‖ν)` and the partition functions `∫ exp (truncLLR n) dν → 1`.

The supremum is generally **not attained** (the optimal `f = llr μ ν` need not be bounded), which is
why this is an `sSup` identity and not an `IsGreatest` — in contrast to the Gibbs formula
`isGreatest_donskerVaradhan`, whose supremum *is* attained, at `ν.tilted f`. -/
theorem toReal_klDiv_eq_sSup_dvDualSet [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) :
    (klDiv μ ν).toReal = sSup (dvDualSet μ ν) := by
  have hbdd : BddAbove (dvDualSet μ ν) := ⟨(klDiv μ ν).toReal, dvDualSet_le μ ν hac hllr⟩
  refine le_antisymm ?_ (csSup_le (dvDualSet_nonempty μ ν) (dvDualSet_le μ ν hac hllr))
  -- achievability: the truncated log-likelihood ratios realise `KL` in the limit
  have hmem : ∀ n : ℕ,
      (∫ x, truncLLR μ ν n x ∂μ) - Real.log (∫ x, Real.exp (truncLLR μ ν n x) ∂ν)
        ∈ dvDualSet μ ν := fun n =>
    ⟨truncLLR μ ν n, measurable_truncLLR μ ν n, ⟨n, abs_truncLLR_le μ ν n⟩, rfl⟩
  have hZ : Tendsto (fun n : ℕ => Real.log (∫ x, Real.exp (truncLLR μ ν n x) ∂ν)) atTop (𝓝 0) := by
    have := (tendsto_integral_exp_truncLLR μ ν hac).log one_ne_zero
    simpa using this
  have hlim : Tendsto
      (fun n : ℕ => (∫ x, truncLLR μ ν n x ∂μ) - Real.log (∫ x, Real.exp (truncLLR μ ν n x) ∂ν))
      atTop (𝓝 ((klDiv μ ν).toReal)) := by
    have hI := tendsto_integral_truncLLR μ ν hac hllr
    rw [← toReal_klDiv_of_measure_eq hac (by simp)] at hI
    simpa using hI.sub hZ
  exact le_of_tendsto hlim (Eventually.of_forall fun n => le_csSup hbdd (hmem n))

/-! ## Semicontinuity: the payoff

A supremum of functionals each of which is *continuous along the convergence in question* is lower
semicontinuous. Concretely, a `KL`-ball is closed under any convergence that integrates bounded
measurable functions correctly. This is the ingredient a Sinkhorn/entropic ambiguity ball needs in
order to be weakly closed, and hence (with Prokhorov) weakly compact — the route to
worst-case-measure attainment. -/

/-- **Lower semicontinuity of `klDiv` in its first argument**, in the form an ambiguity ball needs:
if `μs i → μ` in the sense that bounded measurable functions integrate correctly, and every
`μs i` lies in the `KL`-ball of radius `C` around `ν`, then so does `μ`.

Proof: each achievable value `∫ f dμ − log ∫ eᶠ dν` is the limit of the corresponding values for
`μs i`, each of which is `≤ KL(μs i‖ν) ≤ C` by the Donsker–Varadhan inequality. Take the supremum
over `f` and apply `toReal_klDiv_eq_sSup_dvDualSet`.

Note the convergence hypothesis is over bounded **measurable** `f` (setwise / τ-topology). For the
*weak* topology one needs bounded **continuous** `f`, which requires upgrading `dvDualSet` by a
regularity argument; on a Polish space that is Lusin's theorem. -/
theorem toReal_klDiv_le_of_tendsto_integral {ι : Type*} {l : Filter ι} [l.NeBot]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (μs : ι → Measure α)
    [∀ i, IsProbabilityMeasure (μs i)]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ)
    (hacs : ∀ i, μs i ≪ ν) (hllrs : ∀ i, Integrable (llr (μs i) ν) (μs i))
    (hconv : ∀ f : α → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun i => ∫ x, f x ∂(μs i)) l (𝓝 (∫ x, f x ∂μ)))
    (C : ℝ) (hC : ∀ i, (klDiv (μs i) ν).toReal ≤ C) :
    (klDiv μ ν).toReal ≤ C := by
  rw [toReal_klDiv_eq_sSup_dvDualSet μ ν hac hllr]
  refine csSup_le (dvDualSet_nonempty μ ν) ?_
  rintro r ⟨f, hf, hb, rfl⟩
  -- each `μs i` gives the same functional a value `≤ C`
  have hstep : ∀ i, (∫ x, f x ∂(μs i)) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ C := fun i =>
    le_trans (dvDualSet_le (μs i) ν (hacs i) (hllrs i) _ ⟨f, hf, hb, rfl⟩) (hC i)
  -- pass to the limit
  have hlim : Tendsto (fun i => (∫ x, f x ∂(μs i)) - Real.log (∫ x, Real.exp (f x) ∂ν)) l
      (𝓝 ((∫ x, f x ∂μ) - Real.log (∫ x, Real.exp (f x) ∂ν))) :=
    (hconv f hf hb).sub tendsto_const_nhds
  exact le_of_tendsto hlim (Eventually.of_forall hstep)

/-! ## Convexity of `klDiv` — the dual formula paying off a second time

A supremum of **affine** functionals is convex. `toReal_klDiv_eq_sSup_dvDualSet` writes `KL(·‖ν)` as
`sup_f (∫f d· − log ∫eᶠdν)`, and each of those is affine in the measure. So relative entropy is
convex in its first argument, with no `rnDeriv` manipulation at all.

Mathlib has `klDiv` and the `smul` lemmas (`toReal_klDiv_smul_left`, …) but **no convexity**
(grep-verified). This is the ingredient the *entropic* analogue of Wasserstein-DRO strong duality
needs, exactly as `ForMathlib.OT.concaveOn_droValueAt` (which rests on affinity of `couplingCost`)
is what the Wasserstein one needs: it makes the Sinkhorn objective `𝔼_γ[c] + κ·KL(γ‖μ̂⊗ν)` convex in
the coupling, hence the entropic value function concave. -/

/-- **Relative entropy is convex in its first argument.** Immediate from the dual variational
formula: `KL(·‖ν)` is a supremum of affine functionals of the measure. -/
theorem toReal_klDiv_mix_le (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1)
    (μ₁ μ₂ ν : Measure α) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν]
    (hac₁ : μ₁ ≪ ν) (hac₂ : μ₂ ≪ ν)
    (hllr₁ : Integrable (llr μ₁ ν) μ₁) (hllr₂ : Integrable (llr μ₂ ν) μ₂)
    (μ : Measure α) [IsProbabilityMeasure μ]
    (hμdef : μ = ENNReal.ofReal a • μ₁ + ENNReal.ofReal (1 - a) • μ₂)
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) :
    (klDiv μ ν).toReal ≤ a * (klDiv μ₁ ν).toReal + (1 - a) * (klDiv μ₂ ν).toReal := by
  have ha0 : 0 ≤ a := ha.1
  have ha1 : 0 ≤ 1 - a := by linarith [ha.2]
  rw [toReal_klDiv_eq_sSup_dvDualSet μ ν hac hllr]
  refine csSup_le (dvDualSet_nonempty μ ν) ?_
  rintro r ⟨f, hf, ⟨C, hC⟩, rfl⟩
  have hbound : ∀ (ρ : Measure α) [IsProbabilityMeasure ρ], Integrable f ρ := by
    intro ρ _
    exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hsplit : ∫ x, f x ∂μ = a * ∫ x, f x ∂μ₁ + (1 - a) * ∫ x, f x ∂μ₂ := by
    rw [hμdef, integral_add_measure ((hbound μ₁).smul_measure ENNReal.ofReal_ne_top)
        ((hbound μ₂).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal ha1]
    simp [smul_eq_mul]
  -- each summand is an admissible value for the corresponding measure
  have h1 : (∫ x, f x ∂μ₁) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ (klDiv μ₁ ν).toReal :=
    dvDualSet_le μ₁ ν hac₁ hllr₁ _ ⟨f, hf, ⟨C, hC⟩, rfl⟩
  have h2 : (∫ x, f x ∂μ₂) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ (klDiv μ₂ ν).toReal :=
    dvDualSet_le μ₂ ν hac₂ hllr₂ _ ⟨f, hf, ⟨C, hC⟩, rfl⟩
  have k1 := mul_le_mul_of_nonneg_left h1 ha0
  have k2 := mul_le_mul_of_nonneg_left h2 ha1
  have hL : Real.log (∫ x, Real.exp (f x) ∂ν)
      = a * Real.log (∫ x, Real.exp (f x) ∂ν)
        + (1 - a) * Real.log (∫ x, Real.exp (f x) ∂ν) := by ring
  nlinarith [k1, k2, hsplit, hL]


end ForMathlib.MeasureTheory
