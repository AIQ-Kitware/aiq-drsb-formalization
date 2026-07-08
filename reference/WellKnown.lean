/-
# DrsbBridge/WellKnown.lean

Canonical, self-contained statements (and proofs) of the *well-known* probability
theorems that the DRSB / TwoPager development relies on. These are deliberately
phrased in terms of generic Mathlib objects (`MeasureTheory.Measure.pi`,
`ProbabilityTheory.mgf`, …) rather than the DRSB-specific wrappers
(`sampleMeasure`, `empAvgSample`, `Expect`). The DRSB files import this module and
adapt each result to their own definitions with a one-line `simp [...]` unfold.

Design rationale
----------------
* **One canonical proof per theorem.** The DRSB files should never re-derive
  Hoeffding / Markov / Donsker–Varadhan; they call the versions here.
* **No project-specific defs leak in.** Everything is stated over an abstract
  probability space, so this file could be lifted into any other thrust (or
  upstreamed to Mathlib) unchanged.
* **Honest provenance.** Each result is built from the Mathlib lemmas cited in
  its docstring. As of this writing (Mathlib master, Lean v4.28) the entire
  sub-Gaussian MGF toolkit lives in `Mathlib/Probability/Moments/SubGaussian.lean`.

Status legend in this file:
  ✅  fully proved and compiles (no placeholder).
  🚧  statement is final; proof is a placeholder with a precise pointer to the
      Mathlib lemma to finish it.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace DRSB.WellKnown

/-! ## Helper: marginal of a coordinate under a finite product measure

`∫ s, g (s i) ∂(Measure.pi μ) = ∫ x, g x ∂(μ i)`.

This is the "each coordinate has the right marginal" fact, used to identify the
centering constant in Hoeffding's lemma with the population mean `∫ g ∂μ`.

Built from `MeasureTheory.measurePreserving_eval` (Pi.lean:400) + `integral_map`. ✅
-/
lemma integral_eval_pi {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (i : ι)
    {g : Ω → ℝ} (hg : Measurable g) :
    ∫ s, g (s i) ∂(Measure.pi μ) = ∫ x, g x ∂(μ i) := by
  have hpres : MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) :=
    measurePreserving_eval μ i
  -- rewrite `μ i` as the pushforward, then peel it off with `integral_map`
  rw [← hpres.map_eq,
      integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]

/-! ## Hoeffding MGF bound for an i.i.d. empirical mean

If `g : Ω → ℝ` is measurable with `g x ∈ [-C, C]` for all `x`, and `s` is an
i.i.d. sample of size `n ≥ 1` from a probability measure `μ` (modelled as
`Measure.pi (fun _ : Fin n => μ)`), then the moment-generating function of the
deviation between the empirical mean and the population mean obeys

    ∫ exp( t · ( (1/n) Σᵢ g(sᵢ) − E[g] ) ) dμⁿ  ≤  exp( t² C² / (2n) ).

This is the `hoeffding_mgf_bound` lemma in `drsb-v4.lean`, modulo unfolding
`sampleMeasure`, `empAvgSample`, and `Expect`.

Proof chain (all Mathlib lemmas confirmed present):
1. Each centred coordinate `Zᵢ s = g(sᵢ) − E[g]` is sub-Gaussian with parameter
   `c = (‖C − (−C)‖₊ / 2)² = C²`, by
   `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` (SubGaussian.lean:860).
   The centering constant it introduces is the *coordinate* mean, which equals
   `E[g]` by `integral_eval_pi`.
2. The coordinates are independent under the product measure, by
   `ProbabilityTheory.iIndepFun_pi` (Independence/Basic.lean:784), composed with
   `· − E[g]` via `iIndepFun.comp`.
3. Hence `S s = Σᵢ Zᵢ s` is sub-Gaussian with parameter `Σᵢ c = n·C²`, by
   `HasSubgaussianMGF.sum_of_iIndepFun` (SubGaussian.lean:768).
4. The target integral is exactly `mgf S (μⁿ) (t/n)`, so `HasSubgaussianMGF.mgf_le`
   gives `≤ exp( (n·C²)·(t/n)²/2 ) = exp( t²C²/(2n) )`.

The per-coordinate sub-Gaussian parameter `(‖C − (−C)‖₊/2)² = C²`, summed over the
`n` coordinates, gives `n·C²`; evaluated at `t/n` the exponent collapses to the
advertised `t²C²/(2n)`.   ✅ verified
-/
theorem hoeffding_iid_mgf_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : n ≠ 0)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {g : Ω → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, g x ∈ Set.Icc (-C) C) (t : ℝ) :
    (∫ s, Real.exp (t * ((1 / (n : ℝ)) * ∑ i : Fin n, g (s i) - ∫ x, g x ∂μ))
        ∂(Measure.pi (fun _ : Fin n => μ)))
      ≤ Real.exp (t ^ 2 * C ^ 2 / (2 * (n : ℝ))) := by
  classical
  set P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ) with hP
  -- population mean
  set m : ℝ := ∫ x, g x ∂μ with hm
  -- centred coordinate functions and the per-coordinate sub-Gaussian parameter
  set Z : Fin n → (Fin n → Ω) → ℝ := fun i s => g (s i) - m with hZ
  set c : ℝ≥0 := (‖C - (-C)‖₊ / 2) ^ 2 with hc_def
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn

  -- (1) each coordinate marginal equals the population mean
  have hmean : ∀ i : Fin n, (∫ s, g (s i) ∂P) = m := by
    intro i; rw [hP]; exact integral_eval_pi _ i hg

  -- (1') each centred coordinate is sub-Gaussian with parameter `c`
  have hsub : ∀ i : Fin n, HasSubgaussianMGF (Z i) c P := by
    intro i
    have hXmeas : AEMeasurable (fun s : Fin n → Ω => g (s i)) P :=
      (hg.comp (measurable_pi_apply i)).aemeasurable
    have hXmem : ∀ᵐ s ∂P, (fun s : Fin n → Ω => g (s i)) s ∈ Set.Icc (-C) C :=
      ae_of_all _ fun s => hC (s i)
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P)
      (X := fun s : Fin n → Ω => g (s i)) hXmeas hXmem
    -- `h : HasSubgaussianMGF (fun s => g (s i) - P[fun s => g (s i)]) c P`
    -- rewrite the centring constant to `m`, yielding exactly `Z i`
    rwa [hmean i] at h

  -- (2) independence of the centred coordinates under the product measure
  have hindep0 : iIndepFun (fun (i : Fin n) (s : Fin n → Ω) => g (s i)) P := by
    rw [hP]; exact iIndepFun_pi (fun _ => hg.aemeasurable)
  have hindep : iIndepFun Z P := by
    have := hindep0.comp (fun _ (y : ℝ) => y - m) (fun _ => measurable_id.sub_const m)
    simpa [hZ, Function.comp] using this

  -- (3) the sum of the coordinates is sub-Gaussian with parameter `n • c`
  have hSsub : HasSubgaussianMGF (fun s => ∑ i : Fin n, Z i s)
      (∑ _i : Fin n, c) P :=
    HasSubgaussianMGF.sum_of_iIndepFun hindep (fun i _ => hsub i)

  -- (4a) rewrite the integrand: t·((1/n)Σg − m) = (t/n)·Σ(g − m)
  have key : ∀ s : Fin n → Ω,
      t * ((1 / (n : ℝ)) * ∑ i : Fin n, g (s i) - m)
        = (t / (n : ℝ)) * ∑ i : Fin n, Z i s := by
    intro s
    simp only [hZ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp

  -- (4b) the integral is `mgf S P (t/n)`; bound it and match constants
  calc (∫ s, Real.exp (t * ((1 / (n : ℝ)) * ∑ i : Fin n, g (s i) - m)) ∂P)
      = mgf (fun s => ∑ i : Fin n, Z i s) P (t / (n : ℝ)) := by
        simp only [mgf]
        congr 1
        funext s
        rw [key s]
    _ ≤ Real.exp ((↑(∑ _i : Fin n, c)) * (t / (n : ℝ)) ^ 2 / 2) := hSsub.mgf_le _
    _ = Real.exp (t ^ 2 * C ^ 2 / (2 * (n : ℝ))) := by
        congr 1
        have hc : (c : ℝ) = C ^ 2 := by
          rw [hc_def]
          push_cast [coe_nnnorm, Real.norm_eq_abs]
          -- (|C - (-C)| / 2)^2 = (|2C|/2)^2 = (2C)^2 / 2^2 = C^2
          rw [show C - (-C) = 2 * C by ring, div_pow, sq_abs]
          ring
        have hsum : ((∑ _i : Fin n, c : ℝ≥0) : ℝ) = (n : ℝ) * C ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast [hc]; ring
        rw [hsum]
        field_simp

/-! ## Markov / Chernoff exponential inequality

For a probability measure `μ`, a nonnegative integrable `Z`, and `a > 0`:

    μ {x | a ≤ Z x}  ≤  ENNReal.ofReal ( (∫ Z dμ) / a ).

This is `markov_inequality_exp` in `drsb-v4.lean`. Note this version additionally
requires `Integrable Z μ` — without it the Bochner integral is junk (`0`) and the
inequality is false, so the integrability hypothesis is mandatory.

Built from `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`
(`a · μ.real{a ≤ Z} ≤ ∫ Z`) followed by division by `a` and an `ENNReal.ofReal`
round-trip (`μ S` is finite under a probability measure). ✅
-/
theorem markov_exp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {Z : α → ℝ} (hZ : 0 ≤ᵐ[μ] Z)
    (hint : Integrable Z μ) {a : ℝ} (ha : 0 < a) :
    μ {x | a ≤ Z x} ≤ ENNReal.ofReal ((∫ x, Z x ∂μ) / a) := by
  have hkey : a * μ.real {x | a ≤ Z x} ≤ ∫ x, Z x ∂μ :=
    mul_meas_ge_le_integral_of_nonneg hZ hint a
  have hreal : μ.real {x | a ≤ Z x} ≤ (∫ x, Z x ∂μ) / a := by
    rw [le_div_iff₀ ha]; linarith
  calc μ {x | a ≤ Z x}
      = ENNReal.ofReal (μ.real {x | a ≤ Z x}) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal ((∫ x, Z x ∂μ) / a) := ENNReal.ofReal_le_ofReal hreal

/-! ## Donsker–Varadhan variational principle

For probability measures `μ, ν` on `α` and `f : α → ℝ`:

* **Inequality (change-of-measure) form** — for every `μ ≪ ν`:

      ∫ f dμ  ≤  KL(μ‖ν) + log ∫ exp f dν.

* **Variational (Gibbs) form** — the bound is tight, the supremum being attained
  at the `f`-tilted measure `ν.tilted f`:

      log ∫ exp f dν  =  sup_μ ( ∫ f dμ − KL(μ‖ν) ).

`klDiv μ ν : ℝ≥0∞` is Mathlib's Kullback–Leibler divergence (`InformationTheory`);
for probability measures `(klDiv μ ν).toReal = ∫ llr μ ν dμ` is the `ℝ`-valued KL
used by the DRSB `donsker_varadhan*` lemmas.

These are Mathlib-shaped (generic `Measure`, `klDiv`, standard integrability side
conditions) and are intended to be upstreamable: as of this writing Mathlib has
all the tilting infrastructure (`MeasureTheory.integral_llr_tilted_right`,
`Measure.tilted`, …) but not the Donsker–Varadhan statement itself.
-/
section DonskerVaradhan

open InformationTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Donsker–Varadhan inequality** (change-of-measure / Gibbs inequality form).

For probability measures `μ ≪ ν` and `f` with `exp ∘ f` integrable under `ν`,

    ∫ f dμ ≤ (klDiv μ ν).toReal + log (∫ exp f dν).

Proof: tilt `ν` by `f`. Then `0 ≤ KL(μ ‖ ν.tilted f)` (Gibbs inequality), and by
`integral_llr_tilted_right` the right-hand side expands to
`∫ llr μ ν dμ − ∫ f dμ + log ∫ exp f dν`; rearranging gives the claim. ✅ -/
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

    ∫ f d(ν.tilted f) − KL(ν.tilted f ‖ ν) = log (∫ exp f dν).

`llr (ν.tilted f) ν =ᵐ f − log Z` (the tilted log-density), so `KL` integrates to
`∫ f d(ν.tilted f) − log Z`, and the two `∫ f` terms cancel. ✅ -/
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
`IsGreatest`: over probability measures `μ ≪ ν` with `f` and `llr μ ν` integrable,
the functional `μ ↦ ∫ f dμ − KL(μ‖ν)` has maximum `log ∫ exp f dν`, attained at
`ν.tilted f`. ✅ -/
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

/-- Donsker–Varadhan as a supremum identity (the form used by the DRSB
`donsker_varadhan` lemma). Immediate from `isGreatest_donskerVaradhan`. ✅ -/
theorem log_integral_exp_eq_sSup
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hf_tilted : Integrable f (ν.tilted f)) :
    Real.log (∫ x, Real.exp (f x) ∂ν)
      = sSup { r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ ≪ ν ∧
          Integrable f μ ∧ Integrable (llr μ ν) μ ∧
          r = ∫ x, f x ∂μ - (klDiv μ ν).toReal } :=
  (isGreatest_donskerVaradhan hfν hf_tilted).csSup_eq.symm

end DonskerVaradhan

/-! ## PAC-Bayes master bound (Donsker–Varadhan is load-bearing here)

This is the genuine PAC-Bayes argument, where the change of measure from the prior
`π` to the posterior `ρ` — paying `KL(ρ‖π)` — is exactly the Donsker–Varadhan step
(`integral_le_klDiv_add_log_integral_exp`). Unlike a fixed-hypothesis concentration
bound, DV is essential here: the posterior `ρ` is integrated against a
parameter-dependent functional `F_S(θ)`, and DV is what lets the bound, proved for
the prior, transfer to *any* posterior.

`F ω θ` is the (data-`ω`-dependent) parameter functional, e.g.
`λ·(R θ − r θ S) − λ²C²/(2n)` in the supervised-learning instantiation. The
exp-moment hypothesis `𝔼_ω[∫_θ exp(F ω θ) dπ] ≤ 1` is what a Hoeffding bound,
integrated over the prior and Fubini-swapped, supplies.

Proof completed by Claude (Opus 4.8, 1M context). -/
section PACBayes

open InformationTheory

/-- A sample average of a `[-C,C]`-bounded function stays in `[-C,C]`.
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma abs_avg_le {𝒳 : Type*} {n : ℕ} (s : Fin n → 𝒳) {g : 𝒳 → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, g x ∈ Set.Icc (-C) C) :
    |(1 / (n:ℝ)) * ∑ i : Fin n, g (s i)| ≤ C := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [hC]
  · have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hsum : |∑ i : Fin n, g (s i)| ≤ (n:ℝ) * C :=
      calc |∑ i : Fin n, g (s i)| ≤ ∑ i : Fin n, |g (s i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum (fun i _ => abs_le.mpr (Set.mem_Icc.mp (hb (s i))))
        _ = (n:ℝ) * C := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / n), div_mul_eq_mul_div, one_mul,
      div_le_iff₀ hnR]
    calc |∑ i : Fin n, g (s i)| ≤ (n:ℝ) * C := hsum
      _ = C * n := by ring

/-- The expectation of a `[-C,C]`-bounded measurable function stays in `[-C,C]`.
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma abs_integral_le {𝒳 : Type*} [MeasurableSpace 𝒳] (D : Measure 𝒳) [IsProbabilityMeasure D]
    {g : 𝒳 → ℝ} {C : ℝ} (hg : Measurable g) (hb : ∀ x, g x ∈ Set.Icc (-C) C) :
    |∫ x, g x ∂D| ≤ C := by
  have hint : Integrable g D :=
    Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_le.mpr (Set.mem_Icc.mp (hb x)))
  rw [abs_le]
  exact ⟨by simpa using integral_mono (integrable_const (-C)) hint (fun x => (hb x).1),
    by simpa using integral_mono hint (integrable_const C) (fun x => (hb x).2)⟩

/-- Per-parameter Hoeffding mgf bound, in the `R(θ) − r(θ,S)` orientation used by
PAC-Bayes (apply `hoeffding_iid_mgf_le` at `t = -lam`). For a fixed bounded
measurable loss `g`, sampling `S ∼ Dⁿ`,

    𝔼_S exp( lam·(𝔼_D[g] − (1/n)Σᵢ g(Sᵢ)) ) ≤ exp( lam²C²/(2n) ).

This is what discharges the exp-moment hypothesis of `pacBayes_of_expMoment` once
integrated over the prior and Fubini-swapped.
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma hoeffding_param {𝒳 : Type*} [MeasurableSpace 𝒳] {n : ℕ} (hn : n ≠ 0)
    (D : Measure 𝒳) [IsProbabilityMeasure D] {g : 𝒳 → ℝ} {C lam : ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Set.Icc (-C) C) :
    (∫ S, Real.exp (lam * ((∫ x, g x ∂D) - (1 / (n:ℝ)) * ∑ i : Fin n, g (S i)))
        ∂(Measure.pi fun _ : Fin n => D))
      ≤ Real.exp (lam ^ 2 * C ^ 2 / (2 * (n:ℝ))) := by
  have h := hoeffding_iid_mgf_le (n := n) hn (μ := D) hg (C := C) hb (-lam)
  calc (∫ S, Real.exp (lam * ((∫ x, g x ∂D) - (1 / (n:ℝ)) * ∑ i : Fin n, g (S i)))
            ∂(Measure.pi fun _ : Fin n => D))
      = ∫ S, Real.exp ((-lam) * ((1 / (n:ℝ)) * ∑ i : Fin n, g (S i) - ∫ x, g x ∂D))
            ∂(Measure.pi fun _ : Fin n => D) :=
        integral_congr_ae (ae_of_all _ fun S => by ring_nf)
    _ ≤ Real.exp ((-lam) ^ 2 * C ^ 2 / (2 * (n:ℝ))) := h
    _ = Real.exp (lam ^ 2 * C ^ 2 / (2 * (n:ℝ))) := by rw [neg_pow]; ring_nf

/-- **PAC-Bayes master bound.** With prior `π` and posterior `ρ ≪ π` on a parameter
space `Θ`, sampling measure `μ` on `Ω`, and a measurable functional `F : Ω → Θ → ℝ`:
if the prior exp-moment is controlled, `𝔼_ω[∫_θ exp(F ω θ) dπ] ≤ 1`, then with
probability `≥ 1 − δ` over `ω ∼ μ`,

    ∫_θ F ω θ dρ  ≤  KL(ρ‖π) + log(1/δ).

The single inequality `∫_θ F ω θ dρ ≤ KL(ρ‖π) + log(∫_θ exp(F ω θ) dπ)` is
Donsker–Varadhan; Markov on `ω ↦ ∫_θ exp(F ω θ) dπ` supplies the tail. -/
theorem pacBayes_of_expMoment
    {Θ : Type*} [MeasurableSpace Θ] {Ω : Type*} [MeasurableSpace Ω]
    (π ρ : Measure Θ) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → Θ → ℝ) {δ : ℝ}
    (hρπ : ρ ≪ π) (hllr : Integrable (llr ρ π) ρ)
    (hF_int_ρ : ∀ ω, Integrable (fun θ => F ω θ) ρ)
    (hexpF_int_π : ∀ ω, Integrable (fun θ => Real.exp (F ω θ)) π)
    (Ymeas : Measurable (fun ω => ∫ θ, Real.exp (F ω θ) ∂π))
    (Yint : Integrable (fun ω => ∫ θ, Real.exp (F ω θ) ∂π) μ)
    (hmoment : (∫ ω, (∫ θ, Real.exp (F ω θ) ∂π) ∂μ) ≤ 1)
    (hδ : 0 < δ) :
    μ { ω | (∫ θ, F ω θ ∂ρ) ≤ (klDiv ρ π).toReal + Real.log (1 / δ) }
      ≥ ENNReal.ofReal (1 - δ) := by
  set Y : Ω → ℝ := fun ω => ∫ θ, Real.exp (F ω θ) ∂π with hYdef
  have hYpos : ∀ ω, 0 < Y ω := fun ω => integral_exp_pos (hexpF_int_π ω)
  have ha : (0:ℝ) < 1 / δ := by positivity
  set bad : Set Ω := { ω | (1:ℝ) / δ ≤ Y ω } with hbaddef
  have hbadmeas : MeasurableSet bad := measurableSet_le measurable_const Ymeas
  -- Markov: the bad set has measure ≤ δ.
  have hMarkov : μ bad ≤ ENNReal.ofReal ((∫ ω, Y ω ∂μ) / (1 / δ)) :=
    markov_exp μ (ae_of_all _ fun ω => (hYpos ω).le) Yint ha
  have hbadδ : μ bad ≤ ENNReal.ofReal δ := by
    refine hMarkov.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ ha, mul_one_div, div_self hδ.ne']
    exact hmoment
  -- Complement of the bad set has measure ≥ 1 − δ.
  have hcompl : ENNReal.ofReal (1 - δ) ≤ μ badᶜ := by
    rw [measure_compl hbadmeas (measure_ne_top μ bad), measure_univ,
      ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hbadδ 1
  -- On the complement, Donsker–Varadhan gives the bound.
  have hsub : badᶜ ⊆ { ω | (∫ θ, F ω θ ∂ρ) ≤ (klDiv ρ π).toReal + Real.log (1 / δ) } := by
    intro ω hω
    simp only [hbaddef, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    have hDV := integral_le_klDiv_add_log_integral_exp (μ := ρ) (ν := π)
      hρπ (hF_int_ρ ω) hllr (hexpF_int_π ω)
    have hlog : Real.log (Y ω) ≤ Real.log (1 / δ) := Real.log_le_log (hYpos ω) hω.le
    exact hDV.trans (by linarith)
  exact le_trans hcompl (measure_mono hsub)

/-- **PAC-Bayes generalization bound (supervised, end-to-end).** Prior `π` and
posterior `ρ ≪ π` on parameters `Θ`, bounded measurable loss `ℓ : Θ → 𝒳 → ℝ` with
`ℓ θ x ∈ [-C,C]`, i.i.d. sample `S ∼ Dⁿ`. For `lam > 0`, `δ > 0`, with probability
`≥ 1 − δ`:

    𝔼_{θ~ρ} 𝔼_{x~D}[ℓ θ x] ≤ 𝔼_{θ~ρ}[(1/n) Σᵢ ℓ θ (Sᵢ)]
        + (KL(ρ‖π) + log(1/δ))/lam + lam·C²/(2n).

Donsker–Varadhan (`pacBayes_of_expMoment`) is the load-bearing step; the prior
exp-moment is supplied by `hoeffding_param` integrated over `π` and Fubini-swapped.
Proof completed by Claude (Opus 4.8, 1M context). -/
theorem pacBayes_supervised
    {Θ : Type*} [MeasurableSpace Θ] {𝒳 : Type*} [MeasurableSpace 𝒳]
    {n : ℕ} (hn : n ≠ 0)
    (π ρ : Measure Θ) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (D : Measure 𝒳) [IsProbabilityMeasure D]
    (ℓ : Θ → 𝒳 → ℝ) {C lam δ : ℝ}
    (hℓ : Measurable (Function.uncurry ℓ))
    (hb : ∀ θ x, ℓ θ x ∈ Set.Icc (-C) C) (hC : 0 ≤ C) (hlam : 0 < lam)
    (hρπ : ρ ≪ π) (hllr : Integrable (llr ρ π) ρ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => D)
      { S | (∫ θ, (∫ x, ℓ θ x ∂D) ∂ρ)
              ≤ (∫ θ, (1 / (n:ℝ)) * ∑ i : Fin n, ℓ θ (S i) ∂ρ)
                + ((klDiv ρ π).toReal + Real.log (1 / δ)) / lam
                + lam * C ^ 2 / (2 * (n:ℝ)) }
      ≥ ENNReal.ofReal (1 - δ) := by
  classical
  set Dn : Measure (Fin n → 𝒳) := Measure.pi (fun _ : Fin n => D) with hDn
  haveI : IsProbabilityMeasure Dn := by rw [hDn]; infer_instance
  set q : ℝ := lam ^ 2 * C ^ 2 / (2 * (n:ℝ)) with hq
  set F : (Fin n → 𝒳) → Θ → ℝ :=
    fun S θ => lam * ((∫ x, ℓ θ x ∂D) - (1 / (n:ℝ)) * ∑ i : Fin n, ℓ θ (S i)) - q with hF
  set G : (Fin n → 𝒳) → Θ → ℝ :=
    fun S θ => Real.exp (lam * ((∫ x, ℓ θ x ∂D) - (1 / (n:ℝ)) * ∑ i : Fin n, ℓ θ (S i))) with hG
  -- Measurability.
  have hℓθ : ∀ θ, Measurable (ℓ θ) := fun θ => hℓ.comp (measurable_const.prodMk measurable_id)
  have hRmeas : Measurable (fun θ => ∫ x, ℓ θ x ∂D) :=
    (hℓ.stronglyMeasurable.integral_prod_right').measurable
  have havgjoint : Measurable (fun p : (Fin n → 𝒳) × Θ => (1 / (n:ℝ)) * ∑ i, ℓ p.2 (p.1 i)) :=
    measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
      hℓ.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))))
  have hbase : Measurable (fun p : (Fin n → 𝒳) × Θ =>
      lam * ((∫ x, ℓ p.2 x ∂D) - (1 / (n:ℝ)) * ∑ i, ℓ p.2 (p.1 i))) :=
    measurable_const.mul ((hRmeas.comp measurable_snd).sub havgjoint)
  have hFjoint : Measurable (fun p : (Fin n → 𝒳) × Θ => F p.1 p.2) := by
    simp only [hF]; exact hbase.sub measurable_const
  have hGjoint : Measurable (Function.uncurry G) := by
    exact Real.measurable_exp.comp hbase
  -- Pointwise bounds.
  have hRbd : ∀ θ, |∫ x, ℓ θ x ∂D| ≤ C := fun θ => abs_integral_le D (hℓθ θ) (hb θ)
  have havgbd : ∀ (S : Fin n → 𝒳) (θ : Θ), |(1 / (n:ℝ)) * ∑ i : Fin n, ℓ θ (S i)| ≤ C :=
    fun S θ => abs_avg_le S hC (hb θ)
  have hq0 : (0:ℝ) ≤ q := by rw [hq]; positivity
  have hbasele : ∀ (S : Fin n → 𝒳) (θ : Θ),
      lam * ((∫ x, ℓ θ x ∂D) - (1 / (n:ℝ)) * ∑ i, ℓ θ (S i)) ≤ lam * (2 * C) := by
    intro S θ
    have hR := abs_le.mp (hRbd θ); have hav := abs_le.mp (havgbd S θ)
    nlinarith [hR.1, hR.2, hav.1, hav.2, hlam.le]
  have hFabs : ∀ (S : Fin n → 𝒳) (θ : Θ), |F S θ| ≤ lam * (2 * C) + q := by
    intro S θ
    have hR := abs_le.mp (hRbd θ); have hav := abs_le.mp (havgbd S θ)
    rw [hF, abs_le]; constructor <;> nlinarith [hR.1, hR.2, hav.1, hav.2, hlam.le, hq0]
  have hGbd : ∀ (S : Fin n → 𝒳) (θ : Θ), |G S θ| ≤ Real.exp (lam * (2 * C)) := fun S θ => by
    rw [hG, abs_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_exp.mpr (hbasele S θ)
  -- Integrability of the slices and parametric integrals (bounded measurable on finite measures).
  have hF_int_ρ : ∀ S, Integrable (fun θ => F S θ) ρ := fun S =>
    Integrable.of_bound ((hFjoint.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (lam * (2 * C) + q) (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hFabs S θ)
  have hexpF_int_π : ∀ S, Integrable (fun θ => Real.exp (F S θ)) π := fun S =>
    Integrable.of_bound
      ((Real.measurable_exp.comp (hFjoint.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
      (Real.exp (lam * (2 * C) + q)) (ae_of_all _ fun θ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hFabs S θ)))
  have Ymeas : Measurable (fun S => ∫ θ, Real.exp (F S θ) ∂π) :=
    ((Real.measurable_exp.comp hFjoint).stronglyMeasurable.integral_prod_right').measurable
  have Yint : Integrable (fun S => ∫ θ, Real.exp (F S θ) ∂π) Dn :=
    Integrable.of_bound Ymeas.aestronglyMeasurable (Real.exp (lam * (2 * C) + q))
      (ae_of_all _ fun S => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => (Real.exp_pos _).le)]
        refine (integral_mono (hexpF_int_π S) (integrable_const _)
          (fun θ => Real.exp_le_exp.mpr ((le_abs_self _).trans (hFabs S θ)))).trans ?_
        simp)
  -- Exp-moment bound via Fubini + per-parameter Hoeffding.
  have hGslice : ∀ θ, Integrable (fun S => G S θ) Dn := fun θ =>
    Integrable.of_bound ((hGjoint.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (Real.exp (lam * (2 * C))) (ae_of_all _ fun S => by rw [Real.norm_eq_abs]; exact hGbd S θ)
  have hGint : Integrable (Function.uncurry G) (Dn.prod π) :=
    Integrable.of_bound hGjoint.aestronglyMeasurable (Real.exp (lam * (2 * C)))
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hGbd p.1 p.2)
  have hinnerle : ∀ θ, (∫ S, G S θ ∂Dn) ≤ Real.exp q := fun θ => by
    rw [hq]; exact hoeffding_param hn D (hℓθ θ) (hb θ)
  have hinnerint : Integrable (fun θ => ∫ S, G S θ ∂Dn) π :=
    Integrable.of_bound (hGjoint.stronglyMeasurable.integral_prod_left').measurable.aestronglyMeasurable
      (Real.exp (lam * (2 * C))) (ae_of_all _ fun θ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun S => (Real.exp_pos _).le)]
        refine (integral_mono (hGslice θ) (integrable_const _)
          (fun S => le_of_abs_le (hGbd S θ))).trans ?_
        simp)
  have hmoment : (∫ S, (∫ θ, Real.exp (F S θ) ∂π) ∂Dn) ≤ 1 := by
    have hpull : (fun S => ∫ θ, Real.exp (F S θ) ∂π)
        = fun S => Real.exp (-q) * ∫ θ, G S θ ∂π := by
      funext S; rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun θ => ?_)
      simp only [hF, hG]; rw [← Real.exp_add]; congr 1; ring
    calc (∫ S, (∫ θ, Real.exp (F S θ) ∂π) ∂Dn)
        = ∫ S, Real.exp (-q) * (∫ θ, G S θ ∂π) ∂Dn := by rw [hpull]
      _ = Real.exp (-q) * ∫ θ, (∫ S, G S θ ∂Dn) ∂π := by
          rw [integral_const_mul, integral_integral_swap hGint]
      _ ≤ Real.exp (-q) * ∫ _θ, Real.exp q ∂π :=
          mul_le_mul_of_nonneg_left (integral_mono hinnerint (integrable_const _) hinnerle)
            (Real.exp_pos _).le
      _ = 1 := by rw [integral_const]; simp [← Real.exp_add]
  -- Apply the master lemma and rewrite the event.
  have hmaster := pacBayes_of_expMoment π ρ Dn F hρπ hllr hF_int_ρ hexpF_int_π Ymeas Yint hmoment hδ
  refine le_trans hmaster (measure_mono ?_)
  intro S hS
  simp only [Set.mem_setOf_eq] at hS ⊢
  have hRint : Integrable (fun θ => ∫ x, ℓ θ x ∂D) ρ :=
    Integrable.of_bound hRmeas.aestronglyMeasurable C
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hRbd θ)
  have havgint : Integrable (fun θ => (1 / (n:ℝ)) * ∑ i, ℓ θ (S i)) ρ :=
    Integrable.of_bound (havgjoint.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact havgbd S θ)
  have hcq : (∫ _θ : Θ, q ∂ρ) = q := by simp
  have hFρ : (∫ θ, F S θ ∂ρ)
      = lam * ((∫ θ, (∫ x, ℓ θ x ∂D) ∂ρ) - ∫ θ, (1 / (n:ℝ)) * ∑ i, ℓ θ (S i) ∂ρ) - q := by
    have hsub : Integrable (fun θ => (∫ x, ℓ θ x ∂D) - (1 / (n:ℝ)) * ∑ i, ℓ θ (S i)) ρ :=
      hRint.sub havgint
    calc (∫ θ, F S θ ∂ρ)
        = ∫ θ, (lam * ((∫ x, ℓ θ x ∂D) - (1 / (n:ℝ)) * ∑ i, ℓ θ (S i)) - q) ∂ρ := by
            simp only [hF]
      _ = (∫ θ, lam * ((∫ x, ℓ θ x ∂D) - (1 / (n:ℝ)) * ∑ i, ℓ θ (S i)) ∂ρ) - q := by
            rw [integral_sub (hsub.const_mul lam) (integrable_const q), hcq]
      _ = lam * ((∫ θ, (∫ x, ℓ θ x ∂D) ∂ρ) - ∫ θ, (1 / (n:ℝ)) * ∑ i, ℓ θ (S i) ∂ρ) - q := by
            rw [integral_const_mul, integral_sub hRint havgint]
  have key : lam * ((∫ θ, (∫ x, ℓ θ x ∂D) ∂ρ) - ∫ θ, (1 / (n:ℝ)) * ∑ i, ℓ θ (S i) ∂ρ)
      ≤ ((klDiv ρ π).toReal + Real.log (1 / δ)) + q := by rw [hFρ] at hS; linarith
  have hcombine : (∫ θ, (1 / (n:ℝ)) * ∑ i, ℓ θ (S i) ∂ρ)
        + ((klDiv ρ π).toReal + Real.log (1 / δ)) / lam + lam * C ^ 2 / (2 * (n:ℝ))
      = (∫ θ, (1 / (n:ℝ)) * ∑ i, ℓ θ (S i) ∂ρ)
        + (((klDiv ρ π).toReal + Real.log (1 / δ)) + q) / lam := by
    rw [hq]; field_simp; ring
  rw [hcombine, ← sub_le_iff_le_add', le_div_iff₀ hlam]
  nlinarith [key]

end PACBayes

end DRSB.WellKnown
