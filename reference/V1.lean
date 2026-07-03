/-
TwoPagerPACBayesScaffold.lean

Goal: a clean, paper-faithful scaffold for TwoPager.pdf Theorem 4
(PAC-Bayes generalization bound for the *clipped* terminal-cost network g_ϑ).

Paper statement (Eq. (116)/(126)):
  Let Q be a reference path measure on trajectories (X_t)_{t∈[0,1]}
  and P any controlled path measure with terminal marginal P₁.
  Draw i.i.d. sample S = {X₁^(i)}_{i=1}^n from P₁.
  If g_ϑ is clipped to [-C,C], then for ε>0 and ς∈(0,1),
  with probability ≥ 1-ς:
    E_{X₁~P₁}[g_ϑ(X₁)] ≤ (1/n)∑ g_ϑ(X₁^(i))
                         + ( KL(P‖Q) + log(1/ς) ) / ε
                         + ε C^2 / (2n).

Paper proof steps (Eq. (117)–(126)):
  (117) Define lᵢ, population risk R, empirical risk r.
  (118) Hoeffding mgf bound for bounded lᵢ.
  (119) Integrate w.r.t. Q (sets up DV change-of-measure).
  (120) Fubini + set t = ε/n.
  (121) Apply Donsker–Varadhan (Lemma 5) to introduce KL(P‖Q) under a sup.
  (122) Rearranged exponential-moment inequality ≤ 1.
  (123)-(125) Chernoff bound to get a tail probability ≤ ς.
  (126) Algebraic rearrangement gives final event; complement has prob ≥ 1-ς.
-/

import Mathlib
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace TwoPagerPACBayes

set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
## KL setup (Option 1, paper-faithful)

The TwoPager Theorem 4 uses `KL(P‖Q)` where `P` is a controlled *path measure*
and `Q` is a reference path measure. The bound then samples i.i.d. from the
terminal marginal `P₁`.

In the paper, `KL(P‖Q)` is treated as a real number. In Mathlib, the canonical
Kullback–Leibler divergence is *extended-valued*:

* `InformationTheory.klDiv P Q : ℝ≥0∞` (i.e. `ENNReal`), which may be `⊤`.

To match the paper’s algebra while remaining measure-theoretically honest, we:

1. define `KLinf := InformationTheory.klDiv` as the *true* KL object;
2. define `KLReal := (KLinf ...).toReal` as the real quantity appearing in Eq. (116);
3. whenever we use `KLReal` as a KL term, we carry a finiteness hypothesis
   `KLFinite : KLinf ≠ ⊤`.

This makes the paper’s implicit “KL is finite when used” assumption explicit,
and avoids the pitfall `ENNReal.toReal ⊤ = 0`.
-/

section KL

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Extended-valued KL divergence (`ℝ≥0∞`), i.e. Mathlib’s canonical KL. -/
noncomputable abbrev KLinf (P Q : Measure Ω) : ℝ≥0∞ :=
  InformationTheory.klDiv P Q

/-- Real-valued KL divergence used in the paper, obtained via `toReal`. -/
noncomputable abbrev KLReal (P Q : Measure Ω) : ℝ :=
  (KLinf (Ω := Ω) P Q).toReal

/-- “KL is finite” means the extended KL is not top. -/
def KLFinite (P Q : Measure Ω) : Prop :=
  KLinf (Ω := Ω) P Q ≠ ⊤

/-- Under finiteness, `ENNReal.ofReal (KLReal P Q) = KLinf P Q`. -/
lemma ofReal_KLReal (P Q : Measure Ω) (h : KLFinite (Ω := Ω) P Q) :
    ENNReal.ofReal (KLReal (Ω := Ω) P Q) = KLinf (Ω := Ω) P Q := by
  simpa [KLReal, KLFinite, KLinf] using ENNReal.ofReal_toReal h

/-!
### Log-likelihood ratio

For later DV/KL development, Mathlib’s log-likelihood ratio is
`MeasureTheory.llr P Q : Ω → ℝ`.
-/
-- #check MeasureTheory.llr

end KL


variable {X : Type*} [MeasurableSpace X]

/-!
## 1. Core objects from the paper
-/

/-- Terminal marginal of a trajectory measure via a measurable terminal map `X1`. -/
noncomputable def terminalMarginal {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (X1 : Ω → X) (μ : Measure Ω) : Measure X :=
  Measure.map X1 μ

/-- i.i.d. sample measure on `Fin n → X` with marginal `μ` (finite product measure). -/
noncomputable def iidsampleMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (n : ℕ) : Measure (Fin n → X) :=
  Measure.pi (fun _ : Fin n => μ)

/-- Empirical mean of `g` over a sample `s : Fin n → X`. -/
noncomputable def empMean {X : Type*} [MeasurableSpace X]
    (n : ℕ) (g : X → ℝ) (s : Fin n → X) : ℝ :=
  (1 / (n : ℝ)) * (∑ i : Fin n, g (s i))

/-- Population mean of `g` under `μ`. -/
noncomputable def popMean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : X → ℝ) : ℝ :=
  ∫ x, g x ∂ μ

/-!
## 2. Clipping (Eq. (115))
-/

/-- Real-valued clipping to the interval `[-C, C]`. -/
noncomputable def clip (C : ℝ) (y : ℝ) : ℝ :=
  max (-C) (min C y)

/-- Clipped terminal-cost network: `g = clip C ∘ gTilde`. -/
noncomputable def clipped (C : ℝ) {X : Type*} (gTilde : X → ℝ) : X → ℝ :=
  fun x => clip C (gTilde x)

/-- Basic property: clipping enforces `|clip C y| ≤ C` when `0 ≤ C`. -/
theorem abs_clip_le (C y : ℝ) (hC : 0 ≤ C) : |clip C y| ≤ C := by
  unfold clip
  -- show: -C ≤ max(-C, min C y) ≤ C
  refine (abs_le).2 ?_
  constructor
  · exact le_max_left _ _
  · -- `max a b ≤ C` if `a ≤ C` and `b ≤ C`
    apply max_le
    · linarith
    · exact min_le_left _ _

/-- Therefore, the clipped network is bounded by `C` pointwise. -/
theorem abs_clipped_le {X : Type*} (gTilde : X → ℝ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ x, |clipped C gTilde x| ≤ C := by
  intro x
  simpa [clipped] using abs_clip_le (C := C) (y := gTilde x) hC


/--
If `|y| ≤ C` (and hence `-C ≤ y ≤ C`), then clipping does not change `y`.

This is useful when we want to reuse the "clipped" theorem in a situation where the loss
is already known to be bounded by `C`.
-/
theorem clip_eq_self_of_abs_le (C y : ℝ) (hC : 0 ≤ C) (hy : |y| ≤ C) :
    clip C y = y := by
  unfold clip
  have hy' : (-C ≤ y) ∧ (y ≤ C) := (abs_le).1 hy
  have hmin : min C y = y := by
    -- `y ≤ C` implies `min y C = y`, hence also `min C y = y`.
    have : min y C = y := min_eq_left hy'.2
    simpa [min_comm] using this
  -- `-C ≤ y` implies `max (-C) y = y`
  have hmax : max (-C) y = y := by
    simpa using (max_eq_right hy'.1)
  simpa [hmin, hmax]

/--
If a function is pointwise bounded by `C`, then clipping at `C` leaves it unchanged.
-/
theorem clipped_eq_self_of_abs_le {X : Type*} (g : X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg_bd : ∀ x, |g x| ≤ C) :
    clipped C g = g := by
  funext x
  simpa [clipped] using clip_eq_self_of_abs_le (C := C) (y := g x) hC (hg_bd x)

/-- Measurability of clipping and the clipped network (needed for integrals). -/
theorem measurable_clipped {X : Type*} [MeasurableSpace X]
    (gTilde : X → ℝ) (C : ℝ) (hg : Measurable gTilde) :
    Measurable (clipped C gTilde) := by
  -- `clip C` is built from `min`/`max` with constants.
  have hmin : Measurable (fun x : X => min C (gTilde x)) :=
    (measurable_const.min hg)
  have hmax : Measurable (fun x : X => max (-C) (min C (gTilde x))) :=
    (measurable_const.max hmin)
  simpa [clipped, clip] using hmax

/-!
## 3. Probability-measure instances we will repeatedly need
-/

/-- If `μ` is a probability measure, its i.i.d. product on `Fin n` is too. -/
noncomputable instance iidsampleMeasure.instIsProbabilityMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (iidsampleMeasure μ n) := by
  classical
  refine ⟨by simp [iidsampleMeasure]⟩

/-- If `P` is a probability measure and `X1` is measurable, then its terminal marginal is too. -/
theorem terminalMarginal_isProbability
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (X1 : Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX1 : Measurable X1) -- the terminal-time evaluation map is measurable.
    :
    IsProbabilityMeasure (terminalMarginal X1 P) := by
  classical
  refine ⟨by
    -- `(P.map X1) univ = P (X1 ⁻¹' univ) = P univ = 1`
    simp [terminalMarginal, Measure.map_apply, hX1]⟩

/-!
## 4. Lemma 3 (Hoeffding mgf) specialized to the paper’s variables (Eq. (118))
-/

/-- (Eq. 117) Paper’s definitions, packaged for a fixed terminal marginal `P1`. -/
noncomputable def R_of (P1 : Measure X) (g : X → ℝ) : ℝ := popMean P1 g

noncomputable def r_of (n : ℕ) (g : X → ℝ) (s : Fin n → X) : ℝ := empMean n g s

/-- The centered version of `g`. -/
noncomputable def centered_g {X : Type*} [MeasurableSpace X] (P1 : Measure X) (g : X → ℝ) : X → ℝ :=
  fun x => g x - R_of P1 g

/-- `centered_g` has mean 0. -/
lemma centered_g_mean_zero {X : Type*} [MeasurableSpace X]
    (P1 : Measure X) [IsProbabilityMeasure P1]
    (g : X → ℝ) (hg_int : Integrable g P1) :
    ∫ x, centered_g P1 g x ∂P1 = 0 := by
  simp [centered_g, R_of, popMean]
  rw [integral_sub hg_int (integrable_const _)]
  simp

/-- `centered_g` is bounded in an interval of length `2C`. -/
lemma centered_g_bounds {X : Type*} [MeasurableSpace X]
    (P1 : Measure X) [IsProbabilityMeasure P1]
    (g : X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg_bd : ∀ x, |g x| ≤ C) :
    ∀ x, centered_g P1 g x ∈ Set.Icc (-C - R_of P1 g) (C - R_of P1 g) := by
  intro x
  simp [centered_g]
  have := abs_le.1 (hg_bd x)
  constructor <;> linarith

/-- `centered_g` is sub-Gaussian with parameter `C^2`. -/
lemma centered_g_subgaussian {X : Type*} [MeasurableSpace X]
    (P1 : Measure X) [IsProbabilityMeasure P1]
    (g : X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∀ x, |g x| ≤ C) :
    ProbabilityTheory.HasSubgaussianMGF (centered_g P1 g) (Real.toNNReal (C^2)) P1 := by
  have h_centered_g_bounds : ∀ x, -C - R_of P1 g ≤ centered_g P1 g x ∧ centered_g P1 g x ≤ C - R_of P1 g := by
    exact fun x => ⟨ by linarith [ abs_le.mp ( hg_bd x ), show centered_g P1 g x = g x - R_of P1 g from rfl ], by linarith [ abs_le.mp ( hg_bd x ), show centered_g P1 g x = g x - R_of P1 g from rfl ] ⟩;
  have := @ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero;
  convert this _ _ _ using 1;
  any_goals exact MeasureTheory.ae_of_all _ fun x => h_centered_g_bounds x;
  · norm_num [ ← NNReal.coe_inj, hC ] ; ring_nf;
    norm_num [ abs_mul, mul_pow, hC ] ; ring;
  · infer_instance;
  · exact ( hg_meas.aemeasurable.sub_const _ );
  · apply_rules [ centered_g_mean_zero ];
    refine' MeasureTheory.Integrable.mono' _ _ _;
    exacts [ fun _ => C, MeasureTheory.integrable_const _, hg_meas.aestronglyMeasurable, Filter.Eventually.of_forall hg_bd ]

lemma hoeffding_exponent_rewrite
    {X : Type*} [MeasurableSpace X]
    (P1 : Measure X) (g : X → ℝ) (n : ℕ) (t : ℝ) (s : Fin n → X) (hn : n ≠ 0) :
    t * (n : ℝ) * (R_of P1 g - r_of n g s) = ∑ i : Fin n, -t * centered_g P1 g (s i) := by
      -- By definition of $centered_g$, we can rewrite the sum as $\sum_{i=1}^n -t * (g(s_i) - R(P1, g))$.
      have h_sum_rewrite : ∑ i : Fin n, -t * centered_g P1 g (s i) = -t * (∑ i : Fin n, g (s i) - n * R_of P1 g) := by
        simp +decide [centered_g];
        simp +decide [mul_sub, Finset.mul_sum _ _ _];
        ring;
      -- Substitute the definition of $r_of$ into the right-hand side.
      have h_r_of : r_of n g s = (1 / n : ℝ) * ∑ i : Fin n, g (s i) := by
        rfl;
      simp_all +decide [ mul_assoc, mul_sub ];
      ring

lemma integral_exp_sum_eq_prod_integral {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (n : ℕ) (f : Fin n → X → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hf_int : ∀ i, Integrable (fun x => Real.exp (f i x)) P) :
    ∫ s : Fin n → X, Real.exp (∑ i : Fin n, f i (s i)) ∂(iidsampleMeasure P n) =
    ∏ i : Fin n, ∫ x, Real.exp (f i x) ∂P := by
  rw [iidsampleMeasure]
  conv in (Real.exp _) => rw [Real.exp_sum]
  rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ]

/-- (Lemma 3 / Eq. 118) Hoeffding mgf bound for bounded `g` on i.i.d. sample from `P1`. -/
theorem hoeffding_mgf_bound
    {X : Type*} [MeasurableSpace X]
    (P1 : Measure X) [IsProbabilityMeasure P1]
    (g : X → ℝ) (C t : ℝ) (n : ℕ)
    (hn : 0 < n) (hC : 0 ≤ C) (ht : 0 < t)
    (hg_meas : Measurable g) (hg_bd : ∀ x, |g x| ≤ C) :
    (∫ s, Real.exp (t * (n : ℝ) * (R_of (X:=X) P1 g - r_of (X:=X) n g s))
      ∂ (iidsampleMeasure P1 n))
      ≤ Real.exp ((n : ℝ) * t^2 * C^2 / 2) := by
        /-
        Proof sketch:
        * View the sample `s : Fin n → X` as i.i.d. under the product measure `Measure.pi (fun _ => P1)`.
        * Define centered variables `Y_i(s) := g (s i) - E_{x~P1}[g x]`. Then `E[Y_i]=0` and `|Y_i| ≤ 2C`.
        * Apply Hoeffding's lemma (a.k.a. the bounded-subGaussian mgf bound):
            E[exp(t * Y_i)] ≤ exp(t^2 * (2C)^2 / 8) = exp(t^2 * C^2 / 2).
          In Mathlib this should follow from `Mathlib.Probability.Moments.SubGaussian`:
          show each `Y_i` is subGaussian with parameter `C`, then use mgf bounds.
        * Use independence of the coordinates under the product measure to factor the mgf of the sum:
            E[exp(t * ∑ Y_i)] = ∏ E[exp(t * Y_i)].
        * Rewrite the sum of `Y_i` in terms of `R_of P1 g - r_of n g s`, and simplify.
        -/
        -- By Hoeffding's lemma, we have $\int_{X} \exp(-t \cdot (g(x) - R(P_1, g))) \, dP_1 \leq \exp(t^2 C^2 / 2)$.
        have h_hoeffding_lemma : ∀ t : ℝ, 0 < t → ∫ x, Real.exp (-t * centered_g P1 g x) ∂P1 ≤ Real.exp (t ^ 2 * C ^ 2 / 2) := by
          intro t ht;
          -- Since `centered_g P1 g` is sub-Gaussian with parameter `C^2`, we have
          have h_subgaussian : ProbabilityTheory.HasSubgaussianMGF (centered_g P1 g) (Real.toNNReal (C^2)) P1 := by
            apply_rules [ centered_g_subgaussian ];
          have := h_subgaussian.mgf_le ( -t );
          simp_all +decide [ mul_comm, ProbabilityTheory.mgf ];
        -- By Fubini's theorem, we can interchange the order of integration.
        have h_fubini : ∫ s : Fin n → X, Real.exp (∑ i : Fin n, -t * centered_g P1 g (s i)) ∂(iidsampleMeasure P1 n) =
                        ∏ i : Fin n, (∫ x, Real.exp (-t * centered_g P1 g x) ∂P1) := by
                          convert integral_exp_sum_eq_prod_integral P1 n ( fun i x => -t * centered_g P1 g x ) _ _ using 1;
                          · exact fun i => measurable_const.mul ( hg_meas.sub ( measurable_const ) );
                          · intro i;
                            refine' MeasureTheory.Integrable.mono' _ _ _;
                            refine' fun x => Real.exp ( t * ( C + |R_of P1 g| ) );
                            · exact MeasureTheory.integrable_const _;
                            · refine' Measurable.aestronglyMeasurable _;
                              exact Measurable.exp ( measurable_const.mul ( hg_meas.sub measurable_const ) );
                            · simp +decide [ centered_g ];
                              filter_upwards [ ] with x using by cases abs_cases ( R_of P1 g ) <;> nlinarith [ abs_le.mp ( hg_bd x ) ] ;
        convert h_fubini.le.trans ( Finset.prod_le_prod ( fun _ _ => MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ ) fun _ _ => h_hoeffding_lemma t ht ) using 1;
        · congr! 3;
          convert hoeffding_exponent_rewrite P1 g n t _ _ using 1;
          positivity;
        · rw [ ← Real.exp_sum, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_div_assoc ] ; ring_nf

/-!
## 5. Eq. (119) and Eq. (120): integrating w.r.t. Q and swapping expectations (Fubini)
-/

/-- (Eq. 119) Trivial “integrate w.r.t. Q” wrapper. -/
theorem integrate_over_Q_trivial
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (F : α → ℝ) (μ : Measure α) :
    (∫ ω, (∫ a, F a ∂ μ) ∂ Q) = (∫ a, F a ∂ μ) := by
  simp


theorem fubini_swap_expectations
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (H : Ω → α → ℝ)
    (hH_int : Integrable (Function.uncurry H) (Q.prod μ)) :
    (∫ ω, (∫ a, H ω a ∂ μ) ∂ Q) = (∫ a, (∫ ω, H ω a ∂ Q) ∂ μ) := by
  rw [MeasureTheory.integral_integral_swap hH_int]

/-- (Eq. 120) Swap expectations over `S` and `Q` (Fubini-like) for a jointly measurable integrand. -/
theorem lintegral_swap_expectations
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (H : Ω → α → ENNReal)
    (hH : Measurable (fun p : Ω × α => H p.1 p.2)) :
    (∫⁻ ω, (∫⁻ a, H ω a ∂ μ) ∂ Q) = (∫⁻ a, (∫⁻ ω, H ω a ∂ Q) ∂ μ) := by
  -- Best done either via (a) Tonelli on a nonnegative version of `H` (preferred here,
  have hHae : AEMeasurable (fun p : Ω × α => H p.1 p.2) (Q.prod μ) :=
    hH.aemeasurable
  simpa using (lintegral_lintegral_swap (μ := Q) (ν := μ) hHae)


/-- (Eq. 120) The paper’s “set t = ε/n” rewrite lemma. -/
theorem set_t_eq_eps_over_n (ε : ℝ) (n : ℕ) (hn : 0 < n) :
    (ε / (n : ℝ)) * (n : ℝ) = ε := by
  field_simp [hn.ne']

/-!
## 6. Lemma 5 (Donsker–Varadhan) and the PAC-Bayes exponential-moment inequality (Eq. (121)-(122))
-/

/-
(Lemma 5 / Eq. 121) Donsker–Varadhan inequality in the direction used by PAC-Bayes.

We state it with the paper’s real KL term `KLReal P Q`, and therefore carry the
explicit finiteness hypothesis `KLFinite P Q`.

This is the exact place the paper “pays” for a change-of-measure: `Q`-expectations
become `P`-expectations plus `KL(P‖Q)`.
-/
-- theorem donsker_varadhan_ineq
--     {Ω : Type*} [MeasurableSpace Ω]
--     (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
--     (hKL : KLFinite (Ω := Ω) P Q)
--     (f : Ω → ℝ) (hf : Measurable f) :
--     (∫ ω, f ω ∂ P) - KLReal (Ω := Ω) P Q
--       ≤ Real.log (∫ ω, Real.exp (f ω) ∂ Q) := by
--   /-
--   Proof sketch:
--   * This is the Donsker–Varadhan variational inequality specialized to probability measures.
--   * One standard route in Mathlib is to use the variational characterization of KL:
--       KL(P‖Q) = ∫ llr P Q ∂P   (when `P ≪ Q`) and `⊤` otherwise,
--     together with the convex duality identity
--       log ∫ exp(f) dQ = sup_{P} ( ∫ f dP - KL(P‖Q) ).
--   * From that variational formula, the inequality for a fixed `P` follows by instantiating the supremum.
--   * The finiteness hypothesis `hKL : KLFinite P Q` is used to interpret `KLReal` as a genuine real number
--     (avoiding `toReal ⊤ = 0`).
--   -/

lemma kl_eq_integral_llr
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hAC : P ≪ Q) (hKL : KLFinite P Q) :
    KLReal P Q = ∫ ω, MeasureTheory.llr P Q ω ∂P := by
  -- This relates the KL divergence to the integral of the log-likelihood ratio.
  -- Mathlib has `klDiv_eq_integral_klFun` and `llr` definitions.
  -- We need to connect `klFun (dP/dQ)` integrated against `Q` to `log (dP/dQ)` integrated against `P`.
  -- Apply the theorem that states the KL divergence is equal to the integral of the log-likelihood ratio.
  apply Eq.symm; exact (by
  have h_eq : KLReal P Q = (∫ ω, (MeasureTheory.llr P Q) ω ∂P) := by
    have h_eq : ∀ {μ ν : MeasureTheory.Measure Ω}, MeasureTheory.IsProbabilityMeasure μ → MeasureTheory.IsProbabilityMeasure ν → μ ≪ ν → KLFinite μ ν → KLReal μ ν = (∫ ω, (MeasureTheory.llr μ ν) ω ∂μ) := by
      intros μ ν hμ hν hAC hKL
      have h_eq : KLReal μ ν = (∫ ω, (MeasureTheory.llr μ ν) ω ∂μ) := by
        have h_eq : KLinf μ ν = ENNReal.ofReal (∫ ω, (MeasureTheory.llr μ ν) ω ∂μ) := by
          unfold KLinf;
          rw [ InformationTheory.klDiv ];
          -- Since μ and ν are probability measures, their real parts are both 1. Therefore, the expression simplifies to ENNReal.ofReal (∫ ω, MeasureTheory.llr μ ν ω ∂μ).
          simp [hμ, hν];
          exact InformationTheory.klDiv_ne_top_iff.mp hKL
        convert congr_arg ENNReal.toReal h_eq using 1;
        rw [ ENNReal.toReal_ofReal ];
        contrapose! h_eq;
        -- Since the integral is negative, the KL divergence is positive.
        have h_pos : 0 < KLinf μ ν := by
          apply_rules [ pos_iff_ne_zero.mpr ];
          intro h;
          have h_eq : μ = ν := by
            exact InformationTheory.klDiv_eq_zero_iff.mp h;
          simp_all +decide [ MeasureTheory.llr ];
          rw [ MeasureTheory.integral_eq_zero_of_ae ] at * <;> norm_num at *;
          filter_upwards [ MeasureTheory.Measure.rnDeriv_self ν ] with ω hω using by aesop;
        rw [ ENNReal.ofReal_eq_zero.mpr h_eq.le ] ; aesop;
      exact h_eq
    exact h_eq ‹_› ‹_› hAC hKL;
  exact h_eq.symm)

lemma jensen_ineq_exp
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hg : Integrable g P) (h_exp_int : Integrable (fun ω => Real.exp (g ω)) P) :
    ∫ ω, g ω ∂P ≤ Real.log (∫ ω, Real.exp (g ω) ∂P) := by
  -- Apply Jensen's inequality for the convex function exp.
  -- exp (∫ g ∂P) ≤ ∫ exp g ∂P
  -- Then take log of both sides.
  rw [ Real.le_log_iff_exp_le ];
  · have h_jensen : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
      exact convexOn_exp;
    apply_rules [ h_jensen.map_integral_le ];
    · exact Real.continuousOn_exp;
    · exact isClosed_univ;
    · exact Filter.Eventually.of_forall fun ω => Set.mem_univ _;
  · exact integral_exp_pos h_exp_int


lemma kl_finite_implies_ac {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : KLFinite P Q) : P ≪ Q := by
  unfold KLFinite KLinf at h
  rw [InformationTheory.klDiv_ne_top_iff] at h
  exact h.1

lemma rnDeriv_pos_ae_P
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hAC : P ≪ Q) :
    ∀ᵐ ω ∂P, 0 < (P.rnDeriv Q ω).toReal := by
  -- The Radon-Nikodym derivative is positive almost everywhere with respect to P.
  -- If it were 0 on a set A, then P(A) = ∫_A (dP/dQ) dQ = 0.
  -- Since the Radon-Nikodym derivative is non-negative and P is absolutely continuous with respect to Q, the derivative can't be zero almost everywhere with respect to P.
  have h_deriv_pos : ∀ᵐ ω ∂P, 0 < (MeasureTheory.Measure.rnDeriv P Q ω).toReal := by
    have h_nonneg : ∀ᵐ ω ∂P, 0 ≤ (MeasureTheory.Measure.rnDeriv P Q ω).toReal := by
      exact Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg
    -- Since the integral of the Radon-Nikodym derivative over the entire space is 1, and the derivative is non-negative almost everywhere, the set where the derivative is zero must have measure zero.
    have h_zero_measure : P {ω | (MeasureTheory.Measure.rnDeriv P Q ω).toReal = 0} = 0 := by
      -- Since the integral of the Radon-Nikodym derivative over the set where it's zero must be zero, and the derivative is non-negative almost everywhere, the set where it's zero must have measure zero.
      have h_zero_measure : ∫⁻ ω in {ω | (MeasureTheory.Measure.rnDeriv P Q ω).toReal = 0}, (MeasureTheory.Measure.rnDeriv P Q ω) ∂Q = 0 := by
        rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_zero ];
        rw [ Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' ];
        · filter_upwards [ MeasureTheory.Measure.rnDeriv_lt_top P Q ] with ω hω hω' using by rw [ ENNReal.toReal_eq_zero_iff ] at hω'; aesop;
        · exact measurableSet_eq_fun ( by measurability ) ( by measurability );
      convert h_zero_measure using 1;
      exact Eq.symm (Measure.setLIntegral_rnDeriv hAC {ω | ((∂P/∂Q) ω).toReal = 0});
    filter_upwards [ h_nonneg, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_zero_measure ] with ω hω₁ hω₂ using lt_of_le_of_ne hω₁ ( Ne.symm hω₂ );
  exact h_deriv_pos

lemma integral_exp_sub_llr_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite P Q)
    (f : Ω → ℝ) (hf : Measurable f)
    (h_int_exp : Integrable (fun ω => Real.exp (f ω)) Q) :
    ∫ ω, Real.exp (f ω - MeasureTheory.llr P Q ω) ∂P ≤ ∫ ω, Real.exp (f ω) ∂Q := by
  have hPQ : P ≪ Q := by
    exact kl_finite_implies_ac P Q hKL;
  rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae, MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · -- By definition of $P.rnDeriv Q$, we know that $P.rnDeriv Q ω * ENNReal.ofReal (Real.exp (f ω - MeasureTheory.llr P Q ω)) ≤ ENNReal.ofReal (Real.exp (f ω))$ almost everywhere.
    have h_ineq : ∀ᵐ ω ∂Q, P.rnDeriv Q ω * ENNReal.ofReal (Real.exp (f ω - MeasureTheory.llr P Q ω)) ≤ ENNReal.ofReal (Real.exp (f ω)) := by
      filter_upwards [ MeasureTheory.Measure.rnDeriv_lt_top P Q ] with ω hω;
      by_cases h : ( ∂P/∂Q ) ω = 0 <;> simp_all +decide [ MeasureTheory.llr ];
      rw [ ENNReal.le_ofReal_iff_toReal_le ];
      · rw [ ENNReal.toReal_mul, ENNReal.toReal_ofReal ( Real.exp_nonneg _ ) ];
        rw [ Real.exp_sub, Real.exp_log ( ENNReal.toReal_pos h hω.ne ) ];
        rw [ mul_div_cancel₀ _ ( ne_of_gt ( ENNReal.toReal_pos h hω.ne ) ) ];
      · exact ENNReal.mul_ne_top hω.ne ( ENNReal.ofReal_ne_top );
      · positivity;
    convert ENNReal.toReal_mono _ ( MeasureTheory.lintegral_mono_ae h_ineq ) using 1;
    · rw [ MeasureTheory.lintegral_rnDeriv_mul ];
      · exact hPQ;
      · fun_prop;
    · exact ne_of_lt ( MeasureTheory.Integrable.lintegral_lt_top ( by exact h_int_exp.ofReal ) );
  · exact Filter.Eventually.of_forall fun ω => Real.exp_nonneg _;
  · exact h_int_exp.1;
  · exact Filter.Eventually.of_forall fun ω => Real.exp_nonneg _;
  · fun_prop

lemma integrable_llr_of_kl_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite P Q) :
    MeasureTheory.Integrable (MeasureTheory.llr P Q) P := by
  contrapose! hKL;
  unfold KLFinite
  simp_all only [not_false_eq_true, InformationTheory.klDiv_of_not_integrable, ne_eq,
    not_true_eq_false];

lemma integrable_llr_of_kl_finite_new
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite P Q) :
    MeasureTheory.Integrable (MeasureTheory.llr P Q) P := by
  exact integrable_llr_of_kl_finite P Q hKL

lemma integrable_llr_of_kl_finite'
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite P Q) :
    MeasureTheory.Integrable (MeasureTheory.llr P Q) P := by
  -- We need to show that llr P Q is integrable w.r.t P.
  -- This is equivalent to showing that (dP/dQ) * log(dP/dQ) is integrable w.r.t Q.
  have hAC : P ≪ Q := kl_finite_implies_ac P Q hKL
  apply_rules [ integrable_llr_of_kl_finite ]

lemma integrable_llr_safe
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite P Q) :
    MeasureTheory.Integrable (MeasureTheory.llr P Q) P := by
  -- We need to show that llr P Q is integrable w.r.t P.
  -- This is equivalent to showing that (dP/dQ) * log(dP/dQ) is integrable w.r.t Q.
  have hAC : P ≪ Q := kl_finite_implies_ac P Q hKL
  exact integrable_llr_of_kl_finite' P Q hKL

theorem donsker_varadhan_ineq_more_assumptions
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite (Ω := Ω) P Q)
    (f : Ω → ℝ) (hf : Measurable f)
    -- Strongly recommended in Mathlib because ∫ is 0 if non-integrable:
    (hfP : Integrable f P)
    (hfExpQ : Integrable (fun ω => Real.exp (f ω)) Q) :
    (∫ ω, f ω ∂ P) - KLReal (Ω := Ω) P Q
      ≤ Real.log (∫ ω, Real.exp (f ω) ∂ Q) := by
  classical

  -- 1) From KLFinite, get absolute continuity + integrability of llr under P.
  have h_ne_top : KLinf (Ω := Ω) P Q ≠ ⊤ := hKL
  have h_ac_int : P ≪ Q ∧ Integrable (MeasureTheory.llr P Q) P := by
    simpa [KLinf] using (InformationTheory.klDiv_ne_top_iff (μ := P) (ν := Q)).1 h_ne_top
  have hPQ : P ≪ Q := h_ac_int.1
  have hllrP : Integrable (MeasureTheory.llr P Q) P := h_ac_int.2

  -- 2) Rewrite KLReal as an integral of llr (prob measures have equal mass on univ).
  have h_mass : P Set.univ = Q Set.univ := by simp
  have hKL_as_int :
      KLReal (Ω := Ω) P Q = ∫ ω, MeasureTheory.llr P Q ω ∂P := by
    -- toReal_klDiv_of_measure_eq: no integrability premise needed once masses match
    simpa [KLReal, KLinf] using
      (InformationTheory.toReal_klDiv_of_measure_eq (μ := P) (ν := Q) hPQ h_mass)

  -- 3) Let g = f - llr(P,Q). Then LHS becomes ∫ g dP.
  let g : Ω → ℝ := fun ω => f ω - MeasureTheory.llr P Q ω
  have hgP : Integrable g P := by
    -- integrable sub = integrable f + integrable llr
    simpa [g] using (hfP.sub hllrP)

  have hLHS : (∫ ω, f ω ∂P) - KLReal (Ω := Ω) P Q = ∫ ω, g ω ∂P := by
    -- ∫f - KL = ∫f - ∫llr = ∫(f-llr)
    simp [hKL_as_int, g, MeasureTheory.integral_sub hfP hllrP]

  -- 4) Show exp ∘ g is integrable under P.
  --    Use integrable_rnDeriv_smul_iff to move integrability to Q where it becomes ≤ exp f.
  have h_exp_llr :
      (fun ω => Real.exp (MeasureTheory.llr P Q ω))
        =ᵐ[Q] fun ω =>
          if P.rnDeriv Q ω = 0 then 1 else (P.rnDeriv Q ω).toReal :=
    MeasureTheory.exp_llr P Q

  have h_r_mul_exp_neg_llr :
      (fun ω => (P.rnDeriv Q ω).toReal * Real.exp (-MeasureTheory.llr P Q ω))
        =ᵐ[Q] fun ω => if P.rnDeriv Q ω = 0 then 0 else 1 := by
    filter_upwards [MeasureTheory.exp_llr P Q] with ω hω
    by_cases h0 : P.rnDeriv Q ω = 0
    · -- rnDeriv = 0: llr = log 0 = 0, exp(-0)=1, so LHS = 0
      simp [h0, MeasureTheory.llr_def]
    · -- rnDeriv ≠ 0: from exp_llr we get exp(llr)=toReal(rnDeriv)
      have hExp : Real.exp (MeasureTheory.llr P Q ω) = (P.rnDeriv Q ω).toReal := by
        simpa [h0] using hω
      have hExp_ne0 : Real.exp (MeasureTheory.llr P Q ω) ≠ 0 :=
        (Real.exp_pos _).ne'
      have h_toReal : (P.rnDeriv Q ω).toReal = Real.exp (MeasureTheory.llr P Q ω) :=
        hExp.symm
      calc
        (P.rnDeriv Q ω).toReal * Real.exp (-MeasureTheory.llr P Q ω)
            = Real.exp (MeasureTheory.llr P Q ω) * Real.exp (-MeasureTheory.llr P Q ω) := by
                simpa [h_toReal]
        _ = Real.exp (MeasureTheory.llr P Q ω) * (Real.exp (MeasureTheory.llr P Q ω))⁻¹ := by
                simp [Real.exp_neg]
        _ = (if P.rnDeriv Q ω = 0 then 0 else 1) := by
                -- a * a⁻¹ = 1, then simplify the if using h0
                simp [h0]

  have h_scaled_ae :
      (fun ω => (P.rnDeriv Q ω).toReal * Real.exp (g ω))
        =ᵐ[Q] fun ω =>
          if P.rnDeriv Q ω = 0 then 0 else Real.exp (f ω) := by
    filter_upwards [h_r_mul_exp_neg_llr] with ω hω
    by_cases h0 : P.rnDeriv Q ω = 0
    · simp [g, h0, sub_eq_add_neg, Real.exp_add, hω]
    ·
      -- First, simplify hω using h0 to get the clean cancellation equality
      have hcancel :
          (P.rnDeriv Q ω).toReal * Real.exp (-MeasureTheory.llr P Q ω) = (1 : ℝ) := by
        simpa [h0] using hω
      -- Rewrite the target expression using hcancel (commuting factors if needed)
      have hcancel' :
          Real.exp (-MeasureTheory.llr P Q ω) * (P.rnDeriv Q ω).toReal = (1 : ℝ) := by
        -- just commutativity
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel
      -- Now finish the main simp goal: expand exp(g)=exp(f-llr)=exp(f)*exp(-llr)
      -- and use hcancel'
      simp [g, h0, sub_eq_add_neg, Real.exp_add, hcancel', mul_assoc, mul_left_comm, mul_comm]

  have h_scaled_int :
      Integrable (fun ω => (P.rnDeriv Q ω).toReal • Real.exp (g ω)) Q := by
    -- 1) measurable set {ω | rnDeriv = 0}
    have hmr : Measurable (fun ω : Ω => P.rnDeriv Q ω) := by
      -- this lemma name exists in current Mathlib:
      -- #check Measure.measurable_rnDeriv
      simpa using (Measure.measurable_rnDeriv (μ := P) (ν := Q))

    have hmeas0 : MeasurableSet {ω : Ω | P.rnDeriv Q ω = (0 : ℝ≥0∞)} := by
      have hmr : Measurable (fun ω : Ω => P.rnDeriv Q ω) := by
        simpa using (Measure.measurable_rnDeriv (μ := P) (ν := Q))
      -- singleton {0} is measurable
      have hs : MeasurableSet ({(0 : ℝ≥0∞)} : Set ℝ≥0∞) :=
        measurableSet_singleton (0 : ℝ≥0∞)
      -- preimage is measurable
      have : MeasurableSet ((fun ω : Ω => P.rnDeriv Q ω) ⁻¹' ({(0 : ℝ≥0∞)} : Set ℝ≥0∞)) :=
        hs.preimage hmr
      -- rewrite to setOf form
      simpa [Set.preimage, Set.mem_singleton_iff] using this

    have hmeas_ne0 : MeasurableSet {ω : Ω | P.rnDeriv Q ω ≠ (0 : ℝ≥0∞)} :=
      hmeas0.compl

    -- 2) rewrite the RHS `if rnDeriv=0 then 0 else exp(f)` as an indicator
    have hite_eq :
        (fun ω : Ω => (if P.rnDeriv Q ω = 0 then (0 : ℝ) else Real.exp (f ω)))
          =
        ({ω : Ω | P.rnDeriv Q ω ≠ 0}).indicator (fun ω => Real.exp (f ω)) := by
      funext ω
      by_cases h0 : P.rnDeriv Q ω = 0
      · simp [h0]
      · simp [h0]

    -- 3) integrability: indicator of an integrable function on a measurable set
    have hite :
        Integrable (fun ω : Ω => (if P.rnDeriv Q ω = 0 then (0 : ℝ) else Real.exp (f ω))) Q := by
      -- `hfExpQ.indicator` is the key lemma here
      -- (it states integrability is preserved under `MeasurableSet.indicator`)
      simpa [hite_eq] using (hfExpQ.indicator hmeas_ne0)

    -- 4) transfer integrability across ae-eq; also change `•` to `*`
    have hLHS :
        (fun ω => (P.rnDeriv Q ω).toReal • Real.exp (g ω))
          =ᵐ[Q]
        fun ω => (if P.rnDeriv Q ω = 0 then (0 : ℝ) else Real.exp (f ω)) := by
      simpa [smul_eq_mul] using h_scaled_ae

    exact hite.congr hLHS.symm

  have hExpP : Integrable (fun ω => Real.exp (g ω)) P := by
    -- integrable_rnDeriv_smul_iff: Integrable ((rnDeriv)*f) Q ↔ Integrable f P
    -- (requires HaveLebesgueDecomposition and SigmaFinite, both true for prob measures)
    exact (MeasureTheory.integrable_rnDeriv_smul_iff (μ := P) (ν := Q) hPQ).1 h_scaled_int

  -- 5) Jensen with convex exp: exp(∫ g dP) ≤ ∫ exp(g) dP
  have hJ :
      Real.exp (∫ ω, g ω ∂P) ≤ ∫ ω, Real.exp (g ω) ∂P := by
    -- ConvexOn.map_integral_le
    have hconv := (convexOn_exp : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp)
    have hcontC : Continuous Real.exp := Real.continuous_exp
    have hcontOn : ContinuousOn Real.exp (Set.univ : Set ℝ) := hcontC.continuousOn
    have hclosed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
    have hmem : (∀ᵐ ω ∂P, g ω ∈ (Set.univ : Set ℝ)) := by
      simp
    simpa using hconv.map_integral_le (μ := P) hcontOn hclosed hmem hgP hExpP

  -- 6) Convert exp-inequality to log-inequality, then compare ∫ exp(g) dP ≤ ∫ exp(f) dQ.
  set ZP : ℝ := ∫ ω, Real.exp (g ω) ∂P
  have hZP_pos : 0 < ZP := by
    -- exp(∫g) > 0 and exp(∫g) ≤ ZP
    have : 0 < Real.exp (∫ ω, g ω ∂P) := Real.exp_pos _
    exact lt_of_lt_of_le this (by simpa [ZP] using hJ)

  have h_main : (∫ ω, g ω ∂P) ≤ Real.log ZP := by
    exact (Real.le_log_iff_exp_le hZP_pos).2 (by simpa [ZP] using hJ)

  -- Bound ZP by the Q-moment using change of measure + the `if rnDeriv=0` factor (≤ 1).
  have hZP_le : ZP ≤ ∫ ω, Real.exp (f ω) ∂Q := by
    -- rewrite ZP via integral_rnDeriv_smul
    have hZP_eq :
        ZP = ∫ ω, (P.rnDeriv Q ω).toReal * Real.exp (g ω) ∂Q := by
      -- integral_rnDeriv_smul gives ∫ rnDeriv * φ dQ = ∫ φ dP
      -- rearrange and unfold scalar action
      simpa [ZP, mul_comm, mul_left_comm, mul_assoc] using
        (MeasureTheory.integral_rnDeriv_smul (μ := P) (ν := Q) (E := ℝ) hPQ
          (f := fun ω => Real.exp (g ω))).symm
    -- now compare integrands a.e. using h_scaled_ae
    have h_ae_le :
        (fun ω => (P.rnDeriv Q ω).toReal * Real.exp (g ω)) ≤ᵐ[Q] fun ω => Real.exp (f ω) := by
      -- use the pointwise content of h_scaled_ae directly
      filter_upwards [h_scaled_ae] with ω hω
      by_cases h0 : P.rnDeriv Q ω = 0
      · -- then hω says LHS = 0, so goal is 0 ≤ exp(f ω)
        have : (P.rnDeriv Q ω).toReal * Real.exp (g ω) = 0 := by
          simpa [h0] using hω
        -- rewrite LHS to 0 and finish by nonneg of exp
        simpa [this] using (Real.exp_nonneg (f ω))
      · -- rnDeriv ≠ 0: hω says LHS = exp(f ω), so goal is exp(f ω) ≤ exp(f ω)
        have : (P.rnDeriv Q ω).toReal * Real.exp (g ω) = Real.exp (f ω) := by
          simpa [h0] using hω
        -- rewrite and close
        simpa [this]
    -- apply integral_mono_ae
    have hIntLeft :
        Integrable (fun ω => (P.rnDeriv Q ω).toReal * Real.exp (g ω)) Q := by
      -- from h_scaled_int (same function, scalar action = multiplication)
      simpa [smul_eq_mul] using h_scaled_int
    have hIntRight : Integrable (fun ω => Real.exp (f ω)) Q := hfExpQ
    have := MeasureTheory.integral_mono_ae hIntLeft hIntRight h_ae_le
    simpa [hZP_eq] using this

  -- finish
  calc
    (∫ ω, f ω ∂P) - KLReal (Ω := Ω) P Q
        = ∫ ω, g ω ∂P := hLHS
    _ ≤ Real.log ZP := h_main
    _ ≤ Real.log (∫ ω, Real.exp (f ω) ∂Q) :=
      Real.log_le_log hZP_pos hZP_le


  /-
If `Q` is a probability measure and `f` is uniformly bounded, then `E_Q[exp(f)] > 0`.

Why we want this:
* In the DV/PAC-Bayes chain we frequently get expressions like `Real.exp (Real.log I)`.
* To rewrite `Real.exp (Real.log I) = I`, mathlib needs `0 < I` via `Real.exp_log`. :contentReference[oaicite:0]{index=0}
* With Bochner integrals, `∫` is defined as `0` when the integrand is not integrable,
  so we **must** ensure integrability. A uniform bound gives integrability on a finite measure
  using `MeasureTheory.Integrable.of_bound`. :contentReference[oaicite:1]{index=1}
-/
theorem integral_exp_pos_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ ω, |f ω| ≤ B) :
    0 < ∫ ω, Real.exp (f ω) ∂ Q := by
  classical
  -- Probability measure ⇒ finite measure, needed for `Integrable.of_bound`.
  haveI : IsFiniteMeasure Q := by infer_instance

  -- Step 1: integrability of `exp ∘ f` from an a.e. bound by a constant.
  have hExp_aesm :
      AEStronglyMeasurable (fun ω => Real.exp (f ω)) Q := by
    exact (Real.measurable_exp.comp hf).aestronglyMeasurable

  have hExp_bound :
      ∀ᵐ ω ∂Q, ‖Real.exp (f ω)‖ ≤ Real.exp B := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    -- from `|f ω| ≤ B` we get `f ω ≤ B`
    have hle : f ω ≤ B := (abs_le.mp (hfb ω)).2
    have : Real.exp (f ω) ≤ Real.exp B := Real.exp_le_exp.mpr hle
    -- turn it into a norm inequality; `exp` is nonnegative
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using this

  have hIntExp : Integrable (fun ω => Real.exp (f ω)) Q :=
    MeasureTheory.Integrable.of_bound hExp_aesm (Real.exp B) hExp_bound
    -- `Integrable.of_bound` :contentReference[oaicite:2]{index=2}

  -- Step 2: lower bound the expectation by integrating the constant `exp(-B)`.
  have hLower :
      ∀ᵐ ω ∂Q, Real.exp (-B) ≤ Real.exp (f ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hge : -B ≤ f ω := (abs_le.mp (hfb ω)).1
    exact Real.exp_le_exp.mpr hge

  have hIntConst : Integrable (fun _ : Ω => Real.exp (-B)) Q := by
    simpa using (integrable_const : Integrable (fun _ : Ω => Real.exp (-B)) Q)

  have hmono :
      (∫ ω, Real.exp (-B) ∂Q) ≤ (∫ ω, Real.exp (f ω) ∂Q) :=
    MeasureTheory.integral_mono_ae hIntConst hIntExp hLower
    -- `integral_mono_ae` :contentReference[oaicite:3]{index=3}

  have hconst : (∫ ω, Real.exp (-B) ∂Q) = Real.exp (-B) := by
    simp

  have hpos_const : 0 < Real.exp (-B) := Real.exp_pos (-B)

  -- conclude
  have : Real.exp (-B) ≤ (∫ ω, Real.exp (f ω) ∂Q) := by
    simpa [hconst] using hmono
  exact lt_of_lt_of_le hpos_const this

/-- Exponentiated DV inequality, matching Eq. (121) after taking `exp`. -/
-- theorem exp_dv_ineq
--     {Ω : Type*} [MeasurableSpace Ω]
--     (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
--     (hKL : KLFinite (Ω := Ω) P Q)
--     (f : Ω → ℝ) (hf : Measurable f)
--     (hIpos : 0 < ∫ ω, Real.exp (f ω) ∂ Q) -- extra assumption
--     :
--     Real.exp ((∫ ω, f ω ∂ P) - KLReal (Ω := Ω) P Q)
--       ≤ (∫ ω, Real.exp (f ω) ∂ Q) := by
--   /-
--   Proof sketch:
--   * Start from `donsker_varadhan_ineq` and apply monotonicity of `Real.exp`:
--       `Real.exp_le_exp.mpr` turns `a ≤ b` into `exp(a) ≤ exp(b)`.
--   * The right-hand side becomes `exp(log I)` where `I := ∫ ω, exp(f ω) ∂Q`.
--     Show `0 < I` (using `Real.exp_pos` and that `Q` is a probability measure) and then rewrite
--     `Real.exp (Real.log I) = I` via `Real.exp_log` (or `Real.exp_log` with the positivity proof).
--   * The remaining technical obligation is that the Bochner integral `∫ exp(f) dQ` behaves as expected,
--     i.e. we will want an integrability lemma ensuring it is finite and strictly positive.
--   -/
--   have h := donsker_varadhan_ineq (hKL := hKL) (P := P) (Q := Q) (f := f) hf
--   -- exponentiate both sides
--   have hexp :
--       Real.exp ((∫ ω, f ω ∂ P) - KLReal (Ω := Ω) P Q)
--         ≤ Real.exp (Real.log (∫ ω, Real.exp (f ω) ∂ Q)) :=
--     (Real.exp_le_exp).2 h
--   -- simplify `exp (log I)` using positivity
--   simpa [Real.exp_log hIpos] using hexp


-- probably ok to use this version instead.
theorem exp_dv_ineq_more_assumptions
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite (Ω := Ω) P Q)
    (f : Ω → ℝ) (hf : Measurable f)
    (hIpos : 0 < ∫ ω, Real.exp (f ω) ∂ Q) -- extra assumption
    (hfP : Integrable f P) -- extra assumption
    (hfExpQ : Integrable (fun ω => Real.exp (f ω)) Q) -- extra assumption
    :
    Real.exp ((∫ ω, f ω ∂ P) - KLReal (Ω := Ω) P Q)
      ≤ (∫ ω, Real.exp (f ω) ∂ Q) := by
  /-
  Proof sketch:
  * Start from `donsker_varadhan_ineq` and apply monotonicity of `Real.exp`:
      `Real.exp_le_exp.mpr` turns `a ≤ b` into `exp(a) ≤ exp(b)`.
  * The right-hand side becomes `exp(log I)` where `I := ∫ ω, exp(f ω) ∂Q`.
    Show `0 < I` (using `Real.exp_pos` and that `Q` is a probability measure) and then rewrite
    `Real.exp (Real.log I) = I` via `Real.exp_log` (or `Real.exp_log` with the positivity proof).
  * The remaining technical obligation is that the Bochner integral `∫ exp(f) dQ` behaves as expected,
    i.e. we will want an integrability lemma ensuring it is finite and strictly positive.
  -/
  have h :=
    donsker_varadhan_ineq_more_assumptions
      (P := P) (Q := Q) (hKL := hKL) (f := f) (hf := hf)
      (hfP := hfP) (hfExpQ := hfExpQ)
  -- exponentiate both sides
  have hexp :
      Real.exp ((∫ ω, f ω ∂ P) - KLReal (Ω := Ω) P Q)
        ≤ Real.exp (Real.log (∫ ω, Real.exp (f ω) ∂ Q)) :=
    (Real.exp_le_exp).2 h
  -- simplify `exp (log I)` using positivity
  simpa [Real.exp_log hIpos] using hexp


/-!
### A mathlib-first route to Eq. (122)

We want an exponential-moment inequality over the i.i.d. sample `S : Fin n → X`.
The key observation is that under the product measure, integrals of *coordinatewise products*
factorize via `MeasureTheory.integral_fintype_prod_eq_pow`.

Hoeffding’s lemma is already in mathlib in subgaussian form:
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`.
It gives an MGF bound for the *centered* random variable `g - E[g]` when `g` is a.s. bounded in an interval.
-/

/-- Convenience: pointwise `|g x| ≤ C` implies a.e. `g x ∈ [-C, C]`. -/
lemma ae_mem_Icc_of_abs_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : X → ℝ) (C : ℝ) (hg : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂ μ, g x ∈ Set.Icc (-C) C := by
  -- This avoids `Filter.eventually_of_forall` (since it was missing in your environment).
  -- Use the characterization of `∀ᵐ` via measure of the complement being zero.
  -- Proof idea: the bad set is empty because the property holds pointwise.
  have hpoint : ∀ x, g x ∈ Set.Icc (-C) C := by
    intro x
    have : |g x| ≤ C := hg x
    -- `abs_le` gives `-C ≤ g x ∧ g x ≤ C`.
    exact (abs_le.mp this)
  -- Now convert pointwise truth to `ae` by `simp`.
  -- The set `{x | ¬ g x ∈ Icc (-C) C}` is empty.
  have : {x | ¬ g x ∈ Set.Icc (-C) C} = (∅ : Set X) := by
    ext x; simp
    grind
  -- `Measure.ae_iff` is the usual bridge.
  -- If `Measure.ae_iff` isn’t in your imports, replace with `by simp [Filter.Eventually, this]`.
  simp [Filter.Eventually]
  exact Filter.univ_mem' hpoint


lemma exp_pow_nat (A : ℝ) (m : ℕ) :
    (Real.exp A) ^ m = Real.exp (A * (m : ℝ)) := by
  induction m with
  | zero =>
      simp
  | succ k hk =>
      calc
        (Real.exp A) ^ Nat.succ k
            = (Real.exp A) ^ k * Real.exp A := by
                simp [pow_succ]
        _   = Real.exp (A * (k : ℝ)) * Real.exp A := by
                -- rewrite the power using the induction hypothesis
                rw [hk]
        _   = Real.exp (A * (k : ℝ) + A) := by
                -- product -> exp(sum)
                simpa using (Eq.symm (Real.exp_add (A * (k : ℝ)) A))
        _   = Real.exp (A * ((k : ℝ) + 1)) := by
                ring_nf
        _   = Real.exp (A * (Nat.succ k : ℝ)) := by
                simp


/-- Hoeffding/MGF step for the empirical mean under the i.i.d. product measure.

This is the analytic core behind the quadratic term `ε^2 C^2 / (2n)`.

The proof strategy is:
1. Rewrite `exp(ε(R - r(S)))` as a product over coordinates via `exp(sum)=prod(exp)`.
2. Use `integral_fintype_prod_eq_pow` to factor the product-measure integral.
3. Bound the 1D integral using `hasSubgaussianMGF_of_mem_Icc` (Hoeffding’s lemma).
-/
theorem hoeffding_empMean_mgf
    {X : Type*} [MeasurableSpace X]
    (P1 : Measure X) [IsProbabilityMeasure P1]
    (g : X → ℝ) (C ε : ℝ) (n : ℕ)
    (hn : 0 < n) (hC : 0 ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∀ x, |g x| ≤ C) :
    let μS : Measure (Fin n → X) := iidsampleMeasure P1 n
    let R  : ℝ := R_of (X := X) P1 g
    let r  : (Fin n → X) → ℝ := r_of (X := X) n g
    (∫ s, Real.exp (ε * (R - r s)) ∂ μS)
      ≤ Real.exp (ε^2 * C^2 / (2 * (n : ℝ))) := by
  classical
  intro μS R r
  -- Set t = ε / n.
  let t : ℝ := ε / (n : ℝ)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn

  -- Step 1: rewrite the exponent as a sum over coordinates.
  --   ε*(R - r s) = t * ∑ i, (R - g (s i))
  -- because `r s = (1/n) * ∑ g(s i)`.
  have hexp_rewrite :
      (fun s => Real.exp (ε * (R - r s)))
        =
      (fun s => ∏ i : Fin n, Real.exp (t * (R - g (s i)))) := by
    classical
    funext s
    -- abbreviate the sample sum
    let S : ℝ := ∑ i : Fin n, g (s i)
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)

    -- Step 1: rewrite the LHS exponent using the definition of `r`
    have hL :
        ε * (R - r s) = ε * (R - (1 / (n : ℝ)) * S) := by
      -- unfold `r = r_of = empMean`
      simp [r, r_of, empMean, S]

    -- Step 2: rewrite the RHS exponent as a sum over coordinates
    have hR :
        (∑ i : Fin n, t * (R - g (s i))) = (ε / (n : ℝ)) * ((n : ℝ) * R - S) := by
      classical
      -- expand t and S, and rewrite subtraction as addition of negatives
      simp [t, S, sub_eq_add_neg, mul_add, Finset.mul_sum]  -- pulls out ε/n
      -- after the simp, the goal should be:
      -- ∑ i, (-g(s i) + R) = (n:ℝ)*R + -∑ i, g(s i)
      -- prove that:
      have :
          (∑ i : Fin n, (-g (s i) + R))
            = (n : ℝ) * R + - (∑ i : Fin n, g (s i)) := by
        -- distribute sum over addition:
        -- ∑ (-g(s i) + R) = ∑ (-g(s i)) + ∑ R
        -- and ∑ R = n*R, ∑ (-g) = -(∑ g)
        calc
          (∑ i : Fin n, (-g (s i) + R))
              = (∑ i : Fin n, (-g (s i))) + (∑ i : Fin n, R) := by
                  simpa [Finset.sum_add_distrib]
          _   = (-(∑ i : Fin n, g (s i))) + (∑ i : Fin n, R) := by
                  -- pull neg outside the sum
                  simpa [Finset.sum_neg_distrib]
          _   = (-(∑ i : Fin n, g (s i))) + (n : ℝ) * R := by
                  -- sum of a constant over `Fin n` is `n * R`
                  -- `Finset.card_univ` for `Fin n` is `n`
                  simpa using (by
                    -- `Finset.sum_const` gives: ∑ i in univ, R = (card univ) • R
                    -- and for ℝ, `nsmul` is multiplication by n
                    simp [Finset.sum_const, Finset.card_univ])
          _   = (n : ℝ) * R + (-(∑ i : Fin n, g (s i))) := by ac_rfl
      -- At this point you have:
      -- this : ∑ i, (-g (s i) + R) = (n:ℝ) * R + -∑ i, g (s i)
      -- and your goal is a scaled version with ε/↑n distributed.
      -- Let a be the scalar ε/↑n
      let a : ℝ := ε / (n : ℝ)
      -- Prove the scaled sum identity directly
      have hscale :
          (∑ x : Fin n, (a * R + -(a * g (s x))))
            =
          a * ((n : ℝ) * R) + - (∑ i : Fin n, a * g (s i)) := by
        -- Expand sum over addition
        calc
          (∑ x : Fin n, (a * R + -(a * g (s x))))
              = (∑ x : Fin n, a * R) + (∑ x : Fin n, -(a * g (s x))) := by
                  simpa [Finset.sum_add_distrib]
          _   = (∑ x : Fin n, a * R) + - (∑ x : Fin n, a * g (s x)) := by
                  -- pull neg out of the sum
                  simpa [Finset.sum_neg_distrib]
          _   = a * ((n : ℝ) * R) + - (∑ x : Fin n, a * g (s x)) := by
                  -- sum of a constant over `Fin n` is `n * const`
                  -- `simp` knows `Finset.card_univ` for `Fin n` is `n`
                  -- and `nsmul` becomes multiplication on `ℝ`
                  simp [Finset.sum_const, Finset.card_univ, mul_assoc, mul_left_comm, mul_comm]
          _   = a * ((n : ℝ) * R) + - (∑ i : Fin n, a * g (s i)) := by
                  rfl

      -- Now use `a = ε/↑n` to match your goal
      -- (your goal uses `ε/↑n` explicitly; we unfold `a`)
      simpa [a] using hscale

    -- Step 3: show the LHS exponent equals the same closed form
    have hE :
        ε * (R - (1 / (n : ℝ)) * S) = (ε / (n : ℝ)) * ((n : ℝ) * R - S) := by
      -- clear denominators (needs `n ≠ 0`)
      field_simp [hn0]

    -- Combine exponent equalities
    have hsum :
        ε * (R - r s) = ∑ i : Fin n, t * (R - g (s i)) := by
      -- use hL, hE, hR
      calc
        ε * (R - r s)
            = ε * (R - (1 / (n : ℝ)) * S) := hL
        _   = (ε / (n : ℝ)) * ((n : ℝ) * R - S) := hE
        _   = (∑ i : Fin n, t * (R - g (s i))) := by
                symm
                exact hR

    -- Finally: exp(sum) = product(exp)
    calc
      Real.exp (ε * (R - r s))
          = Real.exp (∑ i : Fin n, t * (R - g (s i))) := by
              simp [hsum]
      _   = ∏ i : Fin n, Real.exp (t * (R - g (s i))) := by
              -- `Real.exp_sum` is stated for `Finset`; `∑ i : Fin n` is `Finset.univ.sum`.
              simpa using
                (Real.exp_sum (s := (Finset.univ : Finset (Fin n)))
                              (f := fun i : Fin n => t * (R - g (s i))))

  -- Step 2: factor the product-measure integral using `integral_fintype_prod_eq_pow`.
  -- Here `μS = Measure.pi (fun _ : Fin n => P1)` by your definition.
  have hfactor :
      (∫ s, (∏ i : Fin n, Real.exp (t * (R - g (s i)))) ∂ μS)
        =
      (∫ x, Real.exp (t * (R - g x)) ∂ P1) ^ n := by
    -- Use `MeasureTheory.integral_fintype_prod_eq_pow` and unfold `μS`.
    -- This is exactly what that lemma is for.  :contentReference[oaicite:3]{index=3}
    -- You may need:
    --   `simp [μS, iidsampleMeasure]`
    -- and then apply:
    --   `MeasureTheory.integral_fintype_prod_eq_pow (ι := Fin n) (μ := P1) (f := ...)`.
    classical
    -- Let the 1D factor be `F x = exp(t * (R - g x))`
    let F : X → ℝ := fun x => Real.exp (t * (R - g x))

    -- `integral_fintype_prod_eq_pow` does exactly this factorization for `Measure.pi`
    -- (finite product measure) and coordinatewise products.
    simpa [μS, iidsampleMeasure, F] using
      (MeasureTheory.integral_fintype_prod_eq_pow
        (ι := Fin n) (μ := P1) (f := F))

  -- Step 3: bound the 1D integral via Hoeffding’s lemma in subgaussian form.
  have hI :
      (∫ x, Real.exp (t * (R - g x)) ∂ P1)
        ≤ Real.exp (t^2 * C^2 / 2) := by
    -- Outline:
    -- * Apply `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` to `g` under `P1`
    --   with interval endpoints `a=-C`, `b=C`.  :contentReference[oaicite:4]{index=4}
    -- * This yields subgaussian MGF control for `(fun x => g x - ∫ g)`.
    -- * Rewrite `(R - g x)` as `-(g x - R)` and apply the mgf bound at `(-t)`.
    -- * Simplify `(-t)^2 = t^2`.
    --
    -- The only slightly annoying part is simplifying the NNReal-interval parameter
    -- `((‖C - (-C)‖₊ / 2)^2)` down to `C^2` using `hC`.
    classical
    -- Step 3a: boundedness gives an a.e. interval constraint g x ∈ [-C, C]
    have hg_ae : AEMeasurable g P1 := hg_meas.aemeasurable
    have hIcc : ∀ᵐ x ∂ P1, g x ∈ Set.Icc (-C) C := by
      refine Filter.Eventually.of_forall ?_
      intro x
      exact abs_le.mp (hg_bd x)

    -- Step 3b: Hoeffding's lemma (subgaussian MGF) for the centered variable (g - E[g])
    -- This gives: mgf (g - ∫ g) t ≤ exp( ((‖C - (-C)‖₊/2)^2) * t^2 / 2 )
    have hSubG :
        ProbabilityTheory.HasSubgaussianMGF
          (fun x : X => g x - ∫ y, g y ∂ P1)
          ((‖(C : ℝ) - (-C)‖₊ / 2) ^ 2) P1 :=
      ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := P1) hg_ae hIcc

    -- Step 3c: relate our integrand to the mgf of the centered variable at parameter (-t)
    -- Let Xc(x) = g(x) - R, where R = ∫ g.
    let Xc : X → ℝ := fun x => g x - R
    have hXc : Xc = (fun x : X => g x - ∫ y, g y ∂ P1) := by
      -- R is definitionally ∫ g by how `R` was set in the surrounding proof
      -- (in your context, `R : ℝ := R_of P1 g`)
      -- so this is just definitional unfolding + simp.
      -- If this doesn't close, replace with `simp [Xc, R, R_of, popMean]`.
      simpa [Xc, R, R_of, popMean]

    -- mgf bound from subgaussianity:
    -- mgf Xc P1 (-t) ≤ exp( ((‖2C‖₊/2)^2) * (-t)^2 / 2 )
    have hmgf :
        ProbabilityTheory.mgf Xc P1 (-t)
          ≤ Real.exp (((((‖(C : ℝ) - (-C)‖₊ / 2) ^ 2 : NNReal) : ℝ) * (-t) ^ 2) / 2) := by
      -- Use `hSubG.mgf_le` and rewrite Xc via hXc.
      -- `HasSubgaussianMGF.mgf_le` is the field giving the mgf upper bound. :contentReference[oaicite:1]{index=1}
      simpa [hXc] using (hSubG.mgf_le (-t))

    -- Convert our integral into that mgf:
    have hmgf_id :
        (∫ x, Real.exp (t * (R - g x)) ∂ P1) = ProbabilityTheory.mgf Xc P1 (-t) := by
      -- mgf Xc P1 (-t) = ∫ exp((-t) * Xc(x)) dP1
      -- and (-t)*Xc(x) = (-t)*(g x - R) = t*(R - g x)
      simp [ProbabilityTheory.mgf, Xc, sub_eq_add_neg, mul_add, mul_sub, add_comm, add_left_comm,
        add_assoc, mul_assoc, mul_left_comm, mul_comm]

    -- Step 3d: simplify the parameter and (-t)^2 = t^2, then finish.
    have ht2 : (-t) ^ 2 = t ^ 2 := by
      ring

    have hparam :
        (((‖(C : ℝ) - (-C)‖₊ / 2) ^ 2 : NNReal) : ℝ) = C ^ 2 := by
      -- (C - (-C)) = 2C, nnnorm(2C) with C≥0 is 2C, divide by 2 gives C, square gives C^2
      have h2C : 0 ≤ (2 * C) := by nlinarith [hC]
      -- `simp` knows how to evaluate `‖2*C‖₊` under `0 ≤ 2*C`
      -- then it's just ring arithmetic.
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hC, h2C, pow_two]
      ring_nf
      grind

    -- combine: integral = mgf ≤ exp(param * t^2 / 2) = exp(t^2*C^2/2)
    calc
      (∫ x, Real.exp (t * (R - g x)) ∂ P1)
          = ProbabilityTheory.mgf Xc P1 (-t) := by
              simpa [hmgf_id]
      _   ≤ Real.exp (((((‖(C : ℝ) - (-C)‖₊ / 2) ^ 2 : NNReal) : ℝ) * (-t) ^ 2) / 2) := hmgf
      _   = Real.exp (t ^ 2 * C ^ 2 / 2) := by
              -- rewrite (-t)^2 and the parameter, then reassociate
              simp [ht2, hparam, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
              grind

  -- Step 4: raise the 1D bound to power `n` and simplify exponent algebra.
  have hpow :
      (∫ x, Real.exp (t * (R - g x)) ∂ P1) ^ n
        ≤ Real.exp (ε^2 * C^2 / (2 * (n : ℝ))) := by
    -- Use `hI` plus monotonicity of `pow` (note the base is ≥ 0),
    -- then rewrite:
    --   (exp (t^2*C^2/2))^n = exp (n*(t^2*C^2/2))
    -- and finally substitute `t = ε/n`.
    classical
    let I : ℝ := ∫ x, Real.exp (t * (R - g x)) ∂ P1
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)

    -- Nonnegativity of the base `I`
    have hI_nonneg : 0 ≤ I := by
      -- integrand is pointwise nonnegative
      have : ∀ x, 0 ≤ Real.exp (t * (R - g x)) := by
        intro x; exact le_of_lt (Real.exp_pos _)
      simpa [I] using (MeasureTheory.integral_nonneg this)

    -- Raise the 1D bound to the n-th power
    have hpow1 :
        I ^ n ≤ (Real.exp (t ^ 2 * C ^ 2 / 2)) ^ n := by
      -- `pow_le_pow_of_le_left` needs `0 ≤ I`
      exact pow_le_pow_left₀ hI_nonneg hI n

    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn

    -- Simplify the exponent after substituting `t = ε / n`
    have hcalc :
        ((n : ℝ) * (t ^ 2 * C ^ 2 / 2)) = (ε ^ 2 * C ^ 2 / (2 * (n : ℝ))) := by
      -- unfold t and clear denominators
      dsimp [t]
      field_simp [hn0]

    -- Finish: I^n ≤ (exp(...))^n = exp(n*...) = exp(ε^2*C^2/(2n))
    calc
      (∫ x, Real.exp (t * (R - g x)) ∂ P1) ^ n
          = I ^ n := by simp [I]
      _   ≤ (Real.exp (t ^ 2 * C ^ 2 / 2)) ^ n := hpow1
      _   = Real.exp (((t ^ 2 * C ^ 2 / 2)) * (n : ℝ)) := by
             simpa using (exp_pow_nat (A := (t ^ 2 * C ^ 2 / 2)) (m := n))
      _   = Real.exp (ε ^ 2 * C ^ 2 / (2 * (n : ℝ))) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hcalc

  -- Combine.
  -- Start from the LHS, rewrite as product, factor integral, then apply the bound.
  calc
    (∫ s, Real.exp (ε * (R - r s)) ∂ μS)
        = (∫ s, (∏ i : Fin n, Real.exp (t * (R - g (s i)))) ∂ μS) := by
            simpa [hexp_rewrite]
    _   = (∫ x, Real.exp (t * (R - g x)) ∂ P1) ^ n := by
            simpa [hfactor]
    _   ≤ Real.exp (ε^2 * C^2 / (2 * (n : ℝ))) := hpow


/-- (Eq. 122) PAC-Bayes exponential-moment inequality (paper-rearranged form). -/
theorem pacBayes_exp_moment_eq122
    {X : Type*} [MeasurableSpace X]
    {Ω : Type*} [MeasurableSpace Ω]
    (P1 : Measure X) [IsProbabilityMeasure P1]
    (g : X → ℝ) (C ε ς : ℝ) (n : ℕ)
    (hn : 0 < n) (hC : 0 ≤ C) (hε : 0 < ε)
    (hg_meas : Measurable g) (hg_bd : ∀ x, |g x| ≤ C)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite (Ω := Ω) P Q) :
    (∫ s,
      Real.exp
        ( ε * (R_of (X:=X) P1 g - r_of (X:=X) n g s)
          - KLReal (Ω := Ω) P Q
          - (ε^2 * C^2) / (2 * (n : ℝ)) )
      ∂ (iidsampleMeasure P1 n)) ≤ 1 := by
  classical

  -- abbreviations
  set μS : Measure (Fin n → X) := iidsampleMeasure P1 n
  set R  : ℝ := R_of (X := X) P1 g
  set r  : (Fin n → X) → ℝ := r_of (X := X) n g
  set quad : ℝ := (ε^2 * C^2) / (2 * (n : ℝ))
  set kl : ℝ := KLReal (Ω := Ω) P Q

  -- Hoeffding/MGF bound:  E[exp(ε(R - r))] ≤ exp(quad)
  have hH :
      (∫ s, Real.exp (ε * (R - r s)) ∂ μS) ≤ Real.exp quad := by
    -- this is exactly what `hoeffding_empMean_mgf` proves (with the work you already did)
    simpa [μS, R, r, quad] using
      (hoeffding_empMean_mgf (P1 := P1) (g := g) (C := C) (ε := ε) (n := n)
        hn hC hg_meas hg_bd)

  -- Rewrite the target integral by factoring out the constants `exp(-kl)` and `exp(-quad)`.
  have hRewrite :
      (∫ s, Real.exp (ε * (R - r s) - kl - quad) ∂ μS)
        =
      Real.exp (-kl - quad) * (∫ s, Real.exp (ε * (R - r s)) ∂ μS) := by
    have hpoint :
        (fun s => Real.exp (ε * (R - r s) - kl - quad))
          =
        (fun s => Real.exp (-kl - quad) * Real.exp (ε * (R - r s))) := by
      funext s
      have : ε * (R - r s) - kl - quad = (-kl - quad) + ε * (R - r s) := by
        ring
      simpa [this, Real.exp_add]
    -- integrate and pull out the left constant
    calc
      (∫ s, Real.exp (ε * (R - r s) - kl - quad) ∂ μS)
          = ∫ s, (Real.exp (-kl - quad) * Real.exp (ε * (R - r s))) ∂ μS := by
              simpa [hpoint]
      _   = Real.exp (-kl - quad) * (∫ s, Real.exp (ε * (R - r s)) ∂ μS) := by
              simpa using (MeasureTheory.integral_const_mul (r := Real.exp (-kl - quad))
                (f := fun s => Real.exp (ε * (R - r s))) (μ := μS))

  -- Use hRewrite + Hoeffding bound:
  -- integral ≤ exp(-kl-quad) * exp(quad) = exp(-kl)
  have hMain :
      (∫ s, Real.exp (ε * (R - r s) - kl - quad) ∂ μS) ≤ Real.exp (-kl) := by
    -- start from rewrite
    have := congrArg (fun z => z) hRewrite
    -- use it as a rewrite rule
    -- and then apply `mul_le_mul_of_nonneg_left` with nonneg constant
    -- (exp is always nonneg)
    have hnonneg : 0 ≤ Real.exp (-kl - quad) := le_of_lt (Real.exp_pos _)
    calc
      (∫ s, Real.exp (ε * (R - r s) - kl - quad) ∂ μS)
          = Real.exp (-kl - quad) * (∫ s, Real.exp (ε * (R - r s)) ∂ μS) := by
              simpa using hRewrite
      _   ≤ Real.exp (-kl - quad) * Real.exp quad := by
              exact mul_le_mul_of_nonneg_left hH hnonneg
      _   = Real.exp (-kl) := by
              -- exp(-kl-quad) * exp(quad) = exp((-kl-quad)+quad) = exp(-kl)
              -- use exp_add backwards
              have : (-kl - quad) + quad = -kl := by ring
              -- `Real.exp_add` : exp(a+b) = exp a * exp b
              -- so rewrite the product into exp(sum)
              calc
                Real.exp (-kl - quad) * Real.exp quad
                    = Real.exp ((-kl - quad) + quad) := by
                        simpa [Real.exp_add] using (Eq.symm (Real.exp_add (-kl - quad) quad))
                _   = Real.exp (-kl) := by simpa [this]

  -- Finally, KLReal is nonnegative ⇒ exp(-KLReal) ≤ 1.
  have hKL_nonneg : 0 ≤ kl := by
    -- `kl = (KLinf P Q).toReal` and toReal is always ≥ 0
    simp [kl, KLReal, KLinf]

  have hExp_le_one : Real.exp (-kl) ≤ 1 := by
    -- exp x ≤ 1 ↔ x ≤ 0
    have : (-kl) ≤ 0 := by exact neg_nonpos.mpr hKL_nonneg
    exact (Real.exp_le_one_iff).2 this

  -- Conclude.
  -- Switch back to the original expression (with R_of/r_of and minus signs).
  have : (∫ s,
      Real.exp
        ( ε * (R_of (X:=X) P1 g - r_of (X:=X) n g s)
          - KLReal (Ω := Ω) P Q
          - (ε^2 * C^2) / (2 * (n : ℝ)) )
      ∂ (iidsampleMeasure P1 n))
      =
    (∫ s, Real.exp (ε * (R - r s) - kl - quad) ∂ μS) := by
    simp [μS, R, r, quad, kl, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

  -- combine everything
  calc
    (∫ s,
      Real.exp
        ( ε * (R_of (X:=X) P1 g - r_of (X:=X) n g s)
          - KLReal (Ω := Ω) P Q
          - (ε^2 * C^2) / (2 * (n : ℝ)) )
      ∂ (iidsampleMeasure P1 n))
        = (∫ s, Real.exp (ε * (R - r s) - kl - quad) ∂ μS) := by simpa [this]
    _   ≤ Real.exp (-kl) := hMain
    _   ≤ 1 := hExp_le_one

/-!
### Markov/Chernoff step

**Lean proof outline**

You want:
  μ {x | a ≤ Z x} ≤ ofReal ((∫ Z dμ) / a)

Given:
- `Z ≥ 0` a.e.
- `a > 0`

In Lean, the cleanest route is to use an existing Markov inequality lemma.
Search for lemmas like:
- `Measure.measure_ge_le_integral_div` / `measure_ge_le_integral_div`
- `MeasureTheory.measure_le_of_integral_le` variants
- lemmas about `lintegral` with `ENNReal` might be easier if you define Z as `α → ENNReal`
  and use `lintegral` rather than `integral`.

If you must prove it:
1. Use indicator:
   `{x | a ≤ Z x}` implies `a * (indicator ...) ≤ Z` pointwise (on that set)
2. Integrate both sides:
   `a * μ{...} ≤ ∫ Z`
3. Divide by a (and convert to `ENNReal` with `ofReal`).

The hardest part is coercions between ℝ and ENNReal; often easiest is to work in ENNReal:
- let `Z' : α → ENNReal := fun x => ENNReal.ofReal (Z x)`
- state Markov in terms of `lintegral`.
-/
lemma markov_inequality_exp
  {α : Type*} [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]
  (X : α → ℝ)
  (hX_nonneg : 0 ≤ᵐ[μ] X)
  (a : ℝ) (ha : 0 < a)
  (hX_meas : Measurable X)
  (hX_int : Integrable X μ) :
  μ {x | a ≤ X x} ≤ ENNReal.ofReal ((∫ x, X x ∂ μ) / a) := by
  classical
  let S : Set α := {x | a ≤ X x}
  have hS : MeasurableSet S := by
    simpa [S] using (measurableSet_le measurable_const hX_meas)

  -- Pointwise a.e.: a * 1_S ≤ X
  have hpoint :
      ∀ᵐ x ∂ μ, a * (S.indicator (fun _ => (1 : ℝ)) x) ≤ X x := by
    filter_upwards [hX_nonneg] with x hx0
    by_cases hxS : x ∈ S
    · have hx : a ≤ X x := by simpa [S] using hxS
      -- unfold indicator via `simp [Set.indicator, hxS]` (no indicator_of_mem lemma needed)
      simp [Set.indicator, hxS, hx, mul_one]
    · -- off S, indicator = 0, goal becomes 0 ≤ X x, which is hx0
      -- again use `simp [Set.indicator, hxS]`, no indicator_of_not_mem needed
      simpa [Set.indicator, hxS] using hx0

  -- integrability of the LHS function
  have hind_int : Integrable (fun x => S.indicator (fun _ => (1 : ℝ)) x) μ := by
    -- indicator of an integrable function is integrable
    have h1 : Integrable (fun _ : α => (1 : ℝ)) μ := integrable_const (1 : ℝ)
    exact h1.indicator hS
  have hleft_int : Integrable (fun x => a * (S.indicator (fun _ => (1 : ℝ)) x)) μ := by
    simpa [mul_assoc] using hind_int.const_mul a

  -- now we can integrate the pointwise inequality
  have hint :
      ∫ x, a * (S.indicator (fun _ => (1 : ℝ)) x) ∂ μ ≤ ∫ x, X x ∂ μ := by
    exact integral_mono_ae hleft_int hX_int hpoint

  -- pull out the constant a from the left integral
  have hint' :
      a * (∫ x, (S.indicator (fun _ => (1 : ℝ)) x) ∂ μ) ≤ ∫ x, X x ∂ μ := by
    -- start from `hint : ∫ (a * 1_S) ≤ ∫ X`
    -- rewrite the left integral as `a * ∫ 1_S`
    have this :
        (∫ x, a * (S.indicator (fun _ => (1 : ℝ)) x) ∂ μ)
          = a * (∫ x, (S.indicator (fun _ => (1 : ℝ)) x) ∂ μ) := by
      simpa [mul_assoc] using (integral_const_mul a (fun x => S.indicator (fun _ => (1 : ℝ)) x) (μ := μ))
    simpa [this] using hint

  -- compute ∫ 1_S = (μ S).toReal
  have hind :
      (∫ x, (S.indicator (fun _ => (1 : ℝ)) x) ∂ μ) = (μ S).toReal := by
    -- integral of indicator of a constant
    simpa using (integral_indicator_const (μ := μ) (s := S) (e := (1 : ℝ)) hS)

  -- convert toReal inequality and divide by a>0
  have htoReal : (μ S).toReal ≤ (∫ x, X x ∂ μ) / a := by
    have : (μ S).toReal * a ≤ ∫ x, X x ∂ μ := by
      -- from hint' : a * ∫ 1_S ≤ ∫ X, substitute hind and commute multiplication
      -- (μ S).toReal * a is what `le_div_iff` expects
      have : a * (μ S).toReal ≤ ∫ x, X x ∂ μ := by
        simpa [hind] using hint'
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    exact (le_div_iff₀ ha).2 this

  -- show μ S ≠ ⊤ (since μ S ≤ 1 < ⊤)
  have hμS_ne_top : μ S ≠ ⊤ := by
    have : μ S ≤ μ Set.univ := measure_mono (Set.subset_univ S)
    have huniv : μ Set.univ = (1 : ENNReal) := by
      simpa using (IsProbabilityMeasure.measure_univ (μ := μ))
    have : μ S ≤ (1 : ENNReal) := by simpa [huniv] using this
    have : μ S < ⊤ := lt_of_le_of_lt this (by simpa using (one_lt_top : (1 : ENNReal) < ⊤))
    exact ne_of_lt this

  -- convert back to ENNReal using `ofReal_toReal`
  have hμS_le :
      μ S ≤ ENNReal.ofReal ((∫ x, X x ∂ μ) / a) := by
    have h_ofReal :
        ENNReal.ofReal ((μ S).toReal) ≤ ENNReal.ofReal ((∫ x, X x ∂ μ) / a) :=
      ENNReal.ofReal_le_ofReal htoReal
    -- rewrite `ofReal (toReal (μ S)) = μ S` since μ S ≠ ⊤
    simpa [ENNReal.ofReal_toReal hμS_ne_top] using h_ofReal

  simpa [S] using hμS_le


lemma markov_inequality_exp_prob
  {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
  (Z : α → ℝ) (hZ : 0 ≤ᵐ[μ] Z)
  (a : ℝ) (ha : 0 < a)
  (hZ_meas : Measurable Z)
  (hZ_int : Integrable Z μ) :
  μ {x | a ≤ Z x} ≤ ENNReal.ofReal ((∫ x, Z x ∂ μ) / a) := by
  exact markov_inequality_exp (μ := μ) (X := Z) hZ a ha hZ_meas hZ_int



/-!
## 7. Chernoff tail bound (Eq. 123-125) and “success probability” conversion
-/

theorem exp_tail_of_moment_le_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (Z : α → ℝ)
    (hZ_meas : Measurable Z)
    (hExp_int : Integrable (fun a => Real.exp (Z a)) μ)
    (ς : ℝ) :
    0 < ς →
    (∫ a, Real.exp (Z a) ∂ μ) ≤ 1 →
    μ {a | Z a ≥ Real.log (1 / ς)} ≤ ENNReal.ofReal ς := by
  /-
  Proof sketch:
  * Apply Markov's inequality to the nonnegative random variable `exp(Z a)`:
      μ{ a | exp(Z a) ≥ exp(log(1/ς)) } ≤ (∫ exp(Z) dμ) / exp(log(1/ς)).
  * Use monotonicity of `Real.exp` to rewrite the event:
      `{Z ≥ log(1/ς)} = {exp(Z) ≥ exp(log(1/ς))}`.
  * Simplify `exp(log(1/ς)) = 1/ς` using `h : 0 < ς`.
  * With the hypothesis `∫ exp(Z) dμ ≤ 1`, conclude the bound `≤ ς`.
  * A clean formalization will likely require adding `Measurable Z` (so the event is measurable)
    and an integrability condition ensuring the real integral is well-behaved.
  -/
  intro hςpos hmoment
  have hprob : μ Set.univ = 1 := by
    simpa using (IsProbabilityMeasure.measure_univ (μ := μ))

  -- nonneg a.e. for exp(Z)
  have hnonneg : 0 ≤ᵐ[μ] fun a => Real.exp (Z a) := by
    filter_upwards with a
    exact le_of_lt (Real.exp_pos (Z a))

  have ha : 0 < (1 / ς) := one_div_pos.2 hςpos

  have hμ_univ : μ Set.univ = 1 := by
    simpa using (IsProbabilityMeasure.measure_univ (μ := μ))

  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    -- μ univ < ⊤ since μ univ = 1
    simpa [hμ_univ] using (one_lt_top : (1 : ENNReal) < ⊤)

 -- Markov on `exp(Z)` at threshold `1/ς`
  have hMarkov :
      μ {a | (1 / ς) ≤ Real.exp (Z a)}
        ≤ ENNReal.ofReal ((∫ a, Real.exp (Z a) ∂ μ) / (1 / ς)) :=
    markov_inequality_exp_prob
      (μ := μ)
      (Z := fun a => Real.exp (Z a))
      (hZ := by
        filter_upwards with a
        exact le_of_lt (Real.exp_pos (Z a)))
      (a := (1 / ς)) (ha := ha)
      (hZ_meas := by measurability)
      (hZ_int := hExp_int)

  have hsubset :
      {a | Z a ≥ Real.log (1 / ς)} ⊆ {a | (1 / ς) ≤ Real.exp (Z a)} := by
    intro a haZ
    have haZ' : Real.log (1 / ς) ≤ Z a := by
      -- unpack membership
      have : Z a ≥ Real.log (1 / ς) := by simpa [Set.mem_setOf_eq] using haZ
      simpa [ge_iff_le] using this
    -- your successful trick:
    have : (1 / ς) ≤ Real.exp (Z a) := (Real.log_le_iff_le_exp ha).mp haZ'
    simpa using this

  have h1 :
      μ {a | Z a ≥ Real.log (1 / ς)}
        ≤ ENNReal.ofReal ((∫ a, Real.exp (Z a) ∂ μ) / (1 / ς)) :=
    le_trans (measure_mono hsubset) hMarkov

  -- bound RHS using hmoment ≤ 1
  have hdiv :
      ((∫ a, Real.exp (Z a) ∂ μ) / (1 / ς))
        = (∫ a, Real.exp (Z a) ∂ μ) * ς := by
    field_simp [hςpos.ne']  -- uses ς ≠ 0

  have hbound_real :
      ((∫ a, Real.exp (Z a) ∂ μ) / (1 / ς)) ≤ ς := by
    have : (∫ a, Real.exp (Z a) ∂ μ) * ς ≤ (1 : ℝ) * ς :=
      mul_le_mul_of_nonneg_right hmoment (le_of_lt hςpos)
    simpa [hdiv] using this

  have h2 :
      ENNReal.ofReal ((∫ a, Real.exp (Z a) ∂ μ) / (1 / ς))
        ≤ ENNReal.ofReal ς :=
    ENNReal.ofReal_le_ofReal hbound_real

  exact le_trans h1 h2

-- That caused `exp_tail_of_moment_le_one` to have unsolved goals:
--μ {a | Z a ≥ Real.log (1 / ς)} ≤ ENNReal.ofReal ς

theorem compl_ge_of_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (ς : ℝ) :
    0 ≤ ς →
    μ A ≤ ENNReal.ofReal ς →
    ς ≤ 1 →
    μ Aᶜ ≥ ENNReal.ofReal (1 - ς) := by
  /-
  Proof sketch:
  * The intended application is with `0 ≤ ς ≤ 1` and with `A` measurable.
  * Use either the exact complement formula (for measurable sets under finite measure):
      μ(Aᶜ) = μ(univ) - μ(A) = 1 - μ(A),
    or the weaker inequality from subadditivity:
      μ(univ) ≤ μ(A) + μ(Aᶜ)  ⇒  1 - μ(A) ≤ μ(Aᶜ).
  * Combine with `μ(A) ≤ ofReal ς` and monotonicity of `ofReal` on `[0,1]` to get
      `ofReal (1-ς) ≤ μ(Aᶜ)`.
  * Note: as stated, this lemma assumes only `ς ≤ 1`; for a correct proof we will want
    to assume `0 ≤ ς` (or `0 < ς`) as well, which is satisfied in the main theorem.
  -/
  intro hς0 hA hς1
  have huniv : μ Set.univ = (1 : ENNReal) := by
    simpa using (IsProbabilityMeasure.measure_univ (μ := μ))

  -- Let A' be a measurable hull of A with the same measure.
  let A' : Set α := toMeasurable μ A
  have hAA' : A ⊆ A' := subset_toMeasurable (μ := μ) A
  have hmeasA' : MeasurableSet A' := measurableSet_toMeasurable (μ := μ) A
  have hμA' : μ A' = μ A := measure_toMeasurable (μ := μ) A

  -- From A ⊆ A' we get A'ᶜ ⊆ Aᶜ, hence μ(Aᶜ) ≥ μ(A'ᶜ).
  have hcomp_mono : μ A'ᶜ ≤ μ Aᶜ := by
    exact measure_mono (Set.compl_subset_compl.2 hAA')

  -- Show μ A' ≠ ⊤ (since μ A' ≤ μ univ = 1).
  have hA'_ne_top : μ A' ≠ ⊤ := by
    have : μ A' ≤ μ Set.univ := measure_mono (Set.subset_univ A')
    have : μ A' ≤ (1 : ENNReal) := by simpa [huniv] using this
    exact measure_ne_top μ A'

  -- Complement formula for measurable A'
  have hcompl : μ A'ᶜ = μ Set.univ - μ A' :=
    measure_compl hmeasA' hA'_ne_top

  -- Use μ univ = 1 and μ A' = μ A
  have hcompl' : μ A'ᶜ = (1 : ENNReal) - μ A := by
    calc
      μ A'ᶜ = μ Set.univ - μ A' := hcompl
      _     = (1 : ENNReal) - μ A' := by simpa [huniv]
      _     = (1 : ENNReal) - μ A := by simpa [hμA']

  -- From μ A ≤ ofReal ς, monotonicity of `tsub` in the subtrahend:
  have htsub : (1 : ENNReal) - ENNReal.ofReal ς ≤ (1 : ENNReal) - μ A :=
    tsub_le_tsub_left hA 1

  -- Rewrite (1 - ofReal ς) as ofReal(1-ς) using ofReal_sub (needs 0 ≤ ς).
  have hrewrite :
      (1 : ENNReal) - ENNReal.ofReal ς = ENNReal.ofReal ((1 : ℝ) - ς) := by
    -- `ofReal_sub` in your build wants `0 ≤ ς`
    have : ENNReal.ofReal ((1 : ℝ) - ς) = ENNReal.ofReal (1 : ℝ) - ENNReal.ofReal ς := by
      simpa using (ENNReal.ofReal_sub (p := (1 : ℝ)) (q := ς) hς0)
    -- flip sides and simp `ofReal 1 = 1`
    simpa using this.symm

  -- Combine everything:
  -- μ Aᶜ ≥ μ A'ᶜ = 1 - μ A ≥ 1 - ofReal ς = ofReal(1-ς)
  have : ENNReal.ofReal ((1 : ℝ) - ς) ≤ μ Aᶜ := by
    calc
      ENNReal.ofReal ((1 : ℝ) - ς)
          = (1 : ENNReal) - ENNReal.ofReal ς := by simpa [hrewrite]
      _   ≤ (1 : ENNReal) - μ A := htsub
      _   = μ A'ᶜ := by simpa [hcompl']
      _   ≤ μ Aᶜ := hcomp_mono
  simpa using this

/-!
## 8. Theorem 4 (Eq. 116 / Eq. 126)
-/

theorem theorem4_pacbayes_terminal_cost
    {X : Type*} [MeasurableSpace X]
    {Ω : Type*} [MeasurableSpace Ω]
    (X1 : Ω → X) (hX1 : Measurable X1)  -- the terminal-time evaluation map is measurable.
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : KLFinite (Ω := Ω) P Q)
    (gTilde : X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ε ς : ℝ) (hε : 0 < ε) (hς : 0 < ς ∧ ς < 1)
    (n : ℕ) (hn : 0 < n)
    (hgTilde_meas : Measurable gTilde) :
    let g : X → ℝ := clipped C gTilde
    let P1 : Measure X := terminalMarginal X1 P
    let μS : Measure (Fin n → X) := iidsampleMeasure P1 n
    let R : ℝ := popMean P1 g
    let r : (Fin n → X) → ℝ := empMean n g
    let quad : ℝ := ε * C^2 / (2 * (n : ℝ))
    μS {s | R ≤ r s + (KLReal (Ω := Ω) P Q + Real.log (1 / ς)) / ε + quad}
      ≥ ENNReal.ofReal (1 - ς) := by
  classical
  intro g P1 μS R r quad

  -- Step 0: measurability + boundedness of clipped g (Eq. 115).
  have hg_meas : Measurable g := by
    simpa [g] using measurable_clipped (gTilde := gTilde) (C := C) hgTilde_meas
  have hg_bd : ∀ x, |g x| ≤ C := by
    simpa [g] using abs_clipped_le (gTilde := gTilde) (C := C) hC

  -- Step A (Eq. 122): exponential-moment inequality (≤ 1).
  let Z : (Fin n → X) → ℝ :=
    fun s =>
      ε * (R - r s) - KLReal (Ω := Ω) P Q - (ε^2 * C^2) / (2 * (n : ℝ))

  -- P1 = P.map X1 is a probability measure (paper: “terminal marginal P₁”)
  haveI : IsProbabilityMeasure P1 := by
    simpa [P1, terminalMarginal] using
      (terminalMarginal_isProbability (X1 := X1) (P := P) hX1)

  have hr_meas : Measurable r := by
    classical
    -- each coordinate map s ↦ g (s i) is measurable
    have hg_i : ∀ i : Fin n, Measurable (fun s : Fin n → X => g (s i)) :=
      fun i => hg_meas.comp (measurable_pi_apply i)

    -- the Fintype sum is measurable
    have hsum : Measurable (fun s : Fin n → X => ∑ i : Fin n, g (s i)) := by
      exact Finset.measurable_sum Finset.univ fun i a ↦ hg_i i

    -- scale by constant (1/n)
    -- adjust `empMean` unfolding if your definition differs
    simpa [r, empMean] using (measurable_const.mul hsum)

  have hr_bounded : ∀ s : Fin n → X, |r s| ≤ C := by
    classical
    intro s
    -- you likely have `hn : 0 < n` (Nat) in scope
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    -- |∑ g| ≤ ∑ |g|
    have hsum_abs :
        |∑ i : Fin n, g (s i)| ≤ ∑ i : Fin n, |g (s i)| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin n)))
          (f := fun i => g (s i)))
    -- ∑ |g| ≤ ∑ C
    have hsum_le :
        (∑ i : Fin n, |g (s i)|) ≤ ∑ i : Fin n, C := by
      -- `Finset.sum_le_sum` expects a proof per element of `univ`
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
          (fun i hi => hg_bd (s i)))
    -- Now combine
    calc
      |r s|
          = |(1 / (n : ℝ)) * (∑ i : Fin n, g (s i))| := by
              simp [r, empMean]
      _   = (1 / (n : ℝ)) * |∑ i : Fin n, g (s i)| := by
              simp [abs_mul, abs_of_pos (one_div_pos.2 hnpos), mul_assoc, mul_left_comm, mul_comm]
      _   ≤ (1 / (n : ℝ)) * (∑ i : Fin n, |g (s i)|) := by
              exact mul_le_mul_of_nonneg_left hsum_abs (le_of_lt (one_div_pos.2 hnpos))
      _   ≤ (1 / (n : ℝ)) * (∑ i : Fin n, C) := by
              exact mul_le_mul_of_nonneg_left hsum_le (le_of_lt (one_div_pos.2 hnpos))
      _   = C := by
              -- `∑ i : Fin n, C = n * C`, then cancel `(1/n) * (n*C) = C`
              simp [Finset.sum_const, Finset.card_univ, hn0]

  have hr_int : Integrable r μS := by
    -- measurability → a.e. measurability
    have hr_ae : AEStronglyMeasurable r μS :=
      (hr_meas.aestronglyMeasurable)  -- if you have `hr_meas : Measurable r`

    -- bound in norm a.e.
    have hbound : ∀ᵐ s ∂ μS, ‖r s‖ ≤ C := by
      filter_upwards with s
      -- ‖·‖ on ℝ is abs
      simpa [Real.norm_eq_abs] using hr_bounded s

    -- constant C is integrable under probability measure
    have hC_int : Integrable (fun _ : Fin n → X => (C : ℝ)) μS := by
      simpa using (integrable_const (C : ℝ))

    -- now apply the standard lemma:
    -- (if this name doesn't resolve, tell me the exact missing name and I’ll swap it)
    exact Integrable.mono' hC_int hr_ae hbound

  have hZ_int : Integrable Z μS := by
    -- constants are integrable under a probability measure
    have hR_int : Integrable (fun _ : Fin n → X => R) μS := by
      simpa using (integrable_const R)
    have hKL_int : Integrable (fun _ : Fin n → X => KLReal (Ω := Ω) P Q) μS := by
      simpa using (integrable_const (KLReal (Ω := Ω) P Q))
    have hquad_int :
        Integrable (fun _ : Fin n → X => (ε^2 * C^2) / (2 * (n : ℝ))) μS := by
      simpa using (integrable_const ((ε^2 * C^2) / (2 * (n : ℝ))))
    -- R - r is integrable
    have hRminus : Integrable (fun s => R - r s) μS := hR_int.sub hr_int
    -- ε*(R - r) is integrable
    have hmul : Integrable (fun s => ε * (R - r s)) μS := hRminus.const_mul ε
    -- goal: Integrable Z μS
    dsimp [Z]
    -- goal is now the expanded expression, exactly matching the term below
    exact (hmul.sub hKL_int).sub hquad_int

  have hZ_meas : Measurable Z := by
    -- Z s = ε * (R - r s) - KLReal P Q - const
    -- `R`, `KLReal P Q`, and the quadratic term are constants in `s`.
    -- now let the `measurability` tactic do the algebra
    -- it knows measurability is closed under add/sub/mul with constants
    measurability

  have hR_abs : |R| ≤ C := by
    -- Make sure g is integrable under the probability measure P1
    haveI : IsFiniteMeasure P1 := by infer_instance
    have hg_aesm : AEStronglyMeasurable g P1 := hg_meas.aestronglyMeasurable
    have hg_bound : ∀ᵐ x ∂P1, ‖g x‖ ≤ C := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      simpa [Real.norm_eq_abs] using hg_bd x
    have hg_int : Integrable g P1 :=
      MeasureTheory.Integrable.of_bound hg_aesm C hg_bound

    -- |∫ g| ≤ ∫ |g|
    have h1 : |∫ x, g x ∂P1| ≤ ∫ x, |g x| ∂P1 := by
      simpa using (MeasureTheory.abs_integral_le_integral_abs (f := g) (μ := P1))

    -- ∫ |g| ≤ ∫ C = C
    have hAbs_int : Integrable (fun x => |g x|) P1 := hg_int.abs
    have hConst_int : Integrable (fun _ : X => (C : ℝ)) P1 := integrable_const (C : ℝ)
    have hle_ae : (fun x => |g x|) ≤ᵐ[P1] (fun _ => (C : ℝ)) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      exact hg_bd x
    have h2 : (∫ x, |g x| ∂P1) ≤ ∫ x, (C : ℝ) ∂P1 :=
      MeasureTheory.integral_mono_ae hAbs_int hConst_int hle_ae

    have h3 : (∫ x, (C : ℝ) ∂P1) = C := by
      simp

    -- combine and rewrite R
    simpa [R, popMean, h3] using (le_trans h1 (by simpa [h3] using h2))

  have hZ_upper : ∀ s, Z s ≤ ε * (2 * C) := by
    intro s

    have hKL_nonneg : 0 ≤ KLReal (Ω := Ω) P Q := by
      -- KLReal = (ENNReal).toReal, always ≥ 0
      simp [KLReal, KLinf]

    have hquad_nonneg :
        0 ≤ (ε^2 * C^2) / (2 * (n : ℝ)) := by
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hden : 0 < (2 * (n : ℝ)) := by nlinarith
      have hnum : 0 ≤ ε^2 * C^2 := by nlinarith
      exact div_nonneg hnum (le_of_lt hden)

    -- R - r s ≤ 2C from |R|≤C and |r s|≤C
    have hR_le : R ≤ C := le_trans (le_abs_self R) hR_abs
    have hr_ge : -C ≤ r s := (abs_le.mp (hr_bounded s)).1
    have hRR : R - r s ≤ 2 * C := by
      linarith

    -- Now: Z s = ε*(R-r s) - KL - quad ≤ ε*(R-r s) ≤ ε*(2C)
    have hε_nonneg : 0 ≤ ε := le_of_lt hε

    calc
      Z s
          = ε * (R - r s) - KLReal (Ω := Ω) P Q - (ε^2 * C^2) / (2 * (n : ℝ)) := by
              rfl
      _   ≤ ε * (R - r s) := by
              linarith [hKL_nonneg, hquad_nonneg]
      _   ≤ ε * (2 * C) := by
              exact mul_le_mul_of_nonneg_left hRR hε_nonneg

  have hExp_int : Integrable (fun s => Real.exp (Z s)) μS := by
    haveI : IsFiniteMeasure μS := by infer_instance
    have hAesm :
        AEStronglyMeasurable (fun s => Real.exp (Z s)) μS :=
      (Real.measurable_exp.comp hZ_meas).aestronglyMeasurable
    refine MeasureTheory.Integrable.of_bound hAesm (Real.exp (ε*(2*C))) ?_
    refine Filter.Eventually.of_forall ?_
    intro s
    have : Real.exp (Z s) ≤ Real.exp (ε*(2*C)) :=
      Real.exp_le_exp.mpr (hZ_upper s)
    -- turn into a norm bound (norm = abs = itself since exp ≥ 0)
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _))] using this

  have hMoment : (∫ s, Real.exp (Z s) ∂ μS) ≤ 1 := by
    simpa [Z, μS, R, r, g, P1, terminalMarginal, iidsampleMeasure, popMean, empMean,
      R_of, r_of]
      using
        (pacBayes_exp_moment_eq122 (P1 := P1) (g := g) (C := C) (ε := ε) (ς := ς) (n := n)
          hn hC hε hg_meas hg_bd P Q hKL)

  -- Step B (Eq. 123-125): Chernoff tail bound.
  let bad : Set (Fin n → X) := {s | Z s ≥ Real.log (1 / ς)}
  have hBad : μS bad ≤ ENNReal.ofReal ς := by
    simpa [bad] using
      (exp_tail_of_moment_le_one (μ := μS) (Z := Z) (hZ_meas : Measurable Z) (hExp_int := hExp_int) (ς := ς) hς.1 hMoment)

  -- Step C: Convert to a good-event probability lower bound.
  have hGood : μS badᶜ ≥ ENNReal.ofReal (1 - ς) := by
    have hς0 : 0 ≤ ς := le_of_lt hς.1
    have hςle1 : ς ≤ 1 := le_of_lt hς.2
    exact compl_ge_of_le (μ := μS) (A := bad) (ς := ς) hς0 hBad hςle1

  -- Step D (Eq. 126): algebraic rearrangement and set inclusion.
  have hSubset :
      badᶜ ⊆ {s | R ≤ r s + (KLReal (Ω := Ω) P Q + Real.log (1 / ς)) / ε + quad} := by
    intro s hs
    have hs_bad : ¬ (Z s ≥ Real.log (1 / ς)) := by
      simpa [bad] using hs
    have hsZ : Z s < Real.log (1 / ς) := lt_of_not_ge hs_bad
    dsimp [Z] at hsZ

    -- Rearrange the strict inequality into the desired ≤ bound (divide by ε>0).
    have h1 :
        ε * (R - r s)
          < KLReal (Ω := Ω) P Q + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / ς) := by
      linarith

    have h2 :
        (R - r s)
          < (KLReal (Ω := Ω) P Q + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / ς)) / ε := by
      have : (R - r s) * ε
              < KLReal (Ω := Ω) P Q + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / ς) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h1
      exact (lt_div_iff₀ hε).2 this

    have h2le :
        (R - r s)
          ≤ (KLReal (Ω := Ω) P Q + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / ς)) / ε :=
      le_of_lt h2

    -- Split the numerator over `ε` without rewriting logs.
    have hsplit :
        (KLReal (Ω := Ω) P Q + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / ς)) / ε
          =
        (KLReal (Ω := Ω) P Q + Real.log (1 / ς)) / ε
          + ((ε^2 * C^2) / (2 * (n : ℝ))) / ε := by
      -- IMPORTANT: avoid `simp` here (it may rewrite `log (1/ς)` as `-log ς`).
      have hnum :
          KLReal (Ω := Ω) P Q + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / ς)
            =
          (KLReal (Ω := Ω) P Q + Real.log (1 / ς))
            + (ε^2 * C^2) / (2 * (n : ℝ)) := by
        ac_rfl
      calc
        (KLReal (Ω := Ω) P Q + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / ς)) / ε
            = ((KLReal (Ω := Ω) P Q + Real.log (1 / ς)) + (ε^2 * C^2) / (2 * (n : ℝ))) / ε := by
                rw [hnum]
        _   = (KLReal (Ω := Ω) P Q + Real.log (1 / ς)) / ε
                + ((ε^2 * C^2) / (2 * (n : ℝ))) / ε := by
                rw [add_div]

    have hmain :
        R ≤ r s
            + (KLReal (Ω := Ω) P Q + Real.log (1 / ς)) / ε
            + ((ε^2 * C^2) / (2 * (n : ℝ))) / ε := by
      -- turn `h2le` into a `≤` statement about `R` by adding `r s` and rewriting via `hsplit`.
      have htmp :
          R - r s ≤
            (KLReal (Ω := Ω) P Q + (ε^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / ς)) / ε :=
        h2le
      -- rewrite the RHS using `hsplit` (no `simp` to avoid rewriting `log (1/ς)`).
      rw [hsplit] at htmp
      -- now add `r s` to both sides
      linarith

    have hQuad :
        ((ε^2 * C^2) / (2 * (n : ℝ))) / ε = quad := by
      dsimp [quad]
      have hε0 : ε ≠ 0 := ne_of_gt hε
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      field_simp [hε0, hn0]

    simpa [hQuad] using hmain

  have hMono :
      μS badᶜ ≤
        μS {s | R ≤ r s + (KLReal (Ω := Ω) P Q + Real.log (1 / ς)) / ε + quad} :=
    measure_mono hSubset
  exact le_trans hGood hMono

section PaperTheorem4Wrapper

variable {X : Type*} [MeasurableSpace X]
variable {Ω : Type*} [MeasurableSpace Ω]

variable (X1 : Ω → X) (hX1 : Measurable X1)
variable (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- The terminal marginal `P₁` as a pushforward measure. -/
noncomputable def P1 : Measure X := Measure.map X1 P

/-- If `P` is a probability measure, then its pushforward `P₁` is too. -/
noncomputable instance P1.instIsProbabilityMeasure :
    IsProbabilityMeasure (P1 (X1 := X1) (P := P)) := by
  classical
  refine ⟨by
    simp [P1, Measure.map_apply, hX1]⟩

/--
Paper-faithful Theorem 4 wrapper:

Same bound, but `KL(P‖Q)` is now *definitionally* `KLinf P Q` (Option 1),
and we assume it is finite so it can appear as a real number in Eq. (116).
-/

theorem theorem4_paper_form
  -- The terminal-time evaluation map ω ↦ X₁(ω) is measurable, so the terminal marginal P₁ = (X₁)#P is well-defined.
  (hX1 : Measurable X1)
  -- Loss/terminal-cost function g; clipping/scale bound C; PAC-Bayes tuning ε; failure probability δ; sample size n.
  (g : X → ℝ) (C ε δ : ℝ) (n : ℕ)
  -- Positivity conditions needed for (1/n) and division by ε, and for log(1/δ) to be meaningful.
  (hn : 0 < n) (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 < δ ∧ δ < 1)
  -- KL(P‖Q) is finite (not ⊤), so its real-valued coercion `KLReal P Q` is the intended divergence term.
  (hKL : KLFinite (Ω := Ω) P Q)
  -- g is measurable and uniformly bounded by C, enabling Hoeffding-style concentration and mgf bounds.
  (hg_meas : Measurable g) (hg_bd : ∀ x, |g x| ≤ C)
  :
  -- μ is the terminal marginal distribution P₁ of the controlled path measure P.
  let μ : Measure X := P1 (X1 := X1) (P := P)
  -- μn is the law of an i.i.d. sample S = (X₁¹,…,X₁ⁿ) drawn from μ = P₁ (product measure).
  let μn := iidsampleMeasure μ n
  -- R is the population mean (true risk): R = E_{X~μ}[g(X)].
  let R  := popMean μ g
  -- r(s) is the empirical mean on a sample s: r(s) = (1/n)∑ᵢ g(sᵢ).
  let r  := empMean n g
  -- The bounded-difference/Hoeffding quadratic term that appears after optimizing the mgf parameterization.
  let quad : ℝ := ε * C^2 / (2 * (n : ℝ))
  -- The “good event”: for the realized sample `s`, the true mean `R = E[g(X)]` under the terminal marginal
  -- is at most the empirical mean `r s` plus a complexity penalty `(KL(P‖Q) + log(1/δ))/ε` and the bounded-loss
  -- concentration term `ε C^2/(2n) = quad`.
  -- The theorem claims this event occurs with probability at least `1 - δ` over an i.i.d. draw `s ~ μn`.
  μn {s | R ≤ r s + (KLReal (Ω := Ω) P Q + Real.log (1 / δ)) / ε + quad} ≥ ENNReal.ofReal (1 - δ)
    := by
  classical
  intro μ μn R r quad

  -- Since `g` is already bounded by `C`, clipping at `C` leaves it unchanged.
  have hclip : clipped C g = g :=
    clipped_eq_self_of_abs_le (g := g) (C := C) hC hg_bd

  -- Apply the clipped theorem with `gTilde := g` and rewrite away the clipping.
  simpa [μ, μn, R, r, quad, P1, terminalMarginal, hclip] using
    (theorem4_pacbayes_terminal_cost (X1 := X1) (hX1 := hX1) (P := P) (Q := Q) (hKL := hKL)
      (gTilde := g) (C := C) (hC := hC)
      (ε := ε) (ς := δ) (hε := hε) (hς := hδ)
      (n := n) (hn := hn) (hgTilde_meas := hg_meas))

end PaperTheorem4Wrapper

end TwoPagerPACBayes
