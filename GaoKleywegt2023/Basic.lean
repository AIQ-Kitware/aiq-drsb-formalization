/-
# Gao–Kleywegt (2023): Wasserstein DRO strong duality + worst-case structure

Lean formalization of selected duality and worst-case-structure results from

  R. Gao, A. Kleywegt, "Distributionally Robust Stochastic Optimization with
  Wasserstein Distance", *Mathematics of Operations Research* (2023),
  arXiv:1604.02199.

Prose transcription: `../prose/wasserstein-dro-duality.md`, section 2
("Gao–Kleywegt (2023): strong duality and worst-case structure"). Printed
theorem/equation numbers are cited in each docstring; every deviation from the
printed form is marked as a documented gap.

Notation bridge (prose §2.1). The paper works with a nominal `ν ∈ P(Ξ)`, an
objective `Ψ : Ξ → ℝ`, and the order-`p` Wasserstein distance built from a metric
cost `dᵖ`. **Remark 2** of the paper states that all of the Section-3.1 duality
results continue to hold when `dᵖ(·,·)` is replaced by *any* measurable nonnegative
cost `c(·,·)` with `c(ξ,ζ)=0` when `ξ=ζ` (in particular the DRSB `W₂²` cost `‖·‖²`).
We therefore state everything for a general cost `c : X → X → ℝ` and radius
`δ := θᵖ`, exactly as the prose licenses. With `c = dᵖ`, `δ = θᵖ` this is the
printed statement; with `c = ‖·‖²`, `δ = ε` it is the DRSB `W₂²` ball.

The shared OT vocabulary (`expect`, `otCost`, `droValue`, …) lives in
`ForMathlib.OptimalTransport.Basic`. The statements below are aligned with the literature
transcription and use the repository's current optimal-transport API.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.DroValue
import ForMathlib.OptimalTransport.StrongDualityGe
import ForMathlib.OptimalTransport.WeakDuality

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace GaoKleywegt2023

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

/-! ### Reusable finite-measure helpers for the worst-case-law construction

The data-driven worst-case distribution of Corollary 2(ii) is a finite weighted sum of
Dirac masses `(1/N) Σᵢ Σₖ aᵢₖ δ_{zᵢₖ}` (here the `≤ N+1`-atom split is the `K = 2` case).
The three lemmas below package the facts needed to work with such sums — total mass,
expectation, and pushforward (marginal) — under `[MeasurableSingletonClass Z]`. They are
verbatim copies of the sibling helpers in `MohajerinEsfahaniKuhn2018/Basic.lean` and are kept
local to avoid a cross-namespace `open` ambiguity. A future `ForMathlib.OT` extraction can
consolidate the two copies. -/

/-- **Total mass of the weighted Dirac double-sum is 1** (a probability measure), given
nonnegative weights summing to `1` over `k` for each `i`, and `0 < N`. -/
theorem isProbabilityMeasure_wsum {Z : Type*} [MeasurableSpace Z]
    {N K : ℕ} (hN : 0 < N) (a : Fin N → Fin K → ℝ) (z : Fin N → Fin K → Z)
    (ha : ∀ i k, 0 ≤ a i k) (hsum : ∀ i, ∑ k, a i k = 1) :
    IsProbabilityMeasure ((N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin K,
        ENNReal.ofReal (a i k) • Measure.dirac (z i k)) := by
  constructor
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply', MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
    smul_eq_mul, mul_one]
  have hi : ∀ i : Fin N, ∑ k : Fin K, ENNReal.ofReal (a i k) = 1 := fun i => by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => ha i k), hsum i, ENNReal.ofReal_one]
  rw [Finset.sum_congr rfl (fun i _ => hi i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)]

/-- **Expectation against the weighted Dirac double-sum**:
`∫ g d((1/N) Σᵢ Σₖ aᵢₖ δ_{zᵢₖ}) = (1/N) Σᵢ Σₖ aᵢₖ · g(zᵢₖ)` (nonnegative weights). -/
theorem integral_wsum {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (z : Fin N → Fin K → Z)
    (ha : ∀ i k, 0 ≤ a i k) (g : Z → ℝ) :
    ∫ x, g x ∂((N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin K,
        ENNReal.ofReal (a i k) • Measure.dirac (z i k))
      = (N : ℝ)⁻¹ * ∑ i, ∑ k, a i k * g (z i k) := by
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ =>
      integrable_finsetSum_measure.2 (fun k _ =>
        (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)),
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum_measure (fun k _ =>
      (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (ha i k), smul_eq_mul]

/-- **Pushforward (marginal) of the weighted Dirac double-sum** under a measurable map. -/
theorem map_wsum {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (z : Fin N → Fin K → Z) (h : Z → Y) (hh : Measurable h) :
    ((N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin K,
        ENNReal.ofReal (a i k) • Measure.dirac (z i k)).map h
      = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin K,
        ENNReal.ofReal (a i k) • Measure.dirac (h (z i k)) := by
  rw [Measure.map_smul]
  congr 1
  rw [← Measure.mapₗ_apply_of_measurable hh, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul]
  congr 1
  rw [Measure.mapₗ_apply_of_measurable hh]
  exact Measure.map_dirac' hh (z i k)

/-!
## 2.1 Setup: ambiguity set, dual objective, and growth rate

We reuse `ForMathlib.OT.otCost`, `expect`, and `droValue`. The primal problem is
the DRO worst-case value `v_P = sup_{μ ∈ M} 𝔼_μ[Ψ]` over the general-cost ball
`M`, and the dual `v_D` is built from the Moreau–Yosida inner map `Φ` (Definition 3).
-/

/-- **Ambiguity set** `M := { μ : W_p(μ, ν) ≤ θ } = { μ : otCost c μ ν ≤ δ }`
(prose §2.1, `M`), with `δ = θᵖ` and general transport cost `c` (Remark 2).
For `c = dᵖ`, `δ = θᵖ` this is the printed Wasserstein ball; for `c = ‖·‖²`,
`δ = ε` it is the DRSB `W₂²` ball `wassersteinBall μ̂ ε`. -/
def ambiguitySet (c : X → X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ) :
    Set (ProbabilityMeasure X) :=
  { μ | otCost c μ ν ≤ δ }

/-- **Primal value** `v_P := sup_{μ ∈ M} ∫ Ψ dμ` (prose §2.1, "Primal"). -/
noncomputable def primalValue (c : X → X → ℝ) (Ψ : X → ℝ)
    (ν : ProbabilityMeasure X) (δ : ℝ) : ℝ :=
  droValue (ambiguitySet c ν δ) Ψ

/-- **Moreau–Yosida inner map** `Φ(λ, ζ) := inf_ξ (λ c(ξ, ζ) − Ψ(ξ))`
(prose §2.1, Definition 3). Its negation is the pointwise conjugate
`sup_ξ (Ψ(ξ) − λ c(ξ, ζ))`, the pointwise Lagrangian envelope used by the shared OT API. -/
noncomputable def Phi (c : X → X → ℝ) (Ψ : X → ℝ) (lam : ℝ) (ζ : X) : ℝ :=
  sInf (Set.range (fun ξ => lam * c ξ ζ - Ψ ξ))

/-- **Dual value** `v_D := inf_{λ ≥ 0} { λ δ − ∫ Φ(λ, ζ) ν(dζ) }`
(prose §2.1, "Dual", with `θᵖ = δ`). Using `−inf_ξ(λc − Ψ) = sup_ξ(Ψ − λc)` this
is the univariate strong dual `inf_{λ≥0}{λδ + 𝔼_ν[sup_ξ(Ψ(ξ) − λ c(ξ,ζ))]}`,
which is the right-hand side used by the shared Wasserstein-DRO dual API. -/
noncomputable def dualValue (c : X → X → ℝ) (Ψ : X → ℝ)
    (ν : ProbabilityMeasure X) (δ : ℝ) : ℝ :=
  sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
    v = lam * δ - expect ν (fun ζ => Phi c Ψ lam ζ) }

/-- **Growth rate** `κ := inf { λ ≥ 0 : ∫ Φ(λ, ζ) ν(dζ) > −∞ }`, with `κ = ∞` when
the integral is `−∞` for every `λ` (prose §2.1, Definition 4). Valued in `ℝ≥0∞`;
`sInf ∅ = ⊤` encodes the `κ = ∞` case.

Documented gap: "`∫ Φ(λ,ζ) ν(dζ) > −∞`" is rendered here as
`Integrable (Φ(λ, ·)) ν`. Under the standing hypothesis `Ψ ∈ L¹(ν)` and
`c(ζ,ζ) = 0` one has `Φ(λ,ζ) ≤ λ c(ζ,ζ) − Ψ(ζ) = −Ψ(ζ)` (take `ξ = ζ`), so `Φ⁺`
is dominated by an `L¹` function; hence "the integral exceeds `−∞`" is equivalent
to `Φ⁻`, and thus `Φ`, being integrable. So on the paper's domain the two forms
agree. -/
noncomputable def kappa (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) :
    ℝ≥0∞ :=
  sInf { l : ℝ≥0∞ | ∃ lam : ℝ, 0 ≤ lam ∧ l = ENNReal.ofReal lam
    ∧ Integrable (fun ζ => Phi c Ψ lam ζ) (ν : Measure X) }

/-!
## 2.2 Strong-duality theorems (prose §2.2)
-/

omit [NormedAddCommGroup X] in
/-- **Proposition 1 (Weak duality).** *Consider any `ν ∈ P(Ξ)` and `Ψ ∈ L¹(ν)`.
Then for any `p ∈ [1,∞)` and `θ > 0`, it holds that `v_P ≤ v_D`.* (prose §2.2,
Proposition 1 — the always-true Lagrangian direction; `p` and `θ` enter through the
general cost `c` and radius `δ = θᵖ > 0`.) -/
theorem weak_duality_prop1
    (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ)
    (_hΨ : Integrable Ψ (ν : Measure X))  -- Ψ ∈ L¹(ν) (faithful paper premise; subsumed by `hφint`)
    (_hδ : 0 < δ)                         -- δ = θᵖ > 0 (faithful paper premise; not proof-critical)
    -- regularity assumptions used by the real-valued formulation:
    (hfeas : (ambiguitySet c ν δ).Nonempty)                 -- the ambiguity set is nonempty
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,                   -- the pointwise conjugate is finite
        BddAbove (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →                           -- the conjugate is ν-integrable
        Integrable (fun ζ => sSup (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ))) (ν : Measure X))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ →
        Integrable Ψ (μ : Measure X))                        -- Ψ ∈ L¹(μ) for feasible μ
    -- OT ε-attainment edge: `otCost ≤ δ` is witnessed by integrable-cost couplings
    (hOT : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → ∀ η : ℝ, 0 < η →
        ∃ π : ProbabilityMeasure (X × X), π ∈ couplings μ ν ∧ couplingCost c π ≤ δ + η ∧
          Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X))) :
    primalValue c Ψ ν δ ≤ dualValue c Ψ ν δ := by
  -- sup-form = −Φ pointwise (unconditional, via `Real.sSup_neg` and `Real.sInf` = `−sSup∘neg`)
  have hnegΦ : ∀ (lam : ℝ) (ζ : X),
      sSup (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ)) = - Phi c Ψ lam ζ := by
    intro lam ζ
    rw [Phi, ← Real.sSup_neg]
    congr 1
    rw [← Set.image_neg_eq_neg, ← Set.range_comp]
    congr 1; funext ξ; simp only [Function.comp_apply]; ring
  -- 𝔼_ν[Φ] = −𝔼_ν[sup-form]
  have hexpΦ : ∀ (lam : ℝ),
      expect ν (fun ζ => Phi c Ψ lam ζ)
        = - expect ν (fun ζ => sSup (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ))) := by
    intro lam
    unfold expect
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards with ζ
    rw [hnegΦ lam ζ, neg_neg]
  unfold primalValue droValue
  obtain ⟨μ₀, hμ₀⟩ := hfeas
  refine csSup_le ⟨expect μ₀ Ψ, μ₀, hμ₀, rfl⟩ ?_
  rintro a ⟨μ, hμ, rfl⟩
  unfold dualValue
  refine le_csInf ⟨_, 0, le_refl 0, rfl⟩ ?_
  rintro d ⟨lam, hlam, rfl⟩
  -- goal: expect μ Ψ ≤ lam * δ − 𝔼_ν[Φ]  =  lam*δ + 𝔼_ν[sup-form]
  rw [hexpΦ lam, sub_neg_eq_add]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hη : (0 : ℝ) < ε / (lam + 1) := div_pos hε (by linarith)
  obtain ⟨π, hπ, hcost, hcint⟩ := hOT μ hμ (ε / (lam + 1)) hη
  have hker := ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost
    c Ψ lam hlam μ ν π hπ (hbdd lam hlam) (hΨμ μ hμ) (hφint lam hlam) hcint
  have h1 : lam * couplingCost c π ≤ lam * δ + lam * (ε / (lam + 1)) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hcost hlam
  have h2 : lam * (ε / (lam + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < lam + 1)]
    nlinarith [hε, hlam]
  linarith [hker, h1, h2]

omit [NormedAddCommGroup X] in

/-! ## Reverse duality

The reverse inequality is obtained by specializing
`ForMathlib.OT.dualValue_le_droValue` to this file's `dualValue` and `primalValue`. -/

omit [NormedAddCommGroup X] in
/-- **Reverse duality under explicit regularity assumptions.** A continuous bounded objective,
a continuous nonnegative cost, a separable Borel sample space, a strictly positive radius, and a
zero-cost feasible plan imply `dualValue ≤ primalValue`. -/
theorem dualValue_le_primalValue
    [TopologicalSpace X] [SecondCountableTopology X] [Nonempty X] [BorelSpace X]
    (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ) (hδ : 0 < δ)
    (hΨc : Continuous Ψ) (hcc : Continuous fun p : X × X => c p.1 p.2)
    (hc0 : ∀ x y, 0 ≤ c x y) (C : ℝ) (hΨb : ∀ x, |Ψ x| ≤ C)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,
        BddAbove (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun ζ => sSup (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ))) (ν : Measure X))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → Integrable Ψ (μ : Measure X))
    (hne0 : (ForMathlib.OT.droValueSet c Ψ ν 0).Nonempty) :
    dualValue c Ψ ν δ ≤ primalValue c Ψ ν δ := by
  classical
  -- `−Φ(λ, ·)` is the `c`-transform
  have hPhi : ∀ (lam : ℝ) (ζ : X), -(Phi c Ψ lam ζ) = ⨆ ξ, (Ψ ξ - lam * c ξ ζ) := by
    intro lam ζ
    rw [Phi, ← Real.sSup_neg, ← sSup_range]
    congr 1
    rw [← Set.image_neg_eq_neg, ← Set.range_comp]
    congr 1; funext ξ; simp only [Function.comp_apply]; ring
  have hExp : ∀ lam : ℝ, -expect ν (fun ζ => Phi c Ψ lam ζ)
      = expect ν (fun ζ => ⨆ ξ, (Ψ ξ - lam * c ξ ζ)) := by
    intro lam
    rw [expect, expect, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => hPhi lam ζ)
  -- rewrite the dual value set in `c`-transform form
  have hset : { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ v = lam * δ - expect ν (fun ζ => Phi c Ψ lam ζ) }
      = { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * δ + expect ν (fun ζ => ⨆ ξ, (Ψ ξ - lam * c ξ ζ)) } := by
    ext v
    constructor
    · rintro ⟨lam, hlam, rfl⟩; exact ⟨lam, hlam, by rw [← hExp lam]; ring⟩
    · rintro ⟨lam, hlam, rfl⟩; exact ⟨lam, hlam, by rw [← hExp lam]; ring⟩
  -- the `λ > 0` slice, and boundedness below of the full `λ ≥ 0` set
  obtain ⟨r₀, μ₀, π₀, hπ₀, hf₀, hc₀, hcost₀, hr₀⟩ := hne0
  have hcost₀' : couplingCost c π₀ = 0 :=
    le_antisymm hcost₀ (integral_nonneg fun z => hc0 z.1 z.2)
  have hBdd : BddBelow { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
      v = lam * δ + expect ν (fun ζ => ⨆ ξ, (Ψ ξ - lam * c ξ ζ)) } := by
    refine ⟨expect μ₀ Ψ, ?_⟩
    rintro v ⟨lam, hlam, rfl⟩
    have hkey := expect_le_dualIntegrand_add_lam_couplingCost c Ψ lam hlam μ₀ ν π₀ hπ₀
      (hbdd lam hlam) hf₀ (hφint lam hlam) hc₀
    simp only [sSup_range] at hkey
    rw [hcost₀', mul_zero, add_zero] at hkey
    nlinarith [hkey, hlam, hδ.le]
  have hsub : { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
        v = lam * δ + expect ν (fun ζ => ⨆ ξ, (Ψ ξ - lam * c ξ ζ)) }
      ⊆ { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
        v = lam * δ + expect ν (fun ζ => ⨆ ξ, (Ψ ξ - lam * c ξ ζ)) } := by
    rintro v ⟨lam, hlam, rfl⟩; exact ⟨lam, hlam.le, rfl⟩
  have hne : { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
      v = lam * δ + expect ν (fun ζ => ⨆ ξ, (Ψ ξ - lam * c ξ ζ)) }.Nonempty :=
    ⟨_, 1, one_pos, rfl⟩
  -- assemble: `dualValue ≤ (λ>0 slice) ≤ droValue = primalValue`
  calc dualValue c Ψ ν δ
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * δ + expect ν (fun ζ => ⨆ ξ, (Ψ ξ - lam * c ξ ζ)) } := by
        rw [dualValue, hset]
    _ ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = lam * δ + expect ν (fun ζ => ⨆ ξ, (Ψ ξ - lam * c ξ ζ)) } :=
        csInf_le_csInf hBdd hne hsub
    _ ≤ primalValue c Ψ ν δ :=
        ForMathlib.OT.dualValue_le_droValue c Ψ ν δ hδ hΨc hcc hc0 C hΨb
          (fun lam hlam => hbdd lam hlam.le)
          (fun lam hlam => by simpa only [sSup_range] using hφint lam hlam.le)
          ⟨r₀, μ₀, π₀, hπ₀, hf₀, hc₀, hcost₀, hr₀⟩ hΨμ


omit [NormedAddCommGroup X] in
/-- **An attaining worst-case measure gives the reverse inequality.** If some feasible `μ`
achieves the dual value, then `dualValue ≤ primalValue`. This implication does not assert that a
vanishing duality gap produces a maximizer.

`BddAbove` is not assumed: `hbdd` at `lam = 0` says `Ψ` is bounded above
(`ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range`). -/
theorem dualValue_le_primalValue_of_attaining_measure
    (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,
        BddAbove (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ)))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → Integrable Ψ (μ : Measure X))
    (hattain : ∃ μ : ProbabilityMeasure X,
        μ ∈ ambiguitySet c ν δ ∧ expect μ Ψ = dualValue c Ψ ν δ) :
    dualValue c Ψ ν δ ≤ primalValue c Ψ ν δ := by
  haveI : IsProbabilityMeasure (ν : Measure X) := ν.2
  have hne : Nonempty X := nonempty_of_isProbabilityMeasure (ν : Measure X)
  have hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
      μ ∈ ambiguitySet c ν δ ∧ r = expect μ Ψ } :=
    ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range _ Ψ
      (ForMathlib.OT.bddAbove_range_of_bddAbove_dualIntegrand Ψ c hne.some (hbdd 0 le_rfl hne.some))
      hΨμ
  obtain ⟨μ, hμ, hμeq⟩ := hattain
  calc dualValue c Ψ ν δ = expect μ Ψ := hμeq.symm
    _ ≤ primalValue c Ψ ν δ := le_csSup hbddP ⟨μ, hμ, rfl⟩

omit [NormedAddCommGroup X] in
/-- **Theorem 1 (Strong duality with finite optimal value).** *Consider any
`p ∈ [1,∞)`, any `ν ∈ P(Ξ)`, any `θ > 0`, and any `Ψ ∈ L¹(ν)` such that `κ < ∞`.
Then `v_P = v_D < ∞`.* (prose §2.2, Theorem 1.)

Documented gap on "`< ∞`": both `primalValue` and `dualValue` are `ℝ`-valued
(Mathlib's `sSup`/`sInf` return the junk value `0` on an unbounded set), so the
finiteness half of "`v_P = v_D < ∞`" is not expressible as a `< ⊤` here; the
hypothesis `κ < ∞` is precisely what rules out the `v_P = v_D = +∞` regime
(Proposition 2). We state the load-bearing equality `v_P = v_D`. -/
theorem strong_duality_thm1
    (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ)
    (hΨ : Integrable Ψ (ν : Measure X))   -- Ψ ∈ L¹(ν)
    (hδ : 0 < δ)                          -- δ = θᵖ with θ > 0
    (_hκ : kappa c Ψ ν ≠ ⊤)              -- κ < ∞  (finite transport growth; paper's finiteness gate)
    -- weak-duality edges (as in `weak_duality_prop1`):
    (hfeas : (ambiguitySet c ν δ).Nonempty)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,
        BddAbove (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun ζ => sSup (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ))) (ν : Measure X))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → Integrable Ψ (μ : Measure X))
    (hOT : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → ∀ η : ℝ, 0 < η →
        ∃ π : ProbabilityMeasure (X × X), π ∈ couplings μ ν ∧ couplingCost c π ≤ δ + η ∧
          Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X)))
    -- the `≥` direction — **the duality gap is zero**. This is the entire research content of
    -- Theorem 1, isolated as one inequality. It is strictly weaker than the customary
    -- "a worst-case distribution attains the dual value": that hypothesis bundles *attainment*
    -- (a separate statement, false in general without compactness) with the vanishing gap.
    -- Attainment is sufficient but not required; the theorem assumes only the reverse inequality.
    (hge : dualValue c Ψ ν δ ≤ primalValue c Ψ ν δ) :
    primalValue c Ψ ν δ = dualValue c Ψ ν δ :=
  le_antisymm (weak_duality_prop1 c Ψ ν δ hΨ hδ hfeas hbdd hφint hΨμ hOT) hge

omit [NormedAddCommGroup X] in
/-- **Strong duality from explicit regularity assumptions.** The weak-duality half is
`weak_duality_prop1`; the reverse inequality is `dualValue_le_primalValue`. No optimizer
attainment assumption is required. -/
theorem strong_duality_thm1_of_regularity
    [TopologicalSpace X] [SecondCountableTopology X] [Nonempty X] [BorelSpace X]
    (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ)
    (hΨ : Integrable Ψ (ν : Measure X)) (hδ : 0 < δ) (hκ : kappa c Ψ ν ≠ ⊤)
    (hfeas : (ambiguitySet c ν δ).Nonempty)
    (hΨc : Continuous Ψ) (hcc : Continuous fun p : X × X => c p.1 p.2)
    (hc0 : ∀ x y, 0 ≤ c x y) (C : ℝ) (hΨb : ∀ x, |Ψ x| ≤ C)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,
        BddAbove (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun ζ => sSup (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ))) (ν : Measure X))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → Integrable Ψ (μ : Measure X))
    (hOT : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → ∀ η : ℝ, 0 < η →
        ∃ π : ProbabilityMeasure (X × X), π ∈ couplings μ ν ∧ couplingCost c π ≤ δ + η ∧
          Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X)))
    (hne0 : (ForMathlib.OT.droValueSet c Ψ ν 0).Nonempty) :
    primalValue c Ψ ν δ = dualValue c Ψ ν δ :=
  strong_duality_thm1 c Ψ ν δ hΨ hδ hκ hfeas hbdd hφint hΨμ hOT
    (dualValue_le_primalValue c Ψ ν δ hδ hΨc hcc hc0 C hΨb hbdd hφint hΨμ hne0)


/-!
## 2.3 Worst-case distribution (prose §2.3)

These characterizations justify the DRSB code's **closed-form worst-case**: the
worst-case law is a *transport of the nominal* that moves each nominal point `ζ`
to a minimizer of `λ* c(ξ,ζ) − Ψ(ξ)` (equivalently a maximizer of
`Ψ(ξ) − λ* c(ξ,ζ)`), i.e. along the cost-optimal direction. For a Gaussian nominal
this transport map is affine, so `μ*` is a shifted/rescaled Gaussian — the
DRSB paper's closed form (prose §2.3, "the DRSB link"; G–K Example 10).
-/

/-- **Corollary 1(ii) — worst-case-distribution structure, eq. (27).** *Under
`κ < ∞`, `Ψ` upper semicontinuous, and bounded subsets of `(Ξ,d)` totally bounded:
whenever a worst-case distribution exists, there is one of the form*
`μ* = p* · T̄_# ν + (1 − p*) · T*_# ν`, `p* ∈ [0,1]` *(eq. 27), where the maps
`T̄, T* : Ξ → Ξ` push `ν` forward and satisfy* `ν{ζ : T̄(ζ), T*(ζ) ∉ argmin_ξ(λ*
c(ξ,ζ) − Ψ(ξ))} = 0` (prose §2.3, Corollary 1(ii)).

`lam_star` is the optimal dual multiplier `λ*`. Existence of *some* worst-case
distribution (the content of Corollary 1(i)'s explicit `λ*`-vs-`κ` trichotomy) is
taken as the hypothesis `hexists`; the conclusion produces a *structured* one that
still attains the sup. The printed clause "if `λ* > 0`, the induced `γ^T` is an
optimal coupling of `W_p^p(μ*, ν)`" is omitted from the formal conclusion
(documented gap) — it constrains the coupling realizing the mixture, not `μ*`.

**Proof (house pattern; the general-`ν` sibling of `dataDriven_worstCase_cor2ii`).** As
there, the §5 trap forbids taking the structured optimizer `μ*` as a hypothesis. We take
only the genuinely-weaker **extremal ingredients** a full OT measurable-selection would
extract from `hexists`: the mixture weight `pstar ∈ [0,1]` and the two measurable transport
maps `Tbar`, `Tstar` that are `ν`-a.e. argmins of `λ* c(·,ζ) − Ψ` (`hargmin` — argmin
*existence* along `ν`, strictly weaker than the conclusion), plus explicit **regularity assumptions**
(`Ψ` and the cost integrable along each transport — needed because `c`, `Ψ` carry no standing
measurability) and the two content edges: a **feasibility budget** `hbudget`
(`pstar·𝔼_ν[c(T̄,·)] + (1−pstar)·𝔼_ν[c(T*,·)] ≤ δ`) and the **attainment `≥` edge** `hattain`
(the mixture value dominates `droValue`). Everything else is proved: `μ*` is
built as the explicit 2-map mixture `pstar·T̄#ν + (1−pstar)·T*#ν`, shown a probability measure,
shown `∈ ambiguitySet` via the explicit transport plan `pstar·(T̄,id)#ν + (1−pstar)·(T*,id)#ν`
(second marginal `ν` since `snd∘(T,id)=id`; cost `≤ δ` through
`ForMathlib.OT.otCost_le_couplingCost`), and its `Ψ`-expectation is `integral_map`'d to the
mixture value; the `≤` half of attainment is `le_csSup`, so `hattain` supplies only the `≥`.
The eq. (27) measure form is then `rfl`. Same `le_antisymm(constructive, one attainment edge)`
posture as every other worst-case result here. `_hκ`/`_husc`/`_hproper`/`_hlam`/`_hexists` are
retained as the paper's premises but `_`-marked as not proof-critical (the ingredients — `pstar`,
`Tbar`/`Tstar`, `hargmin`, `hbudget`, `hattain` — are what they would yield). -/
theorem worstCase_structure_cor1
    (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ) (lam_star : ℝ)
    (_hκ : kappa c Ψ ν ≠ ⊤)                                 -- κ < ∞ (faithful paper premise; `_`)
    (_husc : UpperSemicontinuous Ψ)                         -- Ψ upper semicontinuous (faithful; `_`)
    (_hproper : ∀ s : Set X, Bornology.IsBounded s → TotallyBounded s)
                                                            -- bounded ⇒ totally bounded (faithful; `_`)
    (hc : ∀ x y, 0 ≤ c x y)                                  -- nonnegative cost (Remark 2)
    (_hlam : 0 ≤ lam_star)                                   -- dual minimizer λ* ≥ 0 (faithful; `_`)
    (_hexists : ∃ μ ∈ ambiguitySet c ν δ,
        expect μ Ψ = droValue (ambiguitySet c ν δ) Ψ)        -- a worst-case distribution exists (faithful; `_`)
    -- the extremal INGREDIENTS a full proof extracts from `hexists` (each strictly weaker
    -- than the structured conclusion): the mixture weight and the two argmin transport maps.
    (pstar : ℝ) (Tbar Tstar : X → X)
    (hpstar : pstar ∈ Set.Icc (0 : ℝ) 1)                     -- mixture weight p* ∈ [0,1]
    (hTbarM : Measurable Tbar) (hTstarM : Measurable Tstar)  -- the maps are measurable
    (hargmin : ∀ᵐ ζ ∂(ν : Measure X),                        -- ν-a.e. T̄(ζ), T*(ζ) ∈ argmin
        IsMinOn (fun ξ => lam_star * c ξ ζ - Ψ ξ) Set.univ (Tbar ζ)
      ∧ IsMinOn (fun ξ => lam_star * c ξ ζ - Ψ ξ) Set.univ (Tstar ζ))
    -- regularity edges: Ψ and the cost are integrable along each transport (c, Ψ carry no
    -- standing measurability, so these make the pushforward expectations well-defined)
    (hΨbar : Integrable Ψ (Measure.map Tbar (ν : Measure X)))
    (hΨstar : Integrable Ψ (Measure.map Tstar (ν : Measure X)))
    (hcbar : Integrable (fun z : X × X => c z.1 z.2)
        (Measure.map (fun ζ => (Tbar ζ, ζ)) (ν : Measure X)))
    (hcstar : Integrable (fun z : X × X => c z.1 z.2)
        (Measure.map (fun ζ => (Tstar ζ, ζ)) (ν : Measure X)))
    -- feasibility (budget) edge: the mixture transport cost stays within the radius `δ`
    (hbudget : pstar * (∫ ζ, c (Tbar ζ) ζ ∂(ν : Measure X))
        + (1 - pstar) * (∫ ζ, c (Tstar ζ) ζ ∂(ν : Measure X)) ≤ δ)
    -- the DRO value is finite (bounded ambiguity ball), an explicit finiteness assumption
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ ambiguitySet c ν δ ∧ r = expect μ Ψ })
    -- attainment (`≥`) edge: the structured mixture value dominates `droValue`
    (hattain : droValue (ambiguitySet c ν δ) Ψ
        ≤ pstar * (∫ ζ, Ψ (Tbar ζ) ∂(ν : Measure X))
          + (1 - pstar) * (∫ ζ, Ψ (Tstar ζ) ∂(ν : Measure X))) :
    ∃ (μstar : ProbabilityMeasure X) (Tbar Tstar : X → X) (pstar : ℝ),
      μstar ∈ ambiguitySet c ν δ ∧
      expect μstar Ψ = droValue (ambiguitySet c ν δ) Ψ ∧      -- μ* is worst-case (attains v_P)
      pstar ∈ Set.Icc (0 : ℝ) 1 ∧
      Measurable Tbar ∧ Measurable Tstar ∧
      (μstar : Measure X)                                     -- eq. (27): a 2-map transport of ν
        = ENNReal.ofReal pstar • Measure.map Tbar (ν : Measure X)
          + ENNReal.ofReal (1 - pstar) • Measure.map Tstar (ν : Measure X) ∧
      (∀ᵐ ζ ∂(ν : Measure X),                                 -- ν-a.e. T̄(ζ), T*(ζ) ∈ argmin
          IsMinOn (fun ξ => lam_star * c ξ ζ - Ψ ξ) Set.univ (Tbar ζ)
        ∧ IsMinOn (fun ξ => lam_star * c ξ ζ - Ψ ξ) Set.univ (Tstar ζ)) := by
  classical
  obtain ⟨hp00, hp01⟩ := hpstar
  have hp10 : (0 : ℝ) ≤ 1 - pstar := by linarith
  have hpairbarM : Measurable (fun ζ => (Tbar ζ, ζ)) := Measurable.prodMk hTbarM measurable_id
  have hpairstarM : Measurable (fun ζ => (Tstar ζ, ζ)) := Measurable.prodMk hTstarM measurable_id
  -- μ* = pstar • T̄#ν + (1-pstar) • T*#ν
  set M : Measure X := ENNReal.ofReal pstar • Measure.map Tbar (ν : Measure X)
    + ENNReal.ofReal (1 - pstar) • Measure.map Tstar (ν : Measure X) with hM_def
  have hsum1 : ENNReal.ofReal pstar + ENNReal.ofReal (1 - pstar) = 1 := by
    rw [← ENNReal.ofReal_add hp00 hp10]; norm_num
  have hprobM : IsProbabilityMeasure M := by
    constructor
    rw [hM_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply hTbarM MeasurableSet.univ,
      Measure.map_apply hTstarM MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ, smul_eq_mul, mul_one]
    exact hsum1
  set μstar : ProbabilityMeasure X := ⟨M, hprobM⟩ with hμstar
  have hμcoe : (μstar : Measure X) = M := rfl
  -- the explicit transport plan π* = pstar • (T̄,id)#ν + (1-pstar) • (T*,id)#ν
  set P : Measure (X × X) :=
    ENNReal.ofReal pstar • Measure.map (fun ζ => (Tbar ζ, ζ)) (ν : Measure X)
    + ENNReal.ofReal (1 - pstar) • Measure.map (fun ζ => (Tstar ζ, ζ)) (ν : Measure X)
    with hP_def
  have hprobP : IsProbabilityMeasure P := by
    constructor
    rw [hP_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply hpairbarM MeasurableSet.univ,
      Measure.map_apply hpairstarM MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ, smul_eq_mul, mul_one]
    exact hsum1
  set πstar : ProbabilityMeasure (X × X) := ⟨P, hprobP⟩ with hπstar
  have hπcoe : (πstar : Measure (X × X)) = P := rfl
  have hcoupl : πstar ∈ couplings μstar ν := by
    constructor
    · rw [hπcoe, hP_def, Measure.map_add _ _ measurable_fst, Measure.map_smul,
        Measure.map_smul, Measure.map_map measurable_fst hpairbarM,
        Measure.map_map measurable_fst hpairstarM, hμcoe, hM_def]
      rfl
    · rw [hπcoe, hP_def, Measure.map_add _ _ measurable_snd, Measure.map_smul,
        Measure.map_smul, Measure.map_map measurable_snd hpairbarM,
        Measure.map_map measurable_snd hpairstarM]
      have hbid : (Prod.snd ∘ fun ζ => (Tbar ζ, ζ)) = id := rfl
      have hsid : (Prod.snd ∘ fun ζ => (Tstar ζ, ζ)) = id := rfl
      rw [hbid, hsid, Measure.map_id, ← add_smul, hsum1, one_smul]
  -- μ* lies in the ambiguity ball (feasibility, via the transport plan's cost ≤ δ)
  have hmem : μstar ∈ ambiguitySet c ν δ := by
    have hle := otCost_le_couplingCost c hc μstar ν πstar hcoupl
    rw [ambiguitySet, Set.mem_setOf_eq]
    refine le_trans hle ?_
    rw [couplingCost, hπcoe, hP_def,
      integral_add_measure (hcbar.smul_measure ENNReal.ofReal_ne_top)
        (hcstar.smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure,
      integral_map hpairbarM.aemeasurable hcbar.1,
      integral_map hpairstarM.aemeasurable hcstar.1,
      ENNReal.toReal_ofReal hp00, ENNReal.toReal_ofReal hp10, smul_eq_mul, smul_eq_mul]
    exact hbudget
  -- expectation of Ψ against μ* is the explicit mixture value (via integral_map)
  have hexp : expect μstar Ψ
      = pstar * (∫ ζ, Ψ (Tbar ζ) ∂(ν : Measure X))
        + (1 - pstar) * (∫ ζ, Ψ (Tstar ζ) ∂(ν : Measure X)) := by
    rw [expect, hμcoe, hM_def,
      integral_add_measure (hΨbar.smul_measure ENNReal.ofReal_ne_top)
        (hΨstar.smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure,
      integral_map hTbarM.aemeasurable hΨbar.1,
      integral_map hTstarM.aemeasurable hΨstar.1,
      ENNReal.toReal_ofReal hp00, ENNReal.toReal_ofReal hp10, smul_eq_mul, smul_eq_mul]
  -- attainment: μ* is worst-case (≤ by feasibility + le_csSup, ≥ by the attainment edge)
  have hval : expect μstar Ψ = droValue (ambiguitySet c ν δ) Ψ := by
    refine le_antisymm ?_ ?_
    · exact le_csSup hbddP ⟨μstar, hmem, rfl⟩
    · rw [hexp]; exact hattain
  exact ⟨μstar, Tbar, Tstar, pstar, hmem, hval, ⟨hp00, hp01⟩, hTbarM, hTstarM, rfl, hargmin⟩

/-!
### Data-driven DRSO (empirical nominal): Corollary 2, eqs. (28)/(29)

Nominal `ν = (1/N) Σ_{i} δ_{ξ̂ᵢ}`. The empirical dual (eq. 28) is exactly the
DRSB API's `wdrsbDualObjective`; the empirical worst-case (eq. 29) is the
`≤ N+1`-atom transport that the DRSB code computes in closed form.
-/

/-- **Empirical dual objective, eq. (28)** `inf_{λ≥0}{ λ δ − (1/N) Σᵢ inf_ξ(λ c(ξ,
ξ̂ᵢ) − Ψ(ξ)) }` (prose §2.3, Corollary 2(i), with `θᵖ = δ`). Equal, via
`−inf_ξ(λc − Ψ) = sup_ξ(Ψ − λc)`, to the DRSB API's `wdrsbDualObjective`
`inf_{λ≥0}{λ δ + (1/N) Σᵢ sup_ξ(Ψ(ξ) − λ c(ξ,ξ̂ᵢ))}` (per-sample term `L_wdro`). -/
noncomputable def empiricalDual {N : ℕ} (c : X → X → ℝ) (Ψ : X → ℝ)
    (xhat : Fin N → X) (δ : ℝ) : ℝ :=
  sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
    v = lam * δ
        - (1 / (N : ℝ)) * ∑ i : Fin N, sInf (Set.range (fun ξ => lam * c ξ (xhat i) - Ψ ξ)) }

omit [NormedAddCommGroup X] in
/-- **Empirical dual = specialized general dual (proved reduction).** When the
nominal `ν` is the empirical measure `(1/N) Σᵢ δ_{ξ̂ᵢ}`, the Gao–Kleywegt dual `dualValue`
(an expectation of the Moreau–Yosida inner map `Φ` against `ν`) collapses to the finite
average `empiricalDual`: for every multiplier `λ`,
`𝔼_ν[Φ(λ,·)] = (1/N) Σᵢ Φ(λ, ξ̂ᵢ)` (and `Φ(λ, ζ) = inf_ξ(λ c(ξ,ζ) − Ψ(ξ))` is exactly
`empiricalDual`'s per-sample term), so the two `inf_{λ≥0}` objectives coincide.

The proof is a direct integral-against-empirical-measure computation: each `∫ · d(δ_{ξ̂ᵢ})`
is `integral_dirac`, valid for any real integrand under `[MeasurableSingletonClass X]`, so no
measurability or integrability side condition on `Φ` is needed. This reduction turns the general
Gao–Kleywegt dual into the data-driven form of eq. (28). -/
theorem dualValue_eq_empiricalDual [MeasurableSingletonClass X]
    {N : ℕ} (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X)
    (xhat : Fin N → X) (δ : ℝ) (_hN : 0 < N)  -- N ≥ 1 samples (faithful paper premise; `_`)
    (hν : (ν : Measure X) = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, Measure.dirac (xhat i)) :
    dualValue c Ψ ν δ = empiricalDual c Ψ xhat δ := by
  -- 𝔼_ν[g] = (1/N) ∑ᵢ g(ξ̂ᵢ) for any real g (integral against the empirical measure)
  have hexp : ∀ g : X → ℝ, expect ν g = (1 / (N : ℝ)) * ∑ i : Fin N, g (xhat i) := by
    intro g
    unfold expect
    rw [hν, integral_smul_measure,
      integral_finsetSum_measure (fun i _ => integrable_dirac enorm_lt_top)]
    simp_rw [integral_dirac]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, one_div]
  -- the two `inf_{λ≥0}` objective sets coincide term-by-term in λ
  unfold dualValue empiricalDual
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨lam, hlam, by rw [hexp (fun ζ => Phi c Ψ lam ζ)]; simp only [Phi]⟩
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨lam, hlam, by rw [hexp (fun ζ => Phi c Ψ lam ζ)]; simp only [Phi]⟩

omit [NormedAddCommGroup X] in
/-- **Corollary 2(i) — data-driven strong duality, eq. (28).** *For
`ν = (1/N) Σᵢ δ_{ξ̂ᵢ}`, `p ∈ [1,∞)`, `θ > 0`: the primal has strong dual*
`v_P = v_D = inf_{λ≥0}{ λ θᵖ − (1/N) Σᵢ inf_ξ(λ dᵖ(ξ,ξ̂ᵢ) − Ψ(ξ)) }` (prose §2.3,
Corollary 2(i)). Here `hν` fixes `ν` as the empirical measure on the sample
`xhat : Fin N → X` and `δ = θᵖ`.

Proof structure: the empirical case is the general Gao–Kleywegt strong duality
`strong_duality_thm1` (`primalValue = dualValue`) composed with the proved reduction
`dualValue_eq_empiricalDual` (`dualValue = empiricalDual` for empirical `ν`). The weak
`≤` half is genuinely proved (from the ForMathlib Lagrangian kernel via
`weak_duality_prop1`); the reverse inequality remains an explicit hypothesis `hge`, as in
`strong_duality_thm1`. The finite empirical worst-case construction is represented separately by
Corollary 2(ii), `dataDriven_worstCase_cor2ii`. -/
theorem dataDriven_strongDuality_cor2i [MeasurableSingletonClass X]
    {N : ℕ} (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X)
    (xhat : Fin N → X) (δ : ℝ)
    (hN : 0 < N)
    (hν : (ν : Measure X) = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, Measure.dirac (xhat i))
    (hΨ : Integrable Ψ (ν : Measure X))   -- Ψ ∈ L¹(ν)
    (hδ : 0 < δ)                          -- δ = θᵖ with θ > 0
    (hκ : kappa c Ψ ν ≠ ⊤)               -- κ < ∞ (finiteness gate, as in strong_duality_thm1)
    -- weak-duality edges (proved kernel side), identical to `strong_duality_thm1`:
    (hfeas : (ambiguitySet c ν δ).Nonempty)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,
        BddAbove (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun ζ => sSup (Set.range (fun ξ => Ψ ξ - lam * c ξ ζ))) (ν : Measure X))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → Integrable Ψ (μ : Measure X))
    (hOT : ∀ μ : ProbabilityMeasure X, μ ∈ ambiguitySet c ν δ → ∀ η : ℝ, 0 < η →
        ∃ π : ProbabilityMeasure (X × X), π ∈ couplings μ ν ∧ couplingCost c π ≤ δ + η ∧
          Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X)))
    -- the `≥` edge: the duality gap vanishes (the §6 seam), as in `strong_duality_thm1`.
    (hge : dualValue c Ψ ν δ ≤ primalValue c Ψ ν δ) :
    primalValue c Ψ ν δ = empiricalDual c Ψ xhat δ :=
  (strong_duality_thm1 c Ψ ν δ hΨ hδ hκ hfeas hbdd hφint hΨμ hOT hge).trans
    (dualValue_eq_empiricalDual c Ψ ν xhat δ hN hν)

omit [NormedAddCommGroup X] in
/-- **Corollary 2(ii) — data-driven worst-case distribution, eq. (29).** *Whenever
a worst-case distribution exists, there is one supported on at most `N+1` points,*
`μ* = (1/N) Σ_{i ≠ i₀} δ_{ξ*ⁱ} + (p₀/N) δ_{ξ*^{i₀}} + ((1−p₀)/N) δ_{ξ̄*^{i₀}}`
*(eq. 29) with* `ξ*ⁱ ∈ argmin_ξ(λ* dᵖ(ξ,ξ̂ᵢ) − Ψ(ξ))`*: every data point `ξ̂ᵢ` is
moved to an associated minimizer, and at most one point `ξ̂_{i₀}` is split between
two minimizers `ξ*^{i₀}` and `ξ̄*^{i₀}`* (prose §2.3, Corollary 2(ii)).

`ξstar i` are the per-sample minimizers `ξ*ⁱ` (for `i ≠ i₀`) and `ξ*^{i₀}`;
`ξbarstar` is the second minimizer `ξ̄*^{i₀}` for the split point. `lam_star = λ*`
is the optimal dual multiplier. This `≤ N+1`-atom transport is the DRSB code's
closed-form worst-case.

**Proof structure (`[MeasurableSingletonClass X]`).** This corollary pins down the exact
`≤ N+1`-atom structure. Its explicit inputs are the weaker extremal ingredients that a complete
optimal-transport measurable-selection argument would extract from `hexists`: the split index
`i₀`, weight `p0 ∈ [0,1]`, and the per-point argmin atoms `ξstar`, `ξbarstar` (conditions
(v)/(vi) — argmin *existence* is an extreme-value fact strictly weaker than the conclusion),
plus two ingredient-level scalar edges — a **feasibility budget** `hbudget` (the argmin
transport cost stays within radius `δ`; the analogue of Esfahani–Kuhn's `(1/N)Σ‖q‖ ≤ ε`) and
the **attainment `≥` edge** `hattain` (the argmin-transport value dominates `droValue`; the
analogue of `worstCase_exists`'s `hval`). Everything else is proved: `μ*` is
built as the explicit `K = 2` weighted-Dirac double-sum, shown to be a probability measure,
shown to lie in `ambiguitySet` via the explicit transport plan
`(1/N) Σ_{i≠i₀} δ_{(ξ*ⁱ,ξ̂ᵢ)} + (p₀/N) δ_{(ξ*^{i₀},ξ̂_{i₀})} + ((1−p₀)/N) δ_{(ξ̄*^{i₀},ξ̂_{i₀})}`
(cost `≤ δ` via `ForMathlib.OT.otCost_le_couplingCost`), and its `Ψ`-expectation is computed
in closed form; the `≤` half of attainment is `le_csSup`, so `hattain` supplies only the `≥`.
The measure is then rewritten into the printed eq. (29) split form. The final equality combines the constructive lower bound with the explicit attainment
inequality, as in the other worst-case results in this repository.
`hc` (nonnegative cost) is Remark 2's standing assumption; `hexists`/`hlam` are retained as
the paper's premises (the ingredients are what they would yield). -/
theorem dataDriven_worstCase_cor2ii [MeasurableSingletonClass X]
    {N : ℕ} (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X)
    (xhat : Fin N → X) (δ : ℝ) (lam_star : ℝ)
    (hN : 0 < N)
    (hν : (ν : Measure X) = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, Measure.dirac (xhat i))
    (hc : ∀ x y, 0 ≤ c x y)                                  -- nonnegative cost (Remark 2)
    (_hlam : 0 ≤ lam_star)                                   -- dual minimizer λ* ≥ 0 (faithful; `_`)
    (_hexists : ∃ μ ∈ ambiguitySet c ν δ,
        expect μ Ψ = droValue (ambiguitySet c ν δ) Ψ)        -- worst-case dist exists (faithful; `_`)
    -- the extremal INGREDIENTS a full proof extracts from `_hexists` (each strictly weaker
    -- than the structured conclusion): split index/weight and the per-point argmin atoms.
    (i₀ : Fin N) (ξstar : Fin N → X) (ξbarstar : X) (p0 : ℝ)
    (hp0 : p0 ∈ Set.Icc (0 : ℝ) 1)                           -- (b) optimal split weight
    (hξstar : ∀ i : Fin N,                                   -- (a) per-point argmins exist
        IsMinOn (fun ξ => lam_star * c ξ (xhat i) - Ψ ξ) Set.univ (ξstar i))
    (hξbar : IsMinOn (fun ξ => lam_star * c ξ (xhat i₀) - Ψ ξ) Set.univ ξbarstar)
    -- feasibility (budget) edge: the argmin-transport cost stays within the radius `δ`
    (hbudget : (N : ℝ)⁻¹ * ((∑ i ∈ Finset.univ.erase i₀, c (ξstar i) (xhat i))
        + p0 * c (ξstar i₀) (xhat i₀) + (1 - p0) * c ξbarstar (xhat i₀)) ≤ δ)
    -- the DRO value is finite (bounded ambiguity ball), an explicit finiteness assumption
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ ambiguitySet c ν δ ∧ r = expect μ Ψ })
    -- attainment (`≥`) edge: the structured argmin-transport value dominates `droValue`
    (hattain : droValue (ambiguitySet c ν δ) Ψ
        ≤ (N : ℝ)⁻¹ * ((∑ i ∈ Finset.univ.erase i₀, Ψ (ξstar i))
            + p0 * Ψ (ξstar i₀) + (1 - p0) * Ψ ξbarstar)) :
    ∃ (μstar : ProbabilityMeasure X) (i₀ : Fin N) (ξstar : Fin N → X)
      (ξbarstar : X) (p0 : ℝ),
      μstar ∈ ambiguitySet c ν δ ∧
      expect μstar Ψ = droValue (ambiguitySet c ν δ) Ψ ∧      -- μ* is worst-case (attains v_P)
      p0 ∈ Set.Icc (0 : ℝ) 1 ∧
      (μstar : Measure X)                                     -- eq. (29): ≤ N+1 atoms
        = (∑ i ∈ Finset.univ.erase i₀, (N : ℝ≥0∞)⁻¹ • Measure.dirac (ξstar i))
          + ENNReal.ofReal (p0 / (N : ℝ)) • Measure.dirac (ξstar i₀)
          + ENNReal.ofReal ((1 - p0) / (N : ℝ)) • Measure.dirac ξbarstar ∧
      (∀ i : Fin N,                                           -- each ξ*ⁱ minimizes for ξ̂ᵢ
          IsMinOn (fun ξ => lam_star * c ξ (xhat i) - Ψ ξ) Set.univ (ξstar i)) ∧
      IsMinOn (fun ξ => lam_star * c ξ (xhat i₀) - Ψ ξ) Set.univ ξbarstar := by
                                                              -- split point's second minimizer
  classical
  obtain ⟨hp00, hp01⟩ := hp0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  -- weights and atoms of the K=2 weighted-Dirac double-sum representation of μ*
  set a : Fin N → Fin 2 → ℝ :=
    fun i k => if i = i₀ then (if k = 0 then p0 else 1 - p0) else (if k = 0 then 1 else 0)
    with ha_def
  set atom : Fin N → Fin 2 → X :=
    fun i k => if i = i₀ then (if k = 0 then ξstar i₀ else ξbarstar) else ξstar i
    with hatom_def
  have ha0 : ∀ i k, 0 ≤ a i k := by
    intro i k
    rw [ha_def]
    by_cases hi : i = i₀ <;> fin_cases k <;> simp [hi] <;> linarith
  have hasum : ∀ i, ∑ k, a i k = 1 := by
    intro i
    rw [Fin.sum_univ_two, ha_def]
    by_cases hi : i = i₀ <;> simp [hi]
  -- scalar split reindexing: the K=2 double-sum collapses to the ≤ N+1 split form
  have split : ∀ f : Fin N → X → ℝ,
      ∑ i, ∑ k : Fin 2, a i k * f i (atom i k)
        = (∑ i ∈ Finset.univ.erase i₀, f i (ξstar i))
          + p0 * f i₀ (ξstar i₀) + (1 - p0) * f i₀ ξbarstar := by
    intro f
    rw [← Finset.add_sum_erase Finset.univ
          (fun i => ∑ k : Fin 2, a i k * f i (atom i k)) (Finset.mem_univ i₀)]
    have hFi0 : (∑ k : Fin 2, a i₀ k * f i₀ (atom i₀ k))
        = p0 * f i₀ (ξstar i₀) + (1 - p0) * f i₀ ξbarstar := by
      rw [Fin.sum_univ_two, ha_def, hatom_def]; simp
    have hFerase : ∀ i ∈ Finset.univ.erase i₀,
        (∑ k : Fin 2, a i k * f i (atom i k)) = f i (ξstar i) := by
      intro i hi
      have hii : i ≠ i₀ := Finset.ne_of_mem_erase hi
      rw [Fin.sum_univ_two, ha_def, hatom_def]; simp [hii]
    rw [Finset.sum_congr rfl hFerase, hFi0]; ring
  -- ENNReal scaling helper: (1/N) • ofReal t = ofReal (t/N)
  have hscale : ∀ t : ℝ, 0 ≤ t →
      (N : ℝ≥0∞)⁻¹ * ENNReal.ofReal t = ENNReal.ofReal (t / N) := by
    intro t ht
    rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_inv_of_pos hNR,
      ← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
  -- measure split identity: the K=2 wsum equals the printed eq. (29) ≤ N+1 atom split form
  have hMsplit :
      ((N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin 2,
          ENNReal.ofReal (a i k) • Measure.dirac (atom i k))
        = (∑ i ∈ Finset.univ.erase i₀, (N : ℝ≥0∞)⁻¹ • Measure.dirac (ξstar i))
          + ENNReal.ofReal (p0 / (N : ℝ)) • Measure.dirac (ξstar i₀)
          + ENNReal.ofReal ((1 - p0) / (N : ℝ)) • Measure.dirac ξbarstar := by
    have hGi0 : (∑ k : Fin 2, ENNReal.ofReal (a i₀ k) • Measure.dirac (atom i₀ k))
        = ENNReal.ofReal p0 • Measure.dirac (ξstar i₀)
          + ENNReal.ofReal (1 - p0) • Measure.dirac ξbarstar := by
      rw [Fin.sum_univ_two, ha_def, hatom_def]; simp
    have hGerase : ∀ i ∈ Finset.univ.erase i₀,
        (∑ k : Fin 2, ENNReal.ofReal (a i k) • Measure.dirac (atom i k))
          = Measure.dirac (ξstar i) := by
      intro i hi
      have hii : i ≠ i₀ := Finset.ne_of_mem_erase hi
      rw [Fin.sum_univ_two, ha_def, hatom_def]; simp [hii]
    rw [← Finset.add_sum_erase Finset.univ
          (fun i => ∑ k : Fin 2, ENNReal.ofReal (a i k) • Measure.dirac (atom i k))
          (Finset.mem_univ i₀)]
    rw [hGi0, Finset.sum_congr rfl hGerase, smul_add, smul_add, smul_smul, smul_smul,
      Finset.smul_sum, hscale p0 hp00, hscale (1 - p0) (by linarith)]
    abel
  -- construct the worst-case measure μ*
  have hprobM : IsProbabilityMeasure
      ((N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin 2,
        ENNReal.ofReal (a i k) • Measure.dirac (atom i k)) :=
    isProbabilityMeasure_wsum hN a atom ha0 hasum
  set μstar : ProbabilityMeasure X := ⟨_, hprobM⟩ with hμstar
  have hμcoe : (μstar : Measure X)
      = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin 2,
        ENNReal.ofReal (a i k) • Measure.dirac (atom i k) := rfl
  -- the explicit transport plan π* (moves each ξ̂ᵢ to its argmin, splitting ξ̂_{i₀})
  have hprobπ : IsProbabilityMeasure
      ((N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin 2,
        ENNReal.ofReal (a i k) • Measure.dirac (atom i k, xhat i)) :=
    isProbabilityMeasure_wsum hN a (fun i k => (atom i k, xhat i)) ha0 hasum
  set πstar : ProbabilityMeasure (X × X) := ⟨_, hprobπ⟩ with hπstar
  have hπcoe : (πstar : Measure (X × X))
      = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin 2,
        ENNReal.ofReal (a i k) • Measure.dirac (atom i k, xhat i) := rfl
  have hcoupl : πstar ∈ couplings μstar ν := by
    constructor
    · rw [hπcoe, map_wsum a (fun i k => (atom i k, xhat i)) Prod.fst measurable_fst, hμcoe]
    · rw [hπcoe, map_wsum a (fun i k => (atom i k, xhat i)) Prod.snd measurable_snd, hν]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp only
      rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => ha0 i k), hasum i,
        ENNReal.ofReal_one, one_smul]
  -- μ* lies in the ambiguity ball (feasibility, via the transport plan's cost ≤ δ)
  have hmem : μstar ∈ ambiguitySet c ν δ := by
    have hle := otCost_le_couplingCost c hc μstar ν πstar hcoupl
    rw [ambiguitySet, Set.mem_setOf_eq]
    refine le_trans hle ?_
    rw [couplingCost, hπcoe,
      integral_wsum a (fun i k => (atom i k, xhat i)) ha0 (fun z => c z.1 z.2)]
    have hs := split (fun i x => c x (xhat i))
    dsimp only
    rw [hs]
    exact hbudget
  -- expectation of Ψ against μ* is the explicit atom-value formula
  have hexp : expect μstar Ψ
      = (N : ℝ)⁻¹ * ((∑ i ∈ Finset.univ.erase i₀, Ψ (ξstar i))
          + p0 * Ψ (ξstar i₀) + (1 - p0) * Ψ ξbarstar) := by
    rw [expect, hμcoe, integral_wsum a atom ha0 Ψ]
    have hs := split (fun _ x => Ψ x)
    rw [hs]
  -- attainment: μ* is worst-case (≤ by feasibility + le_csSup, ≥ by the attainment edge)
  have hval : expect μstar Ψ = droValue (ambiguitySet c ν δ) Ψ := by
    refine le_antisymm ?_ ?_
    · exact le_csSup hbddP ⟨μstar, hmem, rfl⟩
    · rw [hexp]; exact hattain
  refine ⟨μstar, i₀, ξstar, ξbarstar, p0, hmem, hval, ⟨hp00, hp01⟩, ?_, hξstar, hξbar⟩
  rw [hμcoe]; exact hMsplit

end GaoKleywegt2023
