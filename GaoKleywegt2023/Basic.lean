/-
# Gao–Kleywegt (2023): Wasserstein DRO strong duality + worst-case structure

Statement-only Lean scaffold for the core results of

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
`ForMathlib.OptimalTransport.Basic` and is re-derived from the prose, not from the
trap-laden `reference/V4.lean`.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.WeakDuality

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace GaoKleywegt2023

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

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
`sup_ξ (Ψ(ξ) − λ c(ξ, ζ))` (the scaffold's `L_wdro`). -/
noncomputable def Phi (c : X → X → ℝ) (Ψ : X → ℝ) (lam : ℝ) (ζ : X) : ℝ :=
  sInf (Set.range (fun ξ => lam * c ξ ζ - Ψ ξ))

/-- **Dual value** `v_D := inf_{λ ≥ 0} { λ δ − ∫ Φ(λ, ζ) ν(dζ) }`
(prose §2.1, "Dual", with `θᵖ = δ`). Using `−inf_ξ(λc − Ψ) = sup_ξ(Ψ − λc)` this
is the univariate strong dual `inf_{λ≥0}{λδ + 𝔼_ν[sup_ξ(Ψ(ξ) − λ c(ξ,ζ))]}`,
i.e. the scaffold's `wdro_dual` / `wdrsbDualObjective` right-hand side. -/
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

/-- **Proposition 1 (Weak duality).** *Consider any `ν ∈ P(Ξ)` and `Ψ ∈ L¹(ν)`.
Then for any `p ∈ [1,∞)` and `θ > 0`, it holds that `v_P ≤ v_D`.* (prose §2.2,
Proposition 1 — the always-true Lagrangian direction; `p` and `θ` enter through the
general cost `c` and radius `δ = θᵖ > 0`.) -/
theorem weak_duality_prop1
    (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ)
    (hΨ : Integrable Ψ (ν : Measure X))   -- Ψ ∈ L¹(ν)
    (hδ : 0 < δ)                          -- δ = θᵖ with θ > 0
    -- regularity / formalization edges (cf. AGENTS.md §6):
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
    (hκ : kappa c Ψ ν ≠ ⊤) :              -- κ < ∞  (finite transport growth)
    primalValue c Ψ ν δ = dualValue c Ψ ν δ := by
  sorry

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
(documented gap) — it constrains the coupling realizing the mixture, not `μ*`. -/
theorem worstCase_structure_cor1
    (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ) (lam_star : ℝ)
    (hκ : kappa c Ψ ν ≠ ⊤)                                  -- κ < ∞
    (husc : UpperSemicontinuous Ψ)                          -- Ψ upper semicontinuous
    (hproper : ∀ s : Set X, Bornology.IsBounded s → TotallyBounded s)
                                                            -- bounded ⇒ totally bounded
    (hlam : 0 ≤ lam_star)                                    -- dual minimizer λ* ≥ 0
    (hexists : ∃ μ ∈ ambiguitySet c ν δ,
        expect μ Ψ = droValue (ambiguitySet c ν δ) Ψ) :      -- a worst-case distribution exists
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
  sorry

/-!
### Data-driven DRSO (empirical nominal): Corollary 2, eqs. (28)/(29)

Nominal `ν = (1/N) Σ_{i} δ_{ξ̂ᵢ}`. The empirical dual (eq. 28) is exactly the
DRSB scaffold's `wdrsbDualObjective`; the empirical worst-case (eq. 29) is the
`≤ N+1`-atom transport that the DRSB code computes in closed form.
-/

/-- **Empirical dual objective, eq. (28)** `inf_{λ≥0}{ λ δ − (1/N) Σᵢ inf_ξ(λ c(ξ,
ξ̂ᵢ) − Ψ(ξ)) }` (prose §2.3, Corollary 2(i), with `θᵖ = δ`). Equal, via
`−inf_ξ(λc − Ψ) = sup_ξ(Ψ − λc)`, to the scaffold's `wdrsbDualObjective`
`inf_{λ≥0}{λ δ + (1/N) Σᵢ sup_ξ(Ψ(ξ) − λ c(ξ,ξ̂ᵢ))}` (per-sample term `L_wdro`). -/
noncomputable def empiricalDual {N : ℕ} (c : X → X → ℝ) (Ψ : X → ℝ)
    (xhat : Fin N → X) (δ : ℝ) : ℝ :=
  sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
    v = lam * δ
        - (1 / (N : ℝ)) * ∑ i : Fin N, sInf (Set.range (fun ξ => lam * c ξ (xhat i) - Ψ ξ)) }

/-- **Corollary 2(i) — data-driven strong duality, eq. (28).** *For
`ν = (1/N) Σᵢ δ_{ξ̂ᵢ}`, `p ∈ [1,∞)`, `θ > 0`: the primal has strong dual*
`v_P = v_D = inf_{λ≥0}{ λ θᵖ − (1/N) Σᵢ inf_ξ(λ dᵖ(ξ,ξ̂ᵢ) − Ψ(ξ)) }` (prose §2.3,
Corollary 2(i)). Here `hν` fixes `ν` as the empirical measure on the sample
`xhat : Fin N → X` and `δ = θᵖ`. -/
theorem dataDriven_strongDuality_cor2i
    {N : ℕ} (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X)
    (xhat : Fin N → X) (δ : ℝ)
    (hN : 0 < N)
    (hν : (ν : Measure X) = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, Measure.dirac (xhat i))
    (hΨ : Integrable Ψ (ν : Measure X))   -- Ψ ∈ L¹(ν)
    (hδ : 0 < δ) :                        -- δ = θᵖ with θ > 0
    primalValue c Ψ ν δ = empiricalDual c Ψ xhat δ := by
  sorry

/-- **Corollary 2(ii) — data-driven worst-case distribution, eq. (29).** *Whenever
a worst-case distribution exists, there is one supported on at most `N+1` points,*
`μ* = (1/N) Σ_{i ≠ i₀} δ_{ξ*ⁱ} + (p₀/N) δ_{ξ*^{i₀}} + ((1−p₀)/N) δ_{ξ̄*^{i₀}}`
*(eq. 29) with* `ξ*ⁱ ∈ argmin_ξ(λ* dᵖ(ξ,ξ̂ᵢ) − Ψ(ξ))`*: every data point `ξ̂ᵢ` is
moved to an associated minimizer, and at most one point `ξ̂_{i₀}` is split between
two minimizers `ξ*^{i₀}` and `ξ̄*^{i₀}`* (prose §2.3, Corollary 2(ii)).

`ξstar i` are the per-sample minimizers `ξ*ⁱ` (for `i ≠ i₀`) and `ξ*^{i₀}`;
`ξbarstar` is the second minimizer `ξ̄*^{i₀}` for the split point. `lam_star = λ*`
is the optimal dual multiplier. This `≤ N+1`-atom transport is the DRSB code's
closed-form worst-case. -/
theorem dataDriven_worstCase_cor2ii
    {N : ℕ} (c : X → X → ℝ) (Ψ : X → ℝ) (ν : ProbabilityMeasure X)
    (xhat : Fin N → X) (δ : ℝ) (lam_star : ℝ)
    (hN : 0 < N)
    (hν : (ν : Measure X) = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, Measure.dirac (xhat i))
    (hlam : 0 ≤ lam_star)                                    -- dual minimizer λ* ≥ 0
    (hexists : ∃ μ ∈ ambiguitySet c ν δ,
        expect μ Ψ = droValue (ambiguitySet c ν δ) Ψ) :      -- a worst-case distribution exists
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
  sorry

end GaoKleywegt2023
