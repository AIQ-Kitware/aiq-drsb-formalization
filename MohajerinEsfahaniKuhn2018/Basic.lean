/-
# Mohajerin Esfahani–Kuhn (2018): data-driven Wasserstein DRO

Lean formalization of selected data-driven strong-duality, finite convex reformulation,
and extremal-distribution results from

  P. Mohajerin Esfahani, D. Kuhn, "Data-driven Distributionally Robust Optimization
  Using the Wasserstein Metric", *Mathematical Programming* (2018), arXiv:1505.05116.

Aligned with the prose transcription `prose/wasserstein-dro-duality.md` (§3,
"Mohajerin Esfahani–Kuhn (2018): data-driven duality and convex reformulation") and the
repository's current optimal-transport API.

## What is stated here

* `worstCaseExpectation_eq_dual` — **Theorem 4.2** (§3.2), the data-driven strong
  duality: the worst-case expectation (eq. (10)) over the ε-Wasserstein ball around
  the empirical nominal `P̂_N` equals the one-dimensional convex dual `inf_{λ ≥ 0}`
  of eq. (12b) (the pointwise-`sup` dual obtained in the proof of Theorem 4.2).
* `worstCase_program` — **Theorem 4.4** (§3.3), the extremal-distribution program:
  the same worst-case value equals the optimal value of the finite convex program
  (eq. (13)) in the transport weights `αᵢₖ` and vectors `qᵢₖ`.
* `worstCase_exists` — **Corollary 4.6** (§3.3), existence of an attaining worst-case
  distribution supported on the atoms `ξ̂ᵢ − qᵢₖ/αᵢₖ`.

## Metric / cost convention (IMPORTANT)

Unlike the DRSB `W₂²` specialization, this paper uses the **1-Wasserstein** metric with an
arbitrary norm `‖·‖` (Definition 3.1). Hence the transport cost is the **un-squared**
`c ξ ξ̂ = ‖ξ − ξ̂‖` (order 1), and the ε-ball radius is `ε` (not `ε²`).

## Faithfulness notes / documented gaps

* The nominal `P̂_N = (1/N) ∑ δ_{ξ̂ᵢ}` is abstracted as a `μhat : ProbabilityMeasure X`
  carrying the hypothesis `(μhat : Measure X) = empiricalMeasure ξhat` (the task's
  sanctioned abstraction). The empirical measure itself is `empiricalMeasure`.
* The uncertainty set `Ξ ⊆ ℝᵐ` is a `Ξ : Set X`; the inner `sup_{ξ ∈ Ξ}` of eq. (12b)
  is `sSup ((fun ξ => …) '' Ξ)` (image over `Ξ`, faithful to the printed `sup_{ξ∈Ξ}`).
* The **printed** Theorem 4.2 is the fully-dualized finite convex program eq. (11) in
  variables `(λ, sᵢ, zᵢₖ, νᵢₖ)` using the conjugates `[−ℓₖ]*`, the dual norm `‖·‖_*`
  and the support function `σ_Ξ`. Per the task instructions we encode the equivalent
  intermediate dual **eq. (12b)** (the pointwise-`sup` dual, from the proof of Thm 4.2),
  which is the form that plugs into the DRSB chain. The conjugate/support-function
  reduction (11) is a further algebraic step not encoded here — documented gap.
* The `q/α` terms use the perspective-function convention `α = 0 ⇒ q = 0` and the term
  contributes `0`; this is realized automatically by Lean's junk value `(0:ℝ)⁻¹ = 0`
  and `0 * _ = 0`, so no side condition is needed.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.WeakDuality

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace MohajerinEsfahaniKuhn2018

-- `Ξ ⊆ ℝᵐ` with an arbitrary norm: a normed real vector space with a Borel-type
-- measurable structure. `NormedSpace ℝ X` provides the scalar action used by the
-- convexity hypotheses and by the transport atoms `ξ̂ᵢ − qᵢₖ/αᵢₖ`.
variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Reusable finite-measure helpers for the worst-case-law construction

The extremal / worst-case distributions of Esfahani–Kuhn Thm 4.4 (and Gao–Kleywegt
Cor 2(ii)) are finite weighted sums of Dirac masses `(1/N) Σᵢ Σₖ αᵢₖ δ_{ξᵢₖ}`. The three
lemmas below package the facts needed to work with them — total mass, integral (expectation)
formula, and pushforward (marginal) — under `[MeasurableSingletonClass X]` (Borel σ-algebra
of a metric space; the data-driven setting `Ξ ⊆ ℝᵐ`). Paper-agnostic; promotable to
`ForMathlib` if a second consumer (Gao Cor 2(ii)) lands. -/

/-- **Total mass of the weighted Dirac double-sum is 1** (so it is a probability measure),
given nonnegative weights that sum to `1` over `k` for each `i`, and `0 < N`. -/
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
`∫ g d((1/N) Σᵢ Σₖ αᵢₖ δ_{zᵢₖ}) = (1/N) Σᵢ Σₖ αᵢₖ · g(zᵢₖ)` (nonnegative weights). -/
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

/-- **Empirical nominal `P̂_N = (1/N) ∑_{i} δ_{ξ̂ᵢ}`** over the data
`ξhat : Fin N → X` (`prose/wasserstein-dro-duality.md` §3.1). A plain `Measure X`;
it is a probability measure when `0 < N`. -/
noncomputable def empiricalMeasure {N : ℕ} (ξhat : Fin N → X) : Measure X :=
  (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, Measure.dirac (ξhat i)

/-- **Wasserstein-1 ambiguity ball `B_ε(P̂_N) = { Q : d_W(P̂_N, Q) ≤ ε }`**
(prose §3.1, Definition 3.1 + eq. (6)). The metric is the order-1 optimal-transport
cost with cost `c ξ ξ̂ = ‖ξ − ξ̂‖`, i.e. `otCost (fun x y => ‖x − y‖) μhat Q = d_W(P̂_N, Q)`
(`d_W` is symmetric, so the marginal order is immaterial). -/
noncomputable def wass1Ball (μhat : ProbabilityMeasure X) (ε : ℝ) :
    Set (ProbabilityMeasure X) :=
  { Q | otCost (fun x y => ‖x - y‖) μhat Q ≤ ε }

/-- **P(Ξ)-restricted Wasserstein-1 ambiguity ball** `B^Ξ_ε(P̂_N) = { Q ∈ P(Ξ) : d_W(P̂_N,Q) ≤ ε }`
— the `wass1Ball` intersected with the measures supported on the uncertainty set `Ξ`
(`∀ᵐ x ∂Q, x ∈ Ξ`).

Esfahani–Kuhn's ambiguity set is over `P(Ξ)`, the probability measures supported on `Ξ`, and
their loss pieces `−ℓₖ` are proper convex functions that equal `+∞` outside `Ξ`. Because the Lean
encoding uses total real-valued functions `ℓk : Fin K → X → ℝ`, the support condition is stated
explicitly in this definition. It ensures that the primal measures and the dual supremum both range
over `Ξ`. The laws constructed by `worstCase_program` and `worstCase_exists` are supported on their
specified atoms in `Ξ`, and hence also belong to `wass1BallΞ`. -/
noncomputable def wass1BallΞ (μhat : ProbabilityMeasure X) (Ξ : Set X) (ε : ℝ) :
    Set (ProbabilityMeasure X) :=
  { Q | (∀ᵐ x ∂(Q : Measure X), x ∈ Ξ)
      ∧ otCost (fun x y => ‖x - y‖) μhat Q ≤ ε }

/-- **Theorem 4.2 — data-driven strong duality / convex reduction**
(`prose/wasserstein-dro-duality.md` §3.2, Theorem 4.2, encoded in the pointwise-`sup`
dual form eq. (12b)).

Under the convexity Assumption 4.1, for every `ε ≥ 0` the worst-case expectation of the
loss `ℓ = max_{k ≤ K} ℓₖ` over the ε-Wasserstein ball around the empirical nominal
`P̂_N` (eq. (10)) equals the one-dimensional convex dual

  `sup_{Q ∈ B^Ξ_ε(P̂_N)} 𝔼_Q[ℓ]
     = inf_{λ ≥ 0} { λε + (1/N) ∑_{i=1}^N sup_{ξ ∈ Ξ} ( ℓ(ξ) − λ‖ξ − ξ̂ᵢ‖ ) }`   (eq. (12b)).

The ambiguity set is `wass1BallΞ`, which makes the source condition `Q ∈ P(Ξ)` explicit in the
real-valued Lean encoding. This matches the primal support restriction with the dual supremum over
`ξ ∈ Ξ`.

**Proof (house pattern — `le_antisymm(weak, attainment)`, the exact posture of
`GaoKleywegt2023.strong_duality_thm1`).** The **weak `≤`** direction is proved genuinely: over
the `Ξ`-restricted ball, `csSup_le → le_csInf → per-(Q,λ)` reduces (via `le_of_forall_pos_le_add`,
the same `η/(λ+1)` trick as `GaoKleywegt2023.weak_duality_prop1`) to the new
`ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost_restrict` — the `Ξ`-restricted
Lagrangian kernel, which needs `Q ∈ P(Ξ)` (`hQ.1`, supplied by the ball) so its conjugate `sup`
lands on `Ξ` — composed with the empirical collapse `𝔼_{P̂_N}[g] = (1/N)Σᵢ g(ξ̂ᵢ)` (integral
against the empirical measure, no measurability side-condition) and the OT coupling ε-approx edge
`hOT`. Integrability against `P̂_N` is automatic (finite Dirac sum). The research-grade **`≥`
(attainment / primal-dual)** direction is isolated to the single explicit edge `hattain` — as in
every strong-duality equality here. Regularity edges (`hbdd`, `hℓQ`, `hOT`, `hfeas`) mirror
`weak_duality_prop1`. `[BorelSpace X]` is added so `IsClosed Ξ ⇒ MeasurableSet Ξ` (the kernel's
one measurability need). `_hΞconv`/`_hconv`/`_hlsc`/`_hdata` (and `_hℓ`, `_hε`) are Assumption 4.1 / setup, retained as
the paper's premises but `_`-marked as not proof-critical for the *equality* (a full proof would
use them to discharge `hOT`/`hattain` via LP duality; `hΞclosed` is used, for `MeasurableSet Ξ`). -/
theorem worstCaseExpectation_eq_dual [MeasurableSingletonClass X] [BorelSpace X]
    (N : ℕ) (ξhat : Fin N → X)
    -- `N` data points, so `0 < N` (needed for the `1/N` average and for `P̂_N` a probability)
    (hN : 0 < N)
    (μhat : ProbabilityMeasure X)
    -- the nominal is the empirical measure (sanctioned abstraction)
    (hμ : (μhat : Measure X) = empiricalMeasure ξhat)
    -- radius `ε ≥ 0` (Theorem 4.2 holds "for any ε ≥ 0"); faithful, not proof-critical for the equality
    (ε : ℝ) (_hε : 0 ≤ ε)
    (K : ℕ) (ℓk : Fin K → X → ℝ) (ℓ : X → ℝ)
    -- the loss is the pointwise max of `K ≥ 1` pieces (faithful; the equality holds for generic `ℓ` —
    -- the max structure only feeds the paper's further LP reduction, so `_hℓ` is not proof-critical)
    (hKne : (Finset.univ : Finset (Fin K)).Nonempty)
    (_hℓ : ∀ ξ, ℓ ξ = (Finset.univ : Finset (Fin K)).sup' hKne (fun k => ℓk k ξ))
    -- Assumption 4.1: `Ξ` convex (faithful; `_`) and closed (`hΞclosed` used for `MeasurableSet Ξ`)
    (Ξ : Set X) (_hΞconv : Convex ℝ Ξ) (hΞclosed : IsClosed Ξ)
    -- Assumption 4.1: each `−ℓₖ` convex on `Ξ` (faithful paper premise; subsumed by `hattain`; `_`)
    (_hconv : ∀ k, ConvexOn ℝ Ξ (fun ξ => -(ℓk k ξ)))
    -- Assumption 4.1: each `−ℓₖ` lower semicontinuous on `Ξ` (faithful; subsumed by `hattain`; `_`)
    (_hlsc : ∀ k, LowerSemicontinuousOn (fun ξ => -(ℓk k ξ)) Ξ)
    -- implicit: the data are realizations of the uncertainty `ξ ∈ Ξ` (faithful; `_`)
    (_hdata : ∀ i, ξhat i ∈ Ξ)
    -- regularity edges (mirror `GaoKleywegt2023.weak_duality_prop1`): the conjugate is finite,
    -- `ℓ ∈ L¹(Q)` for feasible `Q`, the ball is nonempty, and `otCost ≤ ε` is witnessed by
    -- integrable-cost couplings (the OT ε-approximation)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ y : X,
        BddAbove ((fun x => ℓ x - lam * ‖x - y‖) '' Ξ))
    (hℓQ : ∀ Q : ProbabilityMeasure X, Q ∈ wass1BallΞ μhat Ξ ε →
        Integrable ℓ (Q : Measure X))
    (hfeas : (wass1BallΞ μhat Ξ ε).Nonempty)
    (hOT : ∀ Q : ProbabilityMeasure X, Q ∈ wass1BallΞ μhat Ξ ε → ∀ η : ℝ, 0 < η →
        ∃ π : ProbabilityMeasure (X × X), π ∈ couplings Q μhat ∧
          couplingCost (fun x y => ‖x - y‖) π ≤ ε + η ∧
          Integrable (fun z : X × X => ‖z.1 - z.2‖) (π : Measure (X × X)))
    -- the `≥` edge: **the duality gap vanishes** (the research-grade OT primal-dual seam,
    -- isolated as one inequality). Note this is already the weak form — it asserts no maximizer.
    (hge : sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + (1 / (N : ℝ)) * ∑ i : Fin N,
              sSup ((fun ξ : X => ℓ ξ - lam * ‖ξ - ξhat i‖) '' Ξ) }
        ≤ droValue (wass1BallΞ μhat Ξ ε) ℓ) :
    droValue (wass1BallΞ μhat Ξ ε) ℓ
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε
              + (1 / (N : ℝ)) * ∑ i : Fin N,
                  sSup ((fun ξ : X => ℓ ξ - lam * ‖ξ - ξhat i‖) '' Ξ) } := by
  have hΞmeas : MeasurableSet Ξ := hΞclosed.measurableSet
  -- integrability against the empirical nominal is automatic (finite Dirac sum)
  have hint_emp : ∀ g : X → ℝ, Integrable g (μhat : Measure X) := by
    intro g
    rw [hμ, empiricalMeasure]
    exact (integrable_finsetSum_measure.2
      (fun i _ => integrable_dirac enorm_lt_top)).smul_measure
      (by simp; exact_mod_cast hN.ne')
  -- expectation against the empirical nominal: 𝔼_{P̂_N}[g] = (1/N) Σᵢ g(ξ̂ᵢ)
  have hexp_emp : ∀ g : X → ℝ, expect μhat g = (1 / (N : ℝ)) * ∑ i, g (ξhat i) := by
    intro g
    rw [expect, hμ, empiricalMeasure, integral_smul_measure,
      integral_finsetSum_measure (fun i _ => integrable_dirac enorm_lt_top)]
    simp_rw [integral_dirac]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, one_div]
  refine le_antisymm ?_ hge
  -- weak direction: droValue ≤ dual, from the Ξ-restricted kernel + empirical collapse
  obtain ⟨Q₀, hQ₀⟩ := hfeas
  refine csSup_le ⟨expect Q₀ ℓ, Q₀, hQ₀, rfl⟩ ?_
  rintro a ⟨Q, hQ, rfl⟩
  refine le_csInf ⟨_, 0, le_refl 0, rfl⟩ ?_
  rintro v ⟨lam, hlam, rfl⟩
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hηdiv : (0 : ℝ) < η / (lam + 1) := div_pos hη (by linarith)
  obtain ⟨π, hπ, hcost, hcint⟩ := hOT Q hQ (η / (lam + 1)) hηdiv
  have hker := ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost_restrict
    (fun x y => ‖x - y‖) ℓ lam hlam Q μhat Ξ hΞmeas π hπ hQ.1 (hbdd lam hlam)
    (hℓQ Q hQ) (hint_emp _) hcint
  have hcollapse : expect μhat (fun y => sSup ((fun x => ℓ x - lam * ‖x - y‖) '' Ξ))
      = (1 / (N : ℝ)) * ∑ i, sSup ((fun ξ : X => ℓ ξ - lam * ‖ξ - ξhat i‖) '' Ξ) :=
    hexp_emp _
  rw [hcollapse] at hker
  have h1 : lam * couplingCost (fun x y => ‖x - y‖) π
      ≤ lam * ε + lam * (η / (lam + 1)) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hcost hlam
  have h2 : lam * (η / (lam + 1)) ≤ η := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < lam + 1)]
    nlinarith [hη, hlam]
  linarith [hker, h1, h2]

/-- **Feasible set of the extremal program eq. (13)** (`prose/wasserstein-dro-duality.md`
§3.3, Theorem 4.4): mixture weights `αᵢₖ ≥ 0` with `∑ₖ αᵢₖ = 1` for each `i`, transport
vectors `qᵢₖ` with budget `(1/N) ∑_{i,k} ‖qᵢₖ‖ ≤ ε`, and the atoms `ξ̂ᵢ − qᵢₖ/αᵢₖ ∈ Ξ`. -/
def extremalFeasible {N K : ℕ} (ξhat : Fin N → X) (Ξ : Set X) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X) : Prop :=
  (∀ i k, 0 ≤ α i k)
  ∧ (∀ i, ∑ k, α i k = 1)
  ∧ (1 / (N : ℝ)) * ∑ i, ∑ k, ‖q i k‖ ≤ ε
  ∧ (∀ i k, ξhat i - (α i k)⁻¹ • q i k ∈ Ξ)

/-- **Objective of the extremal program eq. (13)** (prose §3.3, Theorem 4.4):
`(1/N) ∑_{i=1}^N ∑_{k=1}^K αᵢₖ · ℓₖ(ξ̂ᵢ − qᵢₖ/αᵢₖ)`. -/
noncomputable def extremalObjective {N K : ℕ} (ξhat : Fin N → X) (ℓk : Fin K → X → ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ∑ k, α i k * ℓk k (ξhat i - (α i k)⁻¹ • q i k)

/-- **The discrete worst-case law** `Q = (1/N) ∑_{i,k} αᵢₖ δ_{ξᵢₖ}` with atoms
`ξ : Fin N → Fin K → X` (prose §3.3, eq. after Theorem 4.4 and Corollary 4.6). A plain
`Measure X`; it is a probability measure when `∑ₖ αᵢₖ = 1` for each `i` and `0 < N`. -/
noncomputable def worstCaseLaw {N K : ℕ} (α : Fin N → Fin K → ℝ)
    (ξ : Fin N → Fin K → X) : Measure X :=
  (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin K, ENNReal.ofReal (α i k) • Measure.dirac (ξ i k)

/-- **Constructive core (proved): the discrete law of a feasible config is in the ball
and dominates its extremal objective.** For any feasible `(α, q)` (Assumption 4.1 program),
the explicit discrete law `Q = (1/N) Σᵢₖ αᵢₖ δ_{ξ̂ᵢ − qᵢₖ/αᵢₖ}` (i) lies in the
ε-Wasserstein ball around the empirical nominal, witnessed by the explicit transport plan
`(1/N) Σᵢₖ αᵢₖ δ_{(ξ̂ᵢ, ξ̂ᵢ − qᵢₖ/αᵢₖ)}` (cost `(1/N) Σ ‖qᵢₖ‖ ≤ ε`, via
`ForMathlib.OT.otCost_le_couplingCost`), and (ii) satisfies `𝔼_Q[ℓ] ≥ extremalObjective`
(since `ℓ = maxₖ ℓₖ ≥ ℓₖ`). No measurable selection — the atoms are the finitely many
data-point perturbations. This is the shared engine behind Theorem 4.4 (`worstCase_program`)
and Corollary 4.6 (`worstCase_exists`). -/
theorem worstCaseLaw_ball_ge [MeasurableSingletonClass X]
    {N : ℕ} (ξhat : Fin N → X) (hN : 0 < N) (μhat : ProbabilityMeasure X)
    (hμ : (μhat : Measure X) = empiricalMeasure ξhat) (ε : ℝ)
    {K : ℕ} (ℓk : Fin K → X → ℝ) (ℓ : X → ℝ)
    (hKne : (Finset.univ : Finset (Fin K)).Nonempty)
    (hℓ : ∀ ξ, ℓ ξ = (Finset.univ : Finset (Fin K)).sup' hKne (fun k => ℓk k ξ))
    (Ξ : Set X) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X)
    (hfeas : extremalFeasible ξhat Ξ ε α q) :
    ∃ Q : ProbabilityMeasure X,
      (Q : Measure X) = worstCaseLaw α (fun i k => ξhat i - (α i k)⁻¹ • q i k)
      ∧ Q ∈ wass1Ball μhat ε
      ∧ extremalObjective ξhat ℓk α q ≤ expect Q ℓ := by
  obtain ⟨hα0, hαsum, hqbudget, hatomΞ⟩ := hfeas
  set atom : Fin N → Fin K → X := fun i k => ξhat i - (α i k)⁻¹ • q i k with hatom
  have hprobQ : IsProbabilityMeasure (worstCaseLaw α atom) :=
    isProbabilityMeasure_wsum hN α atom hα0 hαsum
  set Q : ProbabilityMeasure X := ⟨worstCaseLaw α atom, hprobQ⟩ with hQ
  have hQcoe : (Q : Measure X) = worstCaseLaw α atom := rfl
  -- the explicit transport plan π from μ̂ to Q
  have hprobπ : IsProbabilityMeasure ((N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin K,
      ENNReal.ofReal (α i k) • Measure.dirac (ξhat i, atom i k)) :=
    isProbabilityMeasure_wsum hN α (fun i k => (ξhat i, atom i k)) hα0 hαsum
  set π : ProbabilityMeasure (X × X) := ⟨_, hprobπ⟩ with hπ
  have hπcoe : (π : Measure (X × X)) = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, ∑ k : Fin K,
      ENNReal.ofReal (α i k) • Measure.dirac (ξhat i, atom i k) := rfl
  have hcoupl : π ∈ couplings μhat Q := by
    constructor
    · rw [hπcoe, map_wsum α (fun i k => (ξhat i, atom i k)) Prod.fst measurable_fst, hμ,
        empiricalMeasure]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only
      rw [← Finset.sum_smul,
        ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hα0 i k), hαsum i, ENNReal.ofReal_one,
        one_smul]
    · rw [hπcoe, map_wsum α (fun i k => (ξhat i, atom i k)) Prod.snd measurable_snd, hQcoe,
        worstCaseLaw]
  have hcostπ : couplingCost (fun x y => ‖x - y‖) π ≤ ε := by
    rw [couplingCost, hπcoe,
      integral_wsum α (fun i k => (ξhat i, atom i k)) hα0 (fun z => ‖z.1 - z.2‖)]
    refine le_trans ?_ hqbudget
    rw [one_div]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => ?_))
    have hdiff : ξhat i - atom i k = (α i k)⁻¹ • q i k := by rw [hatom]; simp
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (hα0 i k), ← mul_assoc]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      rcases eq_or_lt_of_le (hα0 i k) with h | h
      · simp [← h]
      · rw [mul_inv_cancel₀ (ne_of_gt h)])
  have hball : Q ∈ wass1Ball μhat ε :=
    le_trans (otCost_le_couplingCost _ (fun x y => norm_nonneg _) μhat Q π hcoupl) hcostπ
  have hexp : extremalObjective ξhat ℓk α q ≤ expect Q ℓ := by
    rw [expect, hQcoe, worstCaseLaw, integral_wsum α atom hα0 ℓ, extremalObjective, one_div]
    simp only [hatom]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => ?_))
    refine mul_le_mul_of_nonneg_left ?_ (hα0 i k)
    rw [hℓ (ξhat i - (α i k)⁻¹ • q i k)]
    exact Finset.le_sup' (fun k' => ℓk k' (ξhat i - (α i k)⁻¹ • q i k)) (Finset.mem_univ k)
  exact ⟨Q, hQcoe, hball, hexp⟩

/-- **Theorem 4.4 — worst-case (extremal) distributions, program form**
(`prose/wasserstein-dro-duality.md` §3.3, Theorem 4.4, eq. (13)).

Under the convexity Assumption 4.1, the worst-case expectation (eq. (10)) coincides with
the optimal value of the finite convex program (eq. (13)) over the transport weights `αᵢₖ`
and vectors `qᵢₖ`:

  `sup_{Q ∈ B_ε(P̂_N)} 𝔼_Q[ℓ]
     = sup_{(α, q) feasible} (1/N) ∑_{i} ∑_{k} αᵢₖ · ℓₖ(ξ̂ᵢ − qᵢₖ/αᵢₖ)`.

**Proof (house pattern, `[MeasurableSingletonClass X]`).** The `≥`
(`sup(program) ≤ droValue`) direction is constructive: every
feasible `(α, q)` yields the explicit discrete law `Q = (1/N) Σᵢₖ αᵢₖ δ_{ξ̂ᵢ − qᵢₖ/αᵢₖ}`,
which lies in the ε-Wasserstein ball (witnessed by the explicit transport plan
`(1/N) Σᵢₖ αᵢₖ δ_{(ξ̂ᵢ, ξ̂ᵢ − qᵢₖ/αᵢₖ)}`, whose cost `(1/N) Σᵢₖ ‖qᵢₖ‖ ≤ ε` — via
`ForMathlib.OT.otCost_le_couplingCost`) and satisfies `𝔼_Q[ℓ] ≥ extremalObjective`
(since `ℓ = maxₖ ℓₖ ≥ ℓₖ`). No measurable selection is needed — the atoms are the finitely
many data-point perturbations. The `≤` (`droValue ≤ sup(program)`, Theorem 4.4's real OT
content — every ball measure is dominated by an extremal config) is isolated to the single
explicit hypothesis `hdom`, expressing that every ball measure is dominated by an extremal
configuration. -/
theorem worstCase_program [MeasurableSingletonClass X]
    (N : ℕ) (ξhat : Fin N → X) (hN : 0 < N)
    (μhat : ProbabilityMeasure X) (hμ : (μhat : Measure X) = empiricalMeasure ξhat)
    (ε : ℝ) (hε : 0 ≤ ε)
    (K : ℕ) (ℓk : Fin K → X → ℝ) (ℓ : X → ℝ)
    (hKne : (Finset.univ : Finset (Fin K)).Nonempty)
    (hℓ : ∀ ξ, ℓ ξ = (Finset.univ : Finset (Fin K)).sup' hKne (fun k => ℓk k ξ))
    -- Assumption 4.1 (`Ξ` convex/closed, `−ℓₖ` convex+lsc): faithful paper premises, subsumed by
    -- the `hdom` reduction edge (the constructive `≥` direction needs none of them); marked `_`
    (Ξ : Set X) (_hΞconv : Convex ℝ Ξ) (_hΞclosed : IsClosed Ξ)
    (_hconv : ∀ k, ConvexOn ℝ Ξ (fun ξ => -(ℓk k ξ)))
    (_hlsc : ∀ k, LowerSemicontinuousOn (fun ξ => -(ℓk k ξ)) Ξ)
    (hdata : ∀ i, ξhat i ∈ Ξ)
    -- the DRO worst-case value is finite (bounded ambiguity ball), an explicit finiteness assumption:
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ wass1Ball μhat ε ∧ r = expect μ ℓ })
    -- the `≤`/reduction edge (Thm 4.4's OT content: every ball measure ≤ some extremal
    -- config), represented by the explicit hypothesis below:
    (hdom : droValue (wass1Ball μhat ε) ℓ
        ≤ sSup { v : ℝ | ∃ (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X),
            extremalFeasible ξhat Ξ ε α q ∧ v = extremalObjective ξhat ℓk α q }) :
    droValue (wass1Ball μhat ε) ℓ
      = sSup { v : ℝ | ∃ (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X),
          extremalFeasible ξhat Ξ ε α q ∧ v = extremalObjective ξhat ℓk α q } := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hKpos : 0 < K := Finset.card_fin K ▸ hKne.card_pos
  refine le_antisymm hdom (csSup_le ?_ ?_)
  · -- program set nonempty: the uniform-weight, zero-transport config is feasible
    refine ⟨extremalObjective ξhat ℓk (fun _ _ => (K : ℝ)⁻¹) (fun _ _ => 0),
      (fun _ _ => (K : ℝ)⁻¹), (fun _ _ => 0), ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · exact fun i k => by positivity
    · intro i; simp; field_simp
    · simp [hε]
    · intro i k; simpa using hdata i
  · -- every feasible objective is ≤ droValue, via the constructed worst-case law Q
    rintro v ⟨α, q, hfeas, rfl⟩
    obtain ⟨Q, _, hball, hge⟩ :=
      worstCaseLaw_ball_ge ξhat hN μhat hμ ε ℓk ℓ hKne hℓ Ξ α q hfeas
    exact hge.trans (le_csSup hbddP ⟨Q, hball, rfl⟩)

/-- **Corollary 4.6 — existence of a worst-case distribution**
(`prose/wasserstein-dro-duality.md` §3.3, Corollary 4.6).

Under the convexity Assumption 4.1, if `Ξ` is compact **or** the loss is concave (`K = 1`),
there exist optimal weights `α` and transport vectors `q` (feasible for eq. (13)) such that
the discrete law `Q* = (1/N) ∑_{i,k} αᵢₖ δ_{ξ̂ᵢ − qᵢₖ/αᵢₖ}` lies in the ε-Wasserstein ball
`B_ε(P̂_N)` and **attains** the supremum of the worst-case expectation (eq. (10)).

The worst-case law is supported on the (at most `N·K`) atoms `ξ̂ᵢ − qᵢₖ/αᵢₖ`, i.e.
perturbations of the data points along the transport vectors `qᵢₖ`; these may lie outside
the support of `P̂_N` (a Wasserstein-ball feature). (Gao–Kleywegt Corollary 2(ii) further
refines the support to at most `N + 1` atoms — not encoded here.)

**Proof (house pattern, `[MeasurableSingletonClass X]`).** The paper's existence condition
`hExist` (`Ξ` compact or `K = 1`) is what *guarantees* the extremal program's optimum is
attained; deriving attainment from compactness is an extreme-value argument over the feasible
set (absent from Mathlib as a packaged result), so it is isolated as the single explicit edge
`hattain` — a feasible `(α, q)` whose extremal objective equals `droValue`. Given it, the
construction lemma `worstCaseLaw_ball_ge` produces the discrete law `Q` in the ball with
`𝔼_Q[ℓ] ≥ extremalObjective = droValue`, and `𝔼_Q[ℓ] ≤ droValue` (as `Q` is in the ball,
`le_csSup`), so `𝔼_Q[ℓ] = droValue` — `Q` attains it. Everything except `hattain` is proved
proved. -/
theorem worstCase_exists [MeasurableSingletonClass X]
    (N : ℕ) (ξhat : Fin N → X) (hN : 0 < N)
    (μhat : ProbabilityMeasure X) (hμ : (μhat : Measure X) = empiricalMeasure ξhat)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (K : ℕ) (ℓk : Fin K → X → ℝ) (ℓ : X → ℝ)
    (hKne : (Finset.univ : Finset (Fin K)).Nonempty)
    (hℓ : ∀ ξ, ℓ ξ = (Finset.univ : Finset (Fin K)).sup' hKne (fun k => ℓk k ξ))
    -- Assumption 4.1 (faithful paper premises, subsumed by `hattain`/`worstCaseLaw_ball_ge`); `_`
    (Ξ : Set X) (_hΞconv : Convex ℝ Ξ) (_hΞclosed : IsClosed Ξ)
    (_hconv : ∀ k, ConvexOn ℝ Ξ (fun ξ => -(ℓk k ξ)))
    (_hlsc : ∀ k, LowerSemicontinuousOn (fun ξ => -(ℓk k ξ)) Ξ)
    (_hdata : ∀ i, ξhat i ∈ Ξ)
    -- Corollary 4.6 existence hypothesis: `Ξ` compact or the loss concave (`K = 1`); it is what
    -- *supplies* `hattain` in reality, so with `hattain` given it is faithful-but-unused; `_`
    (_hExist : IsCompact Ξ ∨ K = 1)
    -- the DRO worst-case value is finite (bounded ambiguity ball), an explicit finiteness assumption:
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ wass1Ball μhat ε ∧ r = expect μ ℓ })
    -- attainment edge: the extremal program's optimum is attained (what `hExist` supplies —
    -- an extreme-value argument absent from Mathlib), isolated as one explicit hypothesis:
    (hattain : ∃ (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X),
        extremalFeasible ξhat Ξ ε α q
          ∧ extremalObjective ξhat ℓk α q = droValue (wass1Ball μhat ε) ℓ) :
    ∃ (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X) (Q : ProbabilityMeasure X),
        extremalFeasible ξhat Ξ ε α q
      ∧ (Q : Measure X) = worstCaseLaw α (fun i k => ξhat i - (α i k)⁻¹ • q i k)
      ∧ Q ∈ wass1Ball μhat ε
      ∧ expect Q ℓ = droValue (wass1Ball μhat ε) ℓ := by
  obtain ⟨α, q, hfeas, hval⟩ := hattain
  obtain ⟨Q, hQeq, hball, hge⟩ :=
    worstCaseLaw_ball_ge ξhat hN μhat hμ ε ℓk ℓ hKne hℓ Ξ α q hfeas
  exact ⟨α, q, Q, hfeas, hQeq, hball,
    le_antisymm (le_csSup hbddP ⟨Q, hball, rfl⟩) (hval ▸ hge)⟩

end MohajerinEsfahaniKuhn2018
