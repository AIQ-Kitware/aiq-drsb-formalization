/-
# Mohajerin Esfahani–Kuhn (2018): data-driven Wasserstein DRO

Statement-only scaffold (`sorry` bodies) for the data-driven strong-duality /
finite convex reformulation and the extremal (worst-case) distributions of

  P. Mohajerin Esfahani, D. Kuhn, "Data-driven Distributionally Robust Optimization
  Using the Wasserstein Metric", *Mathematical Programming* (2018), arXiv:1505.05116.

Re-derived from the prose transcription `prose/wasserstein-dro-duality.md` (§3,
"Mohajerin Esfahani–Kuhn (2018): data-driven duality and convex reformulation"), NOT
from the trap-laden `reference/V4.lean` (which is consulted only for Lean syntax).

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

Unlike the DRSB `W₂²` scaffold, this paper uses the **1-Wasserstein** metric with an
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

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace MohajerinEsfahaniKuhn2018

-- `Ξ ⊆ ℝᵐ` with an arbitrary norm: a normed real vector space with a Borel-type
-- measurable structure. `NormedSpace ℝ X` provides the scalar action used by the
-- convexity hypotheses and by the transport atoms `ξ̂ᵢ − qᵢₖ/αᵢₖ`.
variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

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

/-- **Theorem 4.2 — data-driven strong duality / convex reduction**
(`prose/wasserstein-dro-duality.md` §3.2, Theorem 4.2, encoded in the pointwise-`sup`
dual form eq. (12b)).

Under the convexity Assumption 4.1, for every `ε ≥ 0` the worst-case expectation of the
loss `ℓ = max_{k ≤ K} ℓₖ` over the ε-Wasserstein ball around the empirical nominal
`P̂_N` (eq. (10)) equals the one-dimensional convex dual

  `sup_{Q ∈ B_ε(P̂_N)} 𝔼_Q[ℓ]
     = inf_{λ ≥ 0} { λε + (1/N) ∑_{i=1}^N sup_{ξ ∈ Ξ} ( ℓ(ξ) − λ‖ξ − ξ̂ᵢ‖ ) }`   (eq. (12b)).

Body is `sorry` (statement-only scaffold). -/
theorem worstCaseExpectation_eq_dual
    (N : ℕ) (ξhat : Fin N → X)
    -- `N` data points, so `0 < N` (needed for the `1/N` average and for `P̂_N` a probability)
    (hN : 0 < N)
    (μhat : ProbabilityMeasure X)
    -- the nominal is the empirical measure (sanctioned abstraction)
    (hμ : (μhat : Measure X) = empiricalMeasure ξhat)
    -- radius `ε ≥ 0` (Theorem 4.2 holds "for any ε ≥ 0")
    (ε : ℝ) (hε : 0 ≤ ε)
    (K : ℕ) (ℓk : Fin K → X → ℝ) (ℓ : X → ℝ)
    -- the loss is the pointwise max of `K ≥ 1` pieces: `ℓ(ξ) = max_{k ≤ K} ℓₖ(ξ)`
    (hKne : (Finset.univ : Finset (Fin K)).Nonempty)
    (hℓ : ∀ ξ, ℓ ξ = (Finset.univ : Finset (Fin K)).sup' hKne (fun k => ℓk k ξ))
    -- Assumption 4.1: `Ξ` convex and closed
    (Ξ : Set X) (hΞconv : Convex ℝ Ξ) (hΞclosed : IsClosed Ξ)
    -- Assumption 4.1: each `−ℓₖ` is convex on `Ξ` (properness is automatic for the ℝ-valued encoding)
    (hconv : ∀ k, ConvexOn ℝ Ξ (fun ξ => -(ℓk k ξ)))
    -- Assumption 4.1: each `−ℓₖ` is lower semicontinuous on `Ξ`
    (hlsc : ∀ k, LowerSemicontinuousOn (fun ξ => -(ℓk k ξ)) Ξ)
    -- implicit: the data are realizations of the uncertainty `ξ ∈ Ξ`, so `ξ̂ᵢ ∈ Ξ`
    (hdata : ∀ i, ξhat i ∈ Ξ) :
    droValue (wass1Ball μhat ε) ℓ
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε
              + (1 / (N : ℝ)) * ∑ i : Fin N,
                  sSup ((fun ξ : X => ℓ ξ - lam * ‖ξ - ξhat i‖) '' Ξ) } := by
  sorry

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

/-- **Theorem 4.4 — worst-case (extremal) distributions, program form**
(`prose/wasserstein-dro-duality.md` §3.3, Theorem 4.4, eq. (13)).

Under the convexity Assumption 4.1, the worst-case expectation (eq. (10)) coincides with
the optimal value of the finite convex program (eq. (13)) over the transport weights `αᵢₖ`
and vectors `qᵢₖ`:

  `sup_{Q ∈ B_ε(P̂_N)} 𝔼_Q[ℓ]
     = sup_{(α, q) feasible} (1/N) ∑_{i} ∑_{k} αᵢₖ · ℓₖ(ξ̂ᵢ − qᵢₖ/αᵢₖ)`.

Body is `sorry` (statement-only scaffold). -/
theorem worstCase_program
    (N : ℕ) (ξhat : Fin N → X) (hN : 0 < N)
    (μhat : ProbabilityMeasure X) (hμ : (μhat : Measure X) = empiricalMeasure ξhat)
    (ε : ℝ) (hε : 0 ≤ ε)
    (K : ℕ) (ℓk : Fin K → X → ℝ) (ℓ : X → ℝ)
    (hKne : (Finset.univ : Finset (Fin K)).Nonempty)
    (hℓ : ∀ ξ, ℓ ξ = (Finset.univ : Finset (Fin K)).sup' hKne (fun k => ℓk k ξ))
    (Ξ : Set X) (hΞconv : Convex ℝ Ξ) (hΞclosed : IsClosed Ξ)
    (hconv : ∀ k, ConvexOn ℝ Ξ (fun ξ => -(ℓk k ξ)))
    (hlsc : ∀ k, LowerSemicontinuousOn (fun ξ => -(ℓk k ξ)) Ξ)
    (hdata : ∀ i, ξhat i ∈ Ξ) :
    droValue (wass1Ball μhat ε) ℓ
      = sSup { v : ℝ | ∃ (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X),
          extremalFeasible ξhat Ξ ε α q ∧ v = extremalObjective ξhat ℓk α q } := by
  sorry

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

Body is `sorry` (statement-only scaffold). -/
theorem worstCase_exists
    (N : ℕ) (ξhat : Fin N → X) (hN : 0 < N)
    (μhat : ProbabilityMeasure X) (hμ : (μhat : Measure X) = empiricalMeasure ξhat)
    (ε : ℝ) (hε : 0 ≤ ε)
    (K : ℕ) (ℓk : Fin K → X → ℝ) (ℓ : X → ℝ)
    (hKne : (Finset.univ : Finset (Fin K)).Nonempty)
    (hℓ : ∀ ξ, ℓ ξ = (Finset.univ : Finset (Fin K)).sup' hKne (fun k => ℓk k ξ))
    (Ξ : Set X) (hΞconv : Convex ℝ Ξ) (hΞclosed : IsClosed Ξ)
    (hconv : ∀ k, ConvexOn ℝ Ξ (fun ξ => -(ℓk k ξ)))
    (hlsc : ∀ k, LowerSemicontinuousOn (fun ξ => -(ℓk k ξ)) Ξ)
    (hdata : ∀ i, ξhat i ∈ Ξ)
    -- Corollary 4.6 existence hypothesis: `Ξ` compact or the loss concave (`K = 1`)
    (hExist : IsCompact Ξ ∨ K = 1) :
    ∃ (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → X) (Q : ProbabilityMeasure X),
        extremalFeasible ξhat Ξ ε α q
      ∧ (Q : Measure X) = worstCaseLaw α (fun i k => ξhat i - (α i k)⁻¹ • q i k)
      ∧ Q ∈ wass1Ball μhat ε
      ∧ expect Q ℓ = droValue (wass1Ball μhat ε) ℓ := by
  sorry

end MohajerinEsfahaniKuhn2018
