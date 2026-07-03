/-
# Blanchet–Murthy (2019): optimal-transport DRO strong duality

Statement-only scaffold (`sorry` bodies) for the primary strong-duality result of

  J. Blanchet, K. Murthy, "Quantifying Distributional Model Risk via Optimal
  Transport", *Mathematics of Operations Research* (2019), arXiv:1604.01446.

Re-derived from the prose transcription `prose/wasserstein-dro-duality.md` (§1,
"Blanchet–Murthy (2019): strong duality for optimal-transport DRO"), NOT from the
trap-laden `reference/V4.lean` (which is consulted only for Lean syntax).

The backbone of the WDRSB card bound: the worst-case expectation over a hard
optimal-transport-cost ball equals a one-dimensional convex dual (Theorem 1(a),(b)
collapsed via Remark 1, eq. (9)).
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace BlanchetMurthy2019

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

/-- **Inner dual function `φ_λ`** (Blanchet–Murthy Theorem 1(b),
`prose/wasserstein-dro-duality.md` §1.2, eq. after "(b)"):
`φ_λ(x) := sup_{y ∈ S} (f y − λ · c x y)`.

This is the `L_wdro` object of the DRSB scaffold and the per-sample term of the
univariate dual eq. (9). For the DRSB quadratic cost `c x y = ‖x − y‖²` it is
`sup_x (V x − λ‖x − x̂‖²)`. -/
noncomputable def Lc (c : X → X → ℝ) (f : X → ℝ) (lam : ℝ) (x : X) : ℝ :=
  sSup (Set.range (fun y : X => f y - lam * c x y))

/-- **WDRO strong duality — univariate dual** (Blanchet–Murthy Theorem 1(a),(b)
collapsed via Remark 1, eq. (9); `prose/wasserstein-dro-duality.md` §1.2).

Under Assumptions (A1) and (A2), the worst-case expectation of `f` over the hard
optimal-transport-cost ball `{ ν : d_c(ν, μ̂) ≤ δ }` (primal `I`, eq. (3)) equals the
one-dimensional convex dual

  `I = inf_{λ ≥ 0} { λδ + 𝔼_{X∼μ̂}[ sup_{y} (f y − λ c(X, y)) ] }`   (eq. (9)),

whose only measure is the baseline `μ̂`. This is `wdro_dual` of the DRSB scaffold with
`μ ↦ μ̂`, `δ ↦ ε`, `f ↦ V`, `c(x,y) = ‖x − y‖²`.

Faithfulness notes:
* Theorem 1(a) is the abstract `I = J = inf_{(λ,φ) ∈ Λ_{c,f}} (λδ + ∫ φ dμ̂)`; eq. (9)
  is the specialization to the pointwise-optimal `φ = φ_λ`, giving the univariate
  `inf_{λ ≥ 0}` form encoded here (`φ_λ` = `Lc c f lam`, see `wdro_strong_duality_dualFn`).
* The prose's ball is `d_c(μ̂, ν) ≤ δ` with the baseline `μ̂` as the FIRST coupling
  marginal; per the shared scaffold convention the ambiguity set is written
  `otCost c μ μ̂ ≤ δ` (`otCost c μ μ̂` = `d_c(μ, μ̂)`). These coincide when `c` is
  symmetric (in particular the DRSB quadratic cost `‖x − y‖²`); for a general
  asymmetric `c` this is a stated convention, not a claim proved here.
* Blanchet–Murthy Theorem 1 requires only (A1)+(A2); there is NO growth/`κ < ∞`
  hypothesis (that is the Gao–Kleywegt variant), so none is added.

Body is `sorry` (statement-only scaffold). -/
theorem wdro_strong_duality
    (μhat : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (δ : ℝ)
    -- (A1) the transport cost is nonnegative, `c : S × S → ℝ₊`
    (hc_nonneg : ∀ x y : X, 0 ≤ c x y)
    -- (A1) the transport cost is (jointly) lower semicontinuous
    (hc_lsc : LowerSemicontinuous (fun p : X × X => c p.1 p.2))
    -- (A1) `c(x, y) = 0` iff `x = y`
    (hc_zero : ∀ x y : X, c x y = 0 ↔ x = y)
    -- (A2) the integrand `f` is upper semicontinuous
    (hf_usc : UpperSemicontinuous f)
    -- (A2) `f ∈ L¹(dμ̂)`
    (hf_int : Integrable f (μhat : Measure X))
    -- radius `δ > 0` (eq. (3))
    (hδ : 0 < δ) :
    droValue { μ : ProbabilityMeasure X | otCost c μ μhat ≤ δ } f
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * δ
              + expect μhat (fun x => sSup (Set.range (fun y : X => f y - lam * c x y))) } := by
  sorry

/-- **WDRO strong duality — univariate dual, stated via the inner dual `Lc`**
(Blanchet–Murthy Theorem 1(b) + Remark 1, eq. (9); `prose/wasserstein-dro-duality.md`
§1.2). Identical content to `wdro_strong_duality`, with the per-sample term written as
the inner dual function `φ_λ = Lc c f lam`:

  `I = inf_{λ ≥ 0} { λδ + 𝔼_{μ̂}[ φ_λ ] }`,   `φ_λ(x) = sup_y (f y − λ c x y)`.

This is the same theorem as `wdro_strong_duality` with the per-sample supremum written
as `Lc c f lam` — the two are definitionally equal (`Lc` unfolds to that supremum), so
this is *derived* from `wdro_strong_duality` rather than re-proved; the load-bearing
duality content lives in that one declaration. -/
theorem wdro_strong_duality_dualFn
    (μhat : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (δ : ℝ)
    -- (A1) nonnegative cost
    (hc_nonneg : ∀ x y : X, 0 ≤ c x y)
    -- (A1) lower semicontinuous cost
    (hc_lsc : LowerSemicontinuous (fun p : X × X => c p.1 p.2))
    -- (A1) `c(x, y) = 0` iff `x = y`
    (hc_zero : ∀ x y : X, c x y = 0 ↔ x = y)
    -- (A2) `f` upper semicontinuous
    (hf_usc : UpperSemicontinuous f)
    -- (A2) `f ∈ L¹(dμ̂)`
    (hf_int : Integrable f (μhat : Measure X))
    -- radius `δ > 0`
    (hδ : 0 < δ) :
    droValue { μ : ProbabilityMeasure X | otCost c μ μhat ≤ δ } f
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ v = lam * δ + expect μhat (Lc c f lam) } := by
  -- `Lc c f lam` unfolds (delta) to `fun x => sSup (Set.range (fun y => f y − lam · c x y))`,
  -- so the goal is definitionally equal to `wdro_strong_duality`.
  exact wdro_strong_duality μhat c f δ hc_nonneg hc_lsc hc_zero hf_usc hf_int hδ

end BlanchetMurthy2019
