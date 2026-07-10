/-
# Blanchet–Murthy (2019): optimal-transport DRO strong duality

Statement-only scaffold (proof bodies deferred) for the primary strong-duality result of

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
import ForMathlib.OptimalTransport.DroValue
import ForMathlib.OptimalTransport.WeakDuality

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

omit [NormedAddCommGroup X] in
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

Body is placeholder (statement-only scaffold). -/
theorem wdro_strong_duality
    (μhat : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (δ : ℝ)
    -- the transport cost is symmetric (Blanchet–Murthy's ball uses `μ̂` as first coupling
    -- marginal; the scaffold writes `otCost c μ μ̂`, which coincides for symmetric `c`
    -- — in particular the DRSB `‖·‖²`; see the docstring's faithfulness note):
    (hc_symm : ∀ x y : X, c x y = c y x)
    -- weak-duality edges (as in `GaoKleywegt2023.weak_duality_prop1`):
    (hfeas : { μ : ProbabilityMeasure X | otCost c μ μhat ≤ δ }.Nonempty)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ y : X,
        BddAbove (Set.range (fun x => f x - lam * c x y)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun y => sSup (Set.range (fun x => f x - lam * c x y))) (μhat : Measure X))
    (hfμ : ∀ μ : ProbabilityMeasure X, otCost c μ μhat ≤ δ → Integrable f (μ : Measure X))
    (hOT : ∀ μ : ProbabilityMeasure X, otCost c μ μhat ≤ δ → ∀ η : ℝ, 0 < η →
        ∃ π : ProbabilityMeasure (X × X), π ∈ couplings μ μhat ∧ couplingCost c π ≤ δ + η ∧
          Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X)))
    -- the `≥` direction — **the duality gap is zero**. Strictly weaker than the customary
    -- "a worst-case distribution attains the dual": that bundles *attainment* (a separate
    -- statement, false without compactness) with the vanishing gap, and this proof only ever
    -- used the gap. `dualValue_le_droValue_of_attaining_measure` is the receipt.
    (hge : sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * δ + expect μhat (fun x => sSup (Set.range (fun y => f y - lam * c x y))) }
        ≤ droValue { μ : ProbabilityMeasure X | otCost c μ μhat ≤ δ } f) :
    droValue { μ : ProbabilityMeasure X | otCost c μ μhat ≤ δ } f
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * δ
              + expect μhat (fun x => sSup (Set.range (fun y : X => f y - lam * c x y))) } := by
  -- the `BddAbove` gate: `hbdd` at `lam = 0` says `f` is bounded above
  haveI : IsProbabilityMeasure (μhat : Measure X) := μhat.2
  have hne : Nonempty X := nonempty_of_isProbabilityMeasure (μhat : Measure X)
  have hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
      otCost c μ μhat ≤ δ ∧ r = expect μ f } :=
    ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range { μ | otCost c μ μhat ≤ δ } f
      (ForMathlib.OT.bddAbove_range_of_bddAbove_dualIntegrand f c hne.some (hbdd 0 le_rfl hne.some))
      hfμ
  -- symmetry: the dual integrand `fun x => sup_y (f y − λc(x,y))` equals the kernel's
  -- `fun y => sup_x (f x − λc(x,y))`
  have hAB : ∀ lam : ℝ, (fun x => sSup (Set.range (fun y => f y - lam * c x y)))
      = (fun y => sSup (Set.range (fun x => f x - lam * c x y))) := by
    intro lam; funext t
    have h : (fun y => f y - lam * c t y) = (fun x => f x - lam * c x t) := by
      funext s; rw [hc_symm t s]
    rw [h]
  refine le_antisymm ?_ ?_
  · refine csSup_le ?_ ?_
    · obtain ⟨μ, hμ⟩ := hfeas; exact ⟨expect μ f, μ, hμ, rfl⟩
    · rintro a ⟨μ, hμ, rfl⟩
      refine le_csInf ⟨_, 0, le_refl 0, rfl⟩ ?_
      rintro d ⟨lam, hlam, rfl⟩
      rw [hAB lam]
      refine le_of_forall_pos_le_add fun η hη => ?_
      have hη' : (0 : ℝ) < η / (lam + 1) := div_pos hη (by linarith)
      obtain ⟨π, hπ, hcost, hcint⟩ := hOT μ hμ (η / (lam + 1)) hη'
      have hker := ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost
        c f lam hlam μ μhat π hπ (hbdd lam hlam) (hfμ μ hμ) (hφint lam hlam) hcint
      have h1 : lam * couplingCost c π ≤ lam * δ + lam * (η / (lam + 1)) := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left hcost hlam
      have h2 : lam * (η / (lam + 1)) ≤ η := by
        rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < lam + 1)]
        nlinarith [hη, hlam]
      linarith [hker, h1, h2]
  · exact hge

omit [NormedAddCommGroup X] in
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
    (hc_symm : ∀ x y : X, c x y = c y x)
    (hfeas : { μ : ProbabilityMeasure X | otCost c μ μhat ≤ δ }.Nonempty)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ y : X,
        BddAbove (Set.range (fun x => f x - lam * c x y)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun y => sSup (Set.range (fun x => f x - lam * c x y))) (μhat : Measure X))
    (hfμ : ∀ μ : ProbabilityMeasure X, otCost c μ μhat ≤ δ → Integrable f (μ : Measure X))
    (hOT : ∀ μ : ProbabilityMeasure X, otCost c μ μhat ≤ δ → ∀ η : ℝ, 0 < η →
        ∃ π : ProbabilityMeasure (X × X), π ∈ couplings μ μhat ∧ couplingCost c π ≤ δ + η ∧
          Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X)))
    (hge : sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * δ + expect μhat (fun x => sSup (Set.range (fun y => f y - lam * c x y))) }
        ≤ droValue { μ : ProbabilityMeasure X | otCost c μ μhat ≤ δ } f) :
    droValue { μ : ProbabilityMeasure X | otCost c μ μhat ≤ δ } f
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ v = lam * δ + expect μhat (Lc c f lam) } := by
  -- `Lc c f lam` unfolds (delta) to `fun x => sSup (Set.range (fun y => f y − lam · c x y))`,
  -- so the goal is definitionally equal to `wdro_strong_duality`.
  exact wdro_strong_duality μhat c f δ hc_symm hfeas hbdd hφint hfμ hOT hge

end BlanchetMurthy2019
