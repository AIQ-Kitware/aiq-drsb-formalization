/-
# Drsb — capstone: the DRSB paper's own claims, composed from the source libraries

The GaTech **Distributionally-Robust Schrödinger Bridge** paper is UNPUBLISHED. This
capstone states its load-bearing results — the two evaluation-card cost bounds — in
the shared `ForMathlib.OT` vocabulary, discharging each (in a later proof pass) from
the published source libraries:

* the value function `V` and optimal control are `ChenGeorgiouPavon2021`;
* the WDRSB worst-case cost bound is `BlanchetMurthy2019` / `GaoKleywegt2023`
  (Wasserstein-DRO strong duality) specialized to `f := V`, cost `‖·‖²`;
* the SDRSB bound / "Eq. 47" is `WangGaoXie2023` (Sinkhorn-DRO log-partition dual).

The two `expect μ V ≤ …` theorems are exactly the `wdrsb_cost_bound.yaml` /
`sdrsb_cost_bound.yaml` card claims `E_perturbed[V] ≤ E_worst-case[V]`.

STATUS: statements only (`sorry`). The DRSB "Eq. 47" internal number is from the
GaTech code, NOT a published PDF (see `prose/README.md`).
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.WeakDuality
import BlanchetMurthy2019.Basic
import GaoKleywegt2023.Basic
import WangGaoXie2023.Basic
import ChenGeorgiouPavon2021.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace Drsb

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

/-- The quadratic (Wasserstein-2) transport cost `c(x, y) = ‖x − y‖²` used by both
DRSB cards. -/
def sqCost (x y : X) : ℝ := ‖x - y‖ ^ 2

/-! ## The DRSB value function

The DRSB value function is the Chen–Georgiou–Pavon stochastic-optimal-control value
`V(x) = 𝔼[∫₀¹ ½‖u_t‖² dt + ρ·g(X₁) | X₀ = x]`, with optimal control `u* = −∇V`
(`ChenGeorgiouPavon2021.optimal_control_eq_neg_grad_value`). Here we take it as an
abstract `V : X → ℝ`; its provenance lives in `ChenGeorgiouPavon2021`. -/

/-! ## WDRSB worst-case cost bound  (card `wdrsb_cost_bound.yaml`) -/

/-- **WDRSB strong duality** — the Wasserstein-DRO worst-case value of the DRSB value
function `V` over the `W₂²`-ball equals the Blanchet–Murthy / Gao–Kleywegt univariate
dual, specialized to `f := V`, cost `c := ‖·‖²`. Discharged by
`BlanchetMurthy2019.wdro_strong_duality` (equivalently `GaoKleywegt2023.strong_duality_thm1`). -/
theorem wdrsb_strong_duality (p₀ : ProbabilityMeasure X) (V : X → ℝ) (ε : ℝ)
    (hV : Integrable V (p₀ : Measure X)) (hε : 0 < ε)
    (_hκ : GaoKleywegt2023.kappa sqCost V p₀ ≠ ⊤)
    (hfeas : (GaoKleywegt2023.ambiguitySet sqCost p₀ ε).Nonempty)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,
        BddAbove (Set.range (fun ξ => V ξ - lam * sqCost ξ ζ)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun ζ => sSup (Set.range (fun ξ => V ξ - lam * sqCost ξ ζ))) (p₀ : Measure X))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε →
        Integrable V (μ : Measure X))
    (hOT : ∀ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε → ∀ η : ℝ, 0 < η →
        ∃ π : ProbabilityMeasure (X × X), π ∈ couplings μ p₀ ∧ couplingCost sqCost π ≤ ε + η ∧
          Integrable (fun z : X × X => sqCost z.1 z.2) (π : Measure (X × X)))
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε ∧ r = expect μ V })
    (hattain : ∃ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε ∧
        expect μ V = GaoKleywegt2023.dualValue sqCost V p₀ ε) :
    droValue (wassersteinBall p₀ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } := by
  -- `sqCost` is symmetric, so Blanchet–Murthy's `Lc` = −(Gao–Kleywegt's `Φ`) pointwise
  have hsymm : ∀ a b : X, sqCost a b = sqCost b a := by
    intro a b; simp only [sqCost]; rw [norm_sub_rev]
  have hLcPhi : ∀ (lam : ℝ) (x : X),
      BlanchetMurthy2019.Lc sqCost V lam x = -(GaoKleywegt2023.Phi sqCost V lam x) := by
    intro lam x
    rw [BlanchetMurthy2019.Lc, GaoKleywegt2023.Phi, ← Real.sSup_neg]
    congr 1
    rw [← Set.image_neg_eq_neg, ← Set.range_comp]
    congr 1; funext ξ; simp only [Function.comp_apply]; rw [hsymm x ξ]; ring
  have hexpLc : ∀ lam : ℝ, expect p₀ (BlanchetMurthy2019.Lc sqCost V lam)
      = - expect p₀ (fun ζ => GaoKleywegt2023.Phi sqCost V lam ζ) := by
    intro lam
    unfold expect
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ζ => hLcPhi lam ζ))
  -- apply the proved general strong duality (specialized to `sqCost, V, p₀, ε`)
  have hsd := GaoKleywegt2023.strong_duality_thm1 sqCost V p₀ ε hV hε _hκ hfeas hbdd hφint
    hΨμ hOT hbddP hattain
  rw [show droValue (wassersteinBall p₀ ε) V = GaoKleywegt2023.primalValue sqCost V p₀ ε from rfl,
    hsd, GaoKleywegt2023.dualValue]
  -- the two dual sets coincide (Φ-form = Lc-form)
  congr 1
  ext v
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨lam, hlam, by rw [hexpLc lam]; ring⟩
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨lam, hlam, by rw [hexpLc lam]; ring⟩

/-- **WDRSB cost bound** (the `wdrsb_cost_bound.yaml` claim `E_perturbed[V] ≤ E_wc[V]`):
for any source `μ` inside the Wasserstein-2 ball of radius `ε` around the nominal `p₀`,
the expected cost is bounded by the WDRO dual worst-case value.

**Proved** — the `≤` (weak-duality) direction, which is all the card needs. It composes
`ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost` (the per-coupling Lagrangian
kernel) with `sqCost`'s symmetry (so the kernel's dual integrand matches Blanchet–Murthy's
`Lc`) and `couplingCost ≤ ε`.

The extra hypotheses are the **formalization edges** that make the ideal claim provable
(cf. AGENTS.md §6): `hV`/`hbdd`/`hLc` are the integrability/boundedness regularity that
makes the three expectations well defined, and `hOT` is the **optimal-transport
attainment edge** — that the constraint `W₂²(μ,p₀) ≤ ε` is witnessed by a genuine
integrable-cost coupling. `hOT` stands in for the OT measurable-selection/attainment
result that is *not in Mathlib* (the T4 seam), stated as a hypothesis rather than proved;
everything else is discharged. -/
theorem wdrsb_cost_bound (p₀ : ProbabilityMeasure X) (V : X → ℝ) (ε : ℝ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ wassersteinBall p₀ ε)
    -- regularity (integrability / sup-boundedness):
    (hV : Integrable V (μ : Measure X))
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ y : X,
        BddAbove (Set.range (fun x => V x - lam * sqCost x y)))
    (hLc : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (BlanchetMurthy2019.Lc sqCost V lam) (p₀ : Measure X))
    -- OT-attainment edge: the W₂² ≤ ε constraint is witnessed by an integrable-cost coupling
    (hOT : W2sq μ p₀ ≤ ε →
        ∃ π ∈ couplings μ p₀, couplingCost sqCost π ≤ ε ∧
          Integrable (fun z : X × X => sqCost z.1 z.2) (π : Measure (X × X))) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } := by
  -- discharge the OT edge: get the witnessing coupling
  obtain ⟨π, hπ, hcost_le, hcost_int⟩ := hOT hμ
  -- sqCost is symmetric, so Blanchet–Murthy's `Lc` IS the kernel's dual integrand
  have hsymm : ∀ x y : X, sqCost x y = sqCost y x := by
    intro x y; simp only [sqCost]; rw [norm_sub_rev]
  have hLc_eq : ∀ lam : ℝ, BlanchetMurthy2019.Lc sqCost V lam
      = fun y => sSup (Set.range (fun x => V x - lam * sqCost x y)) := by
    intro lam; funext a
    have h : (fun y => V y - lam * sqCost a y) = (fun x => V x - lam * sqCost x a) := by
      funext t; rw [hsymm a t]
    show sSup (Set.range (fun y => V y - lam * sqCost a y))
        = sSup (Set.range (fun x => V x - lam * sqCost x a))
    rw [h]
  -- `expect μ V` is a lower bound of the dual set
  refine le_csInf ⟨_, 0, le_rfl, rfl⟩ ?_
  rintro v ⟨lam, hlam, rfl⟩
  have hφ : Integrable (fun y => sSup (Set.range (fun x => V x - lam * sqCost x y)))
      (p₀ : Measure X) := by rw [← hLc_eq lam]; exact hLc lam hlam
  have key := ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost
    sqCost V lam hlam μ p₀ π hπ (hbdd lam hlam) hV hφ hcost_int
  rw [← hLc_eq lam] at key
  have hstep : lam * couplingCost sqCost π ≤ lam * ε :=
    mul_le_mul_of_nonneg_left hcost_le hlam
  linarith

/-! ## SDRSB worst-case cost bound and "Eq. 47"  (card `sdrsb_cost_bound.yaml`) -/

/-- **SDRSB cost bound** (the `sdrsb_cost_bound.yaml` claim): any source inside the
Sinkhorn ball (external reference `ν`) has expected cost bounded by the Sinkhorn-DRO dual
worst-case value. **PROVED** — the `≤`/weak-duality direction, the entropic analogue of
`wdrsb_cost_bound`, composing the proved Sinkhorn weak-duality kernel
`WangGaoXie2023.sinkhorn_weak_duality_kernel` (the per-point Gibbs/DV bound integrated over
`p₀`) with `budget ≤ ε` and `le_csInf`.

Formalization edges (honest hypotheses, cf. AGENTS.md §6; the audit fixed the ball to
share the external reference `ν` — `prose/sinkhorn-dro-duality.md`):
* `hSink` is the **Sinkhorn attainment + disintegration edge**: the `W_{κ,ν}(p₀,μ) ≤ ε`
  constraint is realized by a conditional family `P` (each `≪ ν`) with `μ` its second
  marginal (`expect μ V = ∫∫ V dP dp₀`), disintegrated budget `≤ ε`, and the standard
  DV/aggregate integrability. This bundles the OT-attainment (not in Mathlib), the
  `condKernel` disintegration, and the KL chain rule into one edge — the entropic
  counterpart of `wdrsb_cost_bound`'s `hOT`.
* **`0 < lam`** in the dual set (not `0 ≤ lam`): at `lam = 0` the Lean `logPartition`
  degenerates to `0` (junk from `0/0`) rather than the paper's `λ↓0` ess-sup limit, so
  the `λ=0` term is excluded (documented limitation — the ess-sup convention is unencoded).
-/
theorem sdrsb_cost_bound (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ sinkhornBall p₀ ν κ ε)
    (hSink : Wkappa κ ν p₀ μ ≤ ε →
      ∃ P : X → Measure X,
        (∀ x, IsProbabilityMeasure (P x)) ∧ (∀ x, P x ≪ (ν : Measure X)) ∧
        expect μ V = (∫ x, (∫ y, V y ∂(P x)) ∂(p₀ : Measure X)) ∧
        (∫ x, ((∫ y, sqCost x y ∂(P x)) + κ * klReal (P x) (ν : Measure X))
            ∂(p₀ : Measure X)) ≤ ε ∧
        (∀ x, Integrable V (P x)) ∧ (∀ x, Integrable (fun y => sqCost x y) (P x)) ∧
        (∀ x, Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x)) ∧
        (∀ lam, 0 < lam → ∀ x, Integrable
            (fun y => Real.exp ((V y - lam * sqCost x y) / (lam * κ))) (ν : Measure X)) ∧
        Integrable (fun x => ∫ y, V y ∂(P x)) (p₀ : Measure X) ∧
        Integrable (fun x => ∫ y, sqCost x y ∂(P x)) (p₀ : Measure X) ∧
        Integrable (fun x => klReal (P x) (ν : Measure X)) (p₀ : Measure X) ∧
        (∀ lam, 0 < lam → Integrable
            (fun x => WangGaoXie2023.logPartition ν sqCost V κ lam x) (p₀ : Measure X))) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  obtain ⟨P, hP, hac, hVdis, hbudget, hf_P, hc_P, h_llr, h_exp, hI_V, hI_c, hI_kl, hI_lp⟩ :=
    hSink hμ
  refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
  rintro v ⟨lam, hlam, rfl⟩
  have key := WangGaoXie2023.sinkhorn_weak_duality_kernel p₀ ν sqCost V κ lam hκ hlam P hP hac
    hf_P hc_P h_llr (h_exp lam hlam) hI_V hI_c hI_kl (hI_lp lam hlam)
  have hb := mul_le_mul_of_nonneg_left hbudget (le_of_lt hlam)
  rw [hVdis]
  simp only [WangGaoXie2023.sinkhornDualObjective, expect]
  linarith [key, hb]

/-- **SDRSB strong duality** — the Sinkhorn-DRO worst-case value of `V` over the Sinkhorn
ball equals the Wang–Gao–Xie log-partition dual (`f := V`, cost `‖·‖²`). Completes the
SDRSB capstone: `le_antisymm` of `droValue ≤ dual` (each source's `sdrsb_cost_bound`,
`csSup_le`) and `dual ≤ droValue` (the attaining worst-case measure, `le_csSup`). Same
honest edges as `sdrsb_cost_bound`, now `∀ μ` (`hSinkAll`), plus the attainment edge
(`hattain`) and `hbddP`; dual over `0 < lam`. -/
theorem sdrsb_strong_duality (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ)
    (hκ : 0 < κ)
    (hSinkAll : ∀ μ : ProbabilityMeasure X, μ ∈ sinkhornBall p₀ ν κ ε →
      (Wkappa κ ν p₀ μ ≤ ε →
        ∃ P : X → Measure X,
          (∀ x, IsProbabilityMeasure (P x)) ∧ (∀ x, P x ≪ (ν : Measure X)) ∧
          expect μ V = (∫ x, (∫ y, V y ∂(P x)) ∂(p₀ : Measure X)) ∧
          (∫ x, ((∫ y, sqCost x y ∂(P x)) + κ * klReal (P x) (ν : Measure X))
              ∂(p₀ : Measure X)) ≤ ε ∧
          (∀ x, Integrable V (P x)) ∧ (∀ x, Integrable (fun y => sqCost x y) (P x)) ∧
          (∀ x, Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x)) ∧
          (∀ lam, 0 < lam → ∀ x, Integrable
              (fun y => Real.exp ((V y - lam * sqCost x y) / (lam * κ))) (ν : Measure X)) ∧
          Integrable (fun x => ∫ y, V y ∂(P x)) (p₀ : Measure X) ∧
          Integrable (fun x => ∫ y, sqCost x y ∂(P x)) (p₀ : Measure X) ∧
          Integrable (fun x => klReal (P x) (ν : Measure X)) (p₀ : Measure X) ∧
          (∀ lam, 0 < lam → Integrable
              (fun x => WangGaoXie2023.logPartition ν sqCost V κ lam x) (p₀ : Measure X))))
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ sinkhornBall p₀ ν κ ε ∧ r = expect μ V })
    (hattain : ∃ μ : ProbabilityMeasure X, μ ∈ sinkhornBall p₀ ν κ ε ∧
        expect μ V = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam }) :
    droValue (sinkhornBall p₀ ν κ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ?_ ?_
    · obtain ⟨μ, hμ, _⟩ := hattain; exact ⟨expect μ V, μ, hμ, rfl⟩
    · rintro a ⟨μ, hμ, rfl⟩
      exact sdrsb_cost_bound p₀ ν V κ ε hκ μ hμ (hSinkAll μ hμ)
  · obtain ⟨μ, hμ, hμeq⟩ := hattain
    rw [← hμeq]
    exact le_csSup hbddP ⟨μ, hμ, rfl⟩

/-- **DRSB "Eq. 47"** — the SDRSB bound as coded in the GaTech repo
(`compute_bound.py` Term3 / `wdrsb_bridge.py`): the worst-case cost minus a
log-partition term over the terminal reference `ν`,
`Bound = E_wc[V] − ρ · log 𝔼_ν[e^{g(X₁)}]`.

⚠ Reconstructed from the code + coordinator (the DRSB manuscript is unpublished);
"Eq. 47" is the manuscript's internal number, not a published reference. This is
the `WangGaoXie2023.logPartition` term with `f := ρ·g`, `c := 0` at the terminal
layer. -/
noncomputable def eq47Bound (ν : ProbabilityMeasure X) (g : X → ℝ) (ρ Ewc : ℝ) : ℝ :=
  Ewc - ρ * Real.log (∫ x, Real.exp (g x) ∂(ν : Measure X))

end Drsb
