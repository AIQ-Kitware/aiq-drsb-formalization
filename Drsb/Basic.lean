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
theorem wdrsb_strong_duality (p₀ : ProbabilityMeasure X) (V : X → ℝ) (ε : ℝ) :
    droValue (wassersteinBall p₀ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } := by
  sorry

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

/-- **SDRSB strong duality** — the Sinkhorn-DRO worst-case value of `V` over the
Sinkhorn ball equals the Wang–Gao–Xie log-partition dual, specialized to `f := V`,
cost `c := ‖·‖²`. (Paper/Lean symbol convention: `κ` = entropic regularizer, `ε` =
ball radius; `ν` is the entropic-OT reference measure.) Discharged by
`WangGaoXie2023.strong_duality`. -/
theorem sdrsb_strong_duality (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ) :
    droValue (sinkhornBall p₀ κ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  sorry

/-- **SDRSB cost bound** (the `sdrsb_cost_bound.yaml` claim): any source inside the
Sinkhorn ball has expected cost bounded by the Sinkhorn-DRO dual worst-case value. -/
theorem sdrsb_cost_bound (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ sinkhornBall p₀ κ ε) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  sorry

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
