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
for any source `μ` inside the Wasserstein-2 ball of radius `ε` around the nominal
`p₀`, the expected cost is bounded by the WDRO dual worst-case value. -/
theorem wdrsb_cost_bound (p₀ : ProbabilityMeasure X) (V : X → ℝ) (ε : ℝ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ wassersteinBall p₀ ε) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } := by
  sorry

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
