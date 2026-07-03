/-
# Drsb — capstone: the DRSB paper's own claims, composed from the source libraries

The GaTech **Distributionally-Robust Schrödinger Bridge** paper and its "TwoPager"
companion are UNPUBLISHED. This capstone states their load-bearing results in the
shared `ForMathlib.OT` vocabulary, discharging each (in a later proof pass) from the
published source libraries:

* the value function `V` and optimal control are `ChenGeorgiouPavon2021`;
* the WDRSB worst-case cost bound is `BlanchetMurthy2019` / `GaoKleywegt2023`
  (Wasserstein-DRO strong duality) specialized to `f := V`, cost `‖·‖²`;
* the SDRSB bound / "Eq. 47" is `WangGaoXie2023` (Sinkhorn-DRO log-partition dual);
* the TwoPager PAC-Bayes bound is `Alquier2024` (Catoni).

The two `expect μ V ≤ …` theorems are exactly the `wdrsb_cost_bound.yaml` /
`sdrsb_cost_bound.yaml` card claims `E_perturbed[V] ≤ E_worst-case[V]`.

STATUS: statements only (`sorry`). The DRSB "Eq. 47" / TwoPager equation numbers are
from the GaTech code + coordinator, NOT a published PDF (see `prose/README.md`).
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import BlanchetMurthy2019.Basic
import GaoKleywegt2023.Basic
import WangGaoXie2023.Basic
import Alquier2024.Basic
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

/-! ## TwoPager Theorem 4 — PAC-Bayes for the clipped terminal-cost network

⚠ Unpublished DRSB companion ("TwoPager"); Eqs. (116)/(126). Discharged by
`Alquier2024.catoni_pacBayes_bound` (Catoni), specialized to a single controlled
path law `P` (posterior), reference path law `Q` (prior), and loss `g ∘ term`
clipped to `[−C, C]` (range `2C`, giving the Hoeffding term `ε·C²/(2n)`). -/
theorem twopager_theorem4 {Θ : Type*} [MeasurableSpace Θ]
    (P Q : ProbabilityMeasure Θ)          -- controlled (posterior) and reference (prior) path laws
    (term : Θ → X) (hterm : Measurable term)   -- terminal-state map X₁ = term(trajectory)
    (g : X → ℝ) (C : ℝ) (hg : ∀ x, |g x| ≤ C) -- terminal-cost net, clipped to [−C, C]
    (n : ℕ) (hn : 0 < n)                  -- number of terminal samples
    (ε : ℝ) (hε : 0 < ε)                  -- PAC-Bayes inverse-temperature (TwoPager's ε)
    (ς : ℝ) (hς0 : 0 < ς) (hς1 : ς < 1)   -- confidence level
    (hPQ : (P : Measure Θ) ≪ (Q : Measure Θ)) :
    -- With probability ≥ 1 − ς over an i.i.d. terminal sample S ∼ Pⁿ, the population
    -- terminal-cost mean is bounded by the empirical mean + the PAC-Bayes/KL term +
    -- the Hoeffding term (TwoPager Eq. (126)):
    (Measure.pi (fun _ : Fin n => (P : Measure Θ)))
        { S : Fin n → Θ |
          ∫ ω, g (term ω) ∂(P : Measure Θ)
            ≤ (1 / (n : ℝ)) * ∑ i, g (term (S i))
              + ((InformationTheory.klDiv (P : Measure Θ) (Q : Measure Θ)).toReal
                  + Real.log (1 / ς)) / ε
              + ε * C ^ 2 / (2 * (n : ℝ)) }
      ≥ ENNReal.ofReal (1 - ς) := by
  sorry

end Drsb
