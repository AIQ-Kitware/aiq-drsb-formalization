/-
# OT-DRO weak duality: the per-coupling Lagrangian bound (Mathlib-staging)

The **always-true `≤` (weak-duality) half** of optimal-transport DRO duality — the
Lagrangian bound that, taken to the `inf` over the multiplier and the `sup` over the
ambiguity ball, gives `v_P ≤ v_D`. This is the reusable kernel behind
`GaoKleywegt2023.weak_duality_prop1` / `BlanchetMurthy2019.wdro_strong_duality` (`≤`
direction) and hence behind the DRSB card cost bounds (`Drsb.wdrsb_cost_bound`,
`Drsb.sdrsb_cost_bound`) — see `PROOF_PIPELINE.md` §0: the cards need ONLY this half,
never the research-grade `≥` (attainment) direction.

Mathlib has NO optimal-transport / Kantorovich duality of any kind (grep-verified), so
this is a from-scratch contribution. See `FOUNDATIONS.md` (Chain 1).

STATUS: `sorry` (staging target). A COMPLETE proof of this exact bound exists in
`reference/V4.lean` (`wdro_lagrangian_bound`, proved against the reference-local
`Expect`/`Couplings`/`couplingCost2` vocabulary). The task is to PORT it to the
canonical `ForMathlib.OT` vocabulary (`expect`, `couplings`, `couplingCost`) — the
marginal-pushforward integral identities (`integral_map`, `integrable_map_measure`)
carry over verbatim. A T2 port for us, or a clean Fable ticket.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace ForMathlib.OT

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

/-- **Per-coupling Lagrangian bound** (the always-true `≤` half of OT-DRO duality).
For any coupling `π ∈ Π(μ, ν)` of a source `μ` with the nominal `ν`, any cost `c`, and
any multiplier `λ ≥ 0`,
`𝔼_μ[f] ≤ 𝔼_{y∼ν}[ sup_x (f x − λ c(x, y)) ] + λ · 𝔼_π[c]`.

Pointwise `f(x) ≤ φ_λ(y) + λ c(x, y)` with `φ_λ(y) = sup_x (f x − λ c x y)`; integrate
over `π` and use the marginals. Taking `inf_π 𝔼_π[c] = otCost c μ ν ≤ δ` and then
`sup_μ`, `inf_λ` yields `droValue (ball) f ≤ dualValue`. The `sup` boundedness `hbdd`
and the three integrability hypotheses make each expectation well defined. -/
theorem expect_le_dualIntegrand_add_lam_couplingCost
    (c : X → X → ℝ) (f : X → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X))
    (hπ : π ∈ couplings μ ν)
    (hbdd : ∀ y : X, BddAbove (Set.range (fun x => f x - lam * c x y)))
    (hf : Integrable f (μ : Measure X))
    (hφ : Integrable (fun y => sSup (Set.range (fun x => f x - lam * c x y))) (ν : Measure X))
    (hcost : Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X))) :
    expect μ f
      ≤ expect ν (fun y => sSup (Set.range (fun x => f x - lam * c x y)))
        + lam * couplingCost c π := by
  sorry

end ForMathlib.OT
