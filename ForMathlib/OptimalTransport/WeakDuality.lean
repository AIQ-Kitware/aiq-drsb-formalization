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

STATUS: PROVED. Ported from `reference/V4.lean` (`wdro_lagrangian_bound`, proved against
the reference-local `Expect`/`Couplings`/`couplingCost2` vocabulary) to the canonical
`ForMathlib.OT` vocabulary (`expect`, `couplings`, `couplingCost`) and generalized from
the DRSB quadratic cost `‖x − y‖²` to an arbitrary `c : X → X → ℝ`; the
marginal-pushforward integral identities (`integral_map`, `integrable_map_measure`)
carried over verbatim. Remaining for the card path: the `inf`/`sup` ASSEMBLY on top of
this kernel (`GaoKleywegt2023.weak_duality_prop1`) — see `PROOF_PIPELINE.md`.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace ForMathlib.OT

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

omit [NormedAddCommGroup X] in
/-- **Per-coupling Lagrangian bound** (the always-true `≤` half of OT-DRO duality).
For any coupling `π ∈ Π(μ, ν)` of a source `μ` with the nominal `ν`, any cost `c`, and
any multiplier `λ` (the `λ ≥ 0` gate matters only for the downstream assembly, not this
bound),
`𝔼_μ[f] ≤ 𝔼_{y∼ν}[ sup_x (f x − λ c(x, y)) ] + λ · 𝔼_π[c]`.

Pointwise `f(x) ≤ φ_λ(y) + λ c(x, y)` with `φ_λ(y) = sup_x (f x − λ c x y)`; integrate
over `π` and use the marginals. Taking `inf_π 𝔼_π[c] = otCost c μ ν ≤ δ` and then
`sup_μ`, `inf_λ` yields `droValue (ball) f ≤ dualValue`. The `sup` boundedness `hbdd`
and the three integrability hypotheses make each expectation well defined.

Ported from the complete proof in `reference/V4.lean` (`wdro_lagrangian_bound`),
generalized from the DRSB quadratic cost `‖x − y‖²` to an arbitrary `c : X → X → ℝ`
and restated in the canonical `ForMathlib.OT` vocabulary. -/
theorem expect_le_dualIntegrand_add_lam_couplingCost
    (c : X → X → ℝ) (f : X → ℝ) (lam : ℝ) (_hlam : 0 ≤ lam)
    (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X))
    (hπ : π ∈ couplings μ ν)
    (hbdd : ∀ y : X, BddAbove (Set.range (fun x => f x - lam * c x y)))
    (hf : Integrable f (μ : Measure X))
    (hφ : Integrable (fun y => sSup (Set.range (fun x => f x - lam * c x y))) (ν : Measure X))
    (hcost : Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X))) :
    expect μ f
      ≤ expect ν (fun y => sSup (Set.range (fun x => f x - lam * c x y)))
        + lam * couplingCost c π := by
  classical
  set g : X → ℝ := fun y => sSup (Set.range (fun x => f x - lam * c x y)) with hgdef
  -- marginal identities: μ = fst_# π, ν = snd_# π
  have hfst : (μ : Measure X) = Measure.map Prod.fst (π : Measure (X × X)) := hπ.1.symm
  have hsnd : (ν : Measure X) = Measure.map Prod.snd (π : Measure (X × X)) := hπ.2.symm
  have hfae : AEStronglyMeasurable f (Measure.map Prod.fst (π : Measure (X × X))) :=
    hfst ▸ hf.1
  have hgae : AEStronglyMeasurable g (Measure.map Prod.snd (π : Measure (X × X))) :=
    hsnd ▸ hφ.1
  -- rewrite both expectations as integrals against π via its marginals
  have e1 : expect μ f = ∫ z, f z.1 ∂(π : Measure (X × X)) := by
    rw [expect, hfst, integral_map measurable_fst.aemeasurable hfae]
  have e2 : expect ν g = ∫ z, g z.2 ∂(π : Measure (X × X)) := by
    rw [expect, hsnd, integral_map measurable_snd.aemeasurable hgae]
  -- transport the integrability hypotheses onto π
  have hfpi : Integrable (fun z : X × X => f z.1) (π : Measure (X × X)) :=
    (integrable_map_measure hfae measurable_fst.aemeasurable).mp (hfst ▸ hf)
  have hgpi : Integrable (fun z : X × X => g z.2) (π : Measure (X × X)) :=
    (integrable_map_measure hgae measurable_snd.aemeasurable).mp (hsnd ▸ hφ)
  -- pointwise: f(x) ≤ φ_λ(y) + λ c(x, y), from x being in the sup's range
  have hpt : ∀ z : X × X, f z.1 ≤ g z.2 + lam * c z.1 z.2 := by
    intro z
    have hmem : f z.1 - lam * c z.1 z.2
        ∈ Set.range (fun x => f x - lam * c x z.2) := ⟨z.1, rfl⟩
    have := le_csSup (hbdd z.2) hmem
    simp only [hgdef]; linarith
  rw [e1, e2, show couplingCost c π = ∫ z, c z.1 z.2 ∂(π : Measure (X × X)) from rfl]
  calc ∫ z, f z.1 ∂(π : Measure (X × X))
      ≤ ∫ z, (g z.2 + lam * c z.1 z.2) ∂(π : Measure (X × X)) :=
        integral_mono hfpi (hgpi.add (hcost.const_mul lam)) hpt
    _ = (∫ z, g z.2 ∂(π : Measure (X × X)))
          + lam * ∫ z, c z.1 z.2 ∂(π : Measure (X × X)) := by
        rw [integral_add hgpi (hcost.const_mul lam), integral_const_mul]

end ForMathlib.OT
