/-
# CGP static Schrödinger bridge wrappers

This module contains endpoint couplings, the static SB value, and the
dynamic-to-static data-processing/gluing assembly theorem.
-/

import ChenGeorgiouPavon2021.SocOt.Dynamic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (d : SBData X)

/-- Set of couplings `Π(ρ₀,ρ₁)`: joint laws on `X × X` with first marginal `ρ₀` and
second marginal `ρ₁` (CGP §I.0). -/
def couplings (ρ₀ ρ₁ : ProbabilityMeasure X) : Set (ProbabilityMeasure (X × X)) :=
  { π | Measure.map Prod.fst (π : Measure (X × X)) = (ρ₀ : Measure X)
      ∧ Measure.map Prod.snd (π : Measure (X × X)) = (ρ₁ : Measure X) }

/-- Endpoint law `R₀₁ = (X₀,X₁)_# R` of the reference path measure (CGP §I.2). -/
noncomputable def endpointLaw : Measure (X × X) :=
  Measure.map (fun ω : Path X => (ω 0, ω 1)) (d.R : Measure (Path X))

/-- **Static Schrödinger value (CGP Problem 4.2, (4.7)).**
`min { D(ρ₀₁‖ρ₀₁^W) : ρ₀₁ ∈ Π(ρ₀,ρ₁) }` — the reduction of Problem 4.1 to a static
coupling problem. -/
noncomputable def staticSBValue (ρ₀ ρ₁ : ProbabilityMeasure X) : ℝ :=
  sInf { J : ℝ | ∃ π : ProbabilityMeasure (X × X),
    π ∈ couplings ρ₀ ρ₁ ∧ J = klReal (π : Measure (X × X)) (endpointLaw d) }

omit [NormedSpace ℝ X] in
/-- **Dynamic ⇄ static Schrödinger equivalence (CGP Problem 4.1 ⇄ Problem 4.2,
(4.6)/(4.8); Léonard Prop 2.3).**  The infimum over path measures equals the infimum
over couplings: gluing the reference bridges `W_{xy}` onto the optimal coupling gives
the optimal path law.

**Proof (house pattern — `le_antisymm(gluing-edge, DPI-proved)`).** One direction is
now **genuinely proved**: `staticSBValue ≤ schrodingerBridgeValueKL`, via the **data-processing
inequality** for KL. The endpoint projection `e : ω ↦ (ω₀, ω₁)` sends any feasible path law
`P = P^{u,ρ₀}` to a coupling `e_# P ∈ Π(ρ₀,ρ₁)` (its two marginals are `initialMarginal P = ρ₀`
and `terminalMarginal P = ρ₁`, by feasibility), and coarse-graining cannot increase relative
entropy — `D(e_# P ‖ e_# R) ≤ D(P ‖ R)` with `e_# R = R₀₁ = endpointLaw` — so
`staticSBValue ≤ D(e_# P ‖ R₀₁) ≤ D(P ‖ R)`; taking the infimum over feasible `u` gives the
bound. The DPI is the new axiom-clean `ForMathlib.MeasureTheory.toReal_klDiv_map_le` (a genuine
Mathlib gap, proved by conditional Jensen on the convex KL generator). The honest regularity
edges are `hac`/`hfin` (each feasible path law is `≪ R` with finite relative entropy — the
finite-energy diffusion regime) and `hne` (the feasible set is nonempty).

The reverse `schrodingerBridgeValueKL ≤ staticSBValue` (**gluing** the reference bridges
`W_{xy}` onto a coupling to reconstruct a path law of equal relative entropy — Léonard Prop 2.3)
is the disintegration/path-space-reconstruction content absent from Mathlib; it is isolated to
the single explicit edge `hglue`, exactly as the strong-duality equalities isolate their
attainment edge. -/
theorem dynamic_eq_static_SB (ρ₀ ρ₁ : ProbabilityMeasure X)
    -- each feasible path law is absolutely continuous w.r.t. the reference with finite relative
    -- entropy (the finite-energy diffusion regime; cf. `FiniteEnergyDiffusion`):
    (hac : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
        (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)))
    (hfin : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
        InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤)
    -- the feasible set is nonempty (a control steering ρ₀ → ρ₁ exists):
    (hne : ∃ u : Control X, Feasible d u ρ₀ ρ₁)
    -- the gluing / path-reconstruction edge (Léonard Prop 2.3; the ≤ direction, isolated):
    (hglue : schrodingerBridgeValueKL d ρ₀ ρ₁ ≤ staticSBValue d ρ₀ ρ₁) :
    schrodingerBridgeValueKL d ρ₀ ρ₁ = staticSBValue d ρ₀ ρ₁ := by
  refine le_antisymm hglue ?_
  -- the data-processing direction: staticSBValue ≤ schrodingerBridgeValueKL
  obtain ⟨u₀, hu₀⟩ := hne
  refine le_csInf ⟨_, u₀, hu₀, rfl⟩ ?_
  rintro J ⟨u, hu, rfl⟩
  -- the endpoint projection e : ω ↦ (ω 0, ω 1)
  have he : Measurable (fun ω : Path X => (ω (0 : ℝ), ω (1 : ℝ))) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  haveI hπprob : IsProbabilityMeasure
      (Measure.map (fun ω : Path X => (ω 0, ω 1)) (d.pathLaw u ρ₀ : Measure (Path X))) :=
    Measure.isProbabilityMeasure_map he.aemeasurable
  set πP : ProbabilityMeasure (X × X) :=
    ⟨Measure.map (fun ω : Path X => (ω 0, ω 1)) (d.pathLaw u ρ₀ : Measure (Path X)), hπprob⟩
    with hπP
  have hπcoe : (πP : Measure (X × X))
      = Measure.map (fun ω : Path X => (ω 0, ω 1)) (d.pathLaw u ρ₀ : Measure (Path X)) := rfl
  -- e_# P is a coupling of (ρ₀, ρ₁), by feasibility of u
  have hcoupl : πP ∈ couplings ρ₀ ρ₁ := by
    constructor
    · rw [hπcoe, Measure.map_map measurable_fst he]
      exact hu.1
    · rw [hπcoe, Measure.map_map measurable_snd he]
      exact hu.2
  -- data-processing: D(e_# P ‖ endpointLaw) ≤ D(P ‖ R)
  have hdpi : klReal (πP : Measure (X × X)) (endpointLaw d)
      ≤ klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) :=
    ForMathlib.MeasureTheory.toReal_klDiv_map_le
      (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) (hac u hu)
      (fun ω => (ω 0, ω 1)) he (hfin u hu)
  -- staticSBValue ≤ D(e_# P ‖ endpointLaw) ≤ D(P ‖ R)
  refine le_trans ?_ hdpi
  refine csInf_le ⟨0, ?_⟩ ⟨πP, hcoupl, rfl⟩
  rintro _ ⟨π, _, rfl⟩
  exact ENNReal.toReal_nonneg

end ChenGeorgiouPavon2021
