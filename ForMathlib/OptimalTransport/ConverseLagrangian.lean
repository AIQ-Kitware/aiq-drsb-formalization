/-
# The converse Lagrangian bound: the DRO dual value is achieved by a pushforward

`ForMathlib.OptimalTransport.WeakDuality` proves the always-true `≤` half of OT-DRO duality:
for every coupling `π ∈ Π(μ, ν)`,

`𝔼_μ[f] ≤ 𝔼_{y∼ν}[ φ_λ(y) ] + λ · 𝔼_π[c]`,   `φ_λ(y) = sup_x (f x − λ c(x,y))`.

This file proves the **converse**: that bound is *achieved*, to within any `ε > 0`, by an explicit
coupling — the pushforward of the nominal `ν` along a measurable near-maximizer of the
`c`-transform. Together the two give the exact Lagrangian value

`sup_{π ∈ Π(·, ν)} ( 𝔼_μ[f] − λ · 𝔼_π[c] ) = 𝔼_ν[ φ_λ ]`.

## Where this sits in the DRSB proof

The `≥` half of Wasserstein-DRO strong duality (`GaoKleywegt2023.strong_duality_thm1`'s `hge`,
Blanchet–Murthy Thm 1) has two ingredients:

1. **a measurable near-maximizer of the `c`-transform** — this file's `exists_coupling_lagrangian_ge`,
   built on `ForMathlib.MeasureTheory.exists_measurable_eps_argmax_of_separable`, which sidesteps
   Kuratowski–Ryll-Nardzewski entirely by maximizing over a countable dense set;
2. **an optimal multiplier `λ*` with complementary slackness** (`𝔼_π[c] = δ` at the optimum), which
   is a one-dimensional concave-duality argument and is **not** in this file.

This file supplies ingredient (1).  Ingredient (2) is developed in
`ForMathlib.Analysis.Supergradient` and assembled by the strong-duality modules.

## Hypotheses, and why each is there

`f` continuous and bounded, `c` jointly continuous, `X` second-countable Borel: continuity in `x`
is what lets the supremum be computed on a countable dense set; boundedness of `f` is what makes
`f ∘ g` integrable against the pushforward for an *arbitrary* measurable `g`. `0 < λ` is used to
recover the cost's integrability from `λ · c(g y, y) = f (g y) − u y`.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.MeasureTheory.MeasurableArgmax

set_option autoImplicit false

open MeasureTheory TopologicalSpace ForMathlib.MeasureTheory

namespace ForMathlib.OT

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

/-- **The converse Lagrangian bound.** The Lagrangian value `𝔼_ν[φ_λ]` is achieved, to within any
`ε > 0`, by pushing the nominal `ν` forward along a measurable near-maximizer of the `c`-transform:
there is a coupling `π ∈ Π(μ, ν)` with

`𝔼_ν[φ_λ] − ε ≤ 𝔼_μ[f] − λ · 𝔼_π[c]`.

Paired with `expect_le_dualIntegrand_add_lam_couplingCost` (the `≤` half, which holds for *every*
coupling), this pins the Lagrangian supremum exactly.

The near-maximizer is measurable by `exists_measurable_eps_argmax_of_separable` — no
Kuratowski–Ryll-Nardzewski required, because continuity in `x` lets the supremum be attained to
within `ε` on a countable dense subset. -/
theorem exists_coupling_lagrangian_ge
    (c : X → X → ℝ) (f : X → ℝ) (lam : ℝ) (hlam : 0 < lam) (ν : ProbabilityMeasure X)
    (hfc : Continuous f) (hcc : Continuous fun p : X × X => c p.1 p.2)
    (C : ℝ) (hfb : ∀ x, |f x| ≤ C)
    (hbdd : ∀ y, BddAbove (Set.range fun x => f x - lam * c x y))
    (hφ : Integrable (fun y => ⨆ x, (f x - lam * c x y)) (ν : Measure X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (μ : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X)),
      π ∈ couplings μ ν ∧ Integrable f (μ : Measure X) ∧
      Integrable (fun z : X × X => c z.1 z.2) (π : Measure (X × X)) ∧
      expect ν (fun y => ⨆ x, (f x - lam * c x y)) - ε
        ≤ expect μ f - lam * couplingCost c π := by
  classical
  haveI : IsProbabilityMeasure (ν : Measure X) := ν.2
  have hcy : ∀ y, Continuous fun x => c x y := fun y =>
    hcc.comp (continuous_id.prodMk continuous_const)
  have hcx : ∀ x, Continuous fun y => c x y := fun x =>
    hcc.comp (continuous_const.prodMk continuous_id)
  have hFy : ∀ x, Measurable fun y => f x - lam * c x y := fun x =>
    measurable_const.sub (((hcx x).measurable).const_mul lam)
  have hFx : ∀ y, Continuous fun x => f x - lam * c x y := fun y =>
    hfc.sub (continuous_const.mul (hcy y))
  obtain ⟨g, hg, hgspec⟩ :=
    exists_measurable_eps_argmax_of_separable (fun x y => f x - lam * c x y) hFy hFx hbdd hε
  have hp : Measurable fun y : X => (g y, y) := hg.prodMk measurable_id
  -- the two pushforwards
  have hfg : Integrable (fun y => f (g y)) (ν : Measure X) :=
    Integrable.mono' (integrable_const C) ((hfc.measurable.comp hg).aestronglyMeasurable)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hfb _)
  have humeas : Measurable fun y => f (g y) - lam * c (g y) y :=
    (hfc.measurable.comp hg).sub ((hcc.measurable.comp hp).const_mul lam)
  have hu : Integrable (fun y => f (g y) - lam * c (g y) y) (ν : Measure X) := by
    refine Integrable.mono' (hφ.abs.add (integrable_const ε)) humeas.aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have hle : f (g y) - lam * c (g y) y ≤ ⨆ x, (f x - lam * c x y) := le_ciSup (hbdd y) (g y)
    have hgt : (⨆ x, (f x - lam * c x y)) - ε < f (g y) - lam * c (g y) y := hgspec y
    have habs : (⨆ x, (f x - lam * c x y)) ≤ |⨆ x, (f x - lam * c x y)| := le_abs_self _
    have habs' : -|⨆ x, (f x - lam * c x y)| ≤ ⨆ x, (f x - lam * c x y) := neg_abs_le _
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hε.le]
  have hcg : Integrable (fun y => c (g y) y) (ν : Measure X) := by
    have h := (hfg.sub hu).const_mul lam⁻¹
    refine h.congr (ae_of_all _ fun y => ?_)
    simp only [Pi.sub_apply, sub_sub_cancel]
    rw [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
  set μ : ProbabilityMeasure X :=
    ⟨Measure.map g (ν : Measure X), Measure.isProbabilityMeasure_map hg.aemeasurable⟩ with hμdef
  set π : ProbabilityMeasure (X × X) :=
    ⟨Measure.map (fun y => (g y, y)) (ν : Measure X),
      Measure.isProbabilityMeasure_map hp.aemeasurable⟩ with hπdef
  have hμc : (μ : Measure X) = Measure.map g (ν : Measure X) := rfl
  have hπc : (π : Measure (X × X)) = Measure.map (fun y => (g y, y)) (ν : Measure X) := rfl
  have haef : AEStronglyMeasurable f (Measure.map g (ν : Measure X)) :=
    hfc.measurable.aestronglyMeasurable
  have haec : AEStronglyMeasurable (fun z : X × X => c z.1 z.2)
      (Measure.map (fun y => (g y, y)) (ν : Measure X)) := hcc.measurable.aestronglyMeasurable
  refine ⟨μ, π, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · show Measure.map Prod.fst (Measure.map (fun y => (g y, y)) (ν : Measure X))
        = Measure.map g (ν : Measure X)
    rw [Measure.map_map measurable_fst hp]; rfl
  · show Measure.map Prod.snd (Measure.map (fun y => (g y, y)) (ν : Measure X)) = (ν : Measure X)
    rw [Measure.map_map measurable_snd hp]; simp [Function.comp_def]
  · rw [hμc]; exact (integrable_map_measure haef hg.aemeasurable).mpr hfg
  · rw [hπc]; exact (integrable_map_measure haec hp.aemeasurable).mpr hcg
  · -- the value identity, then `integral_mono` on the pointwise `φ − ε ≤ u`
    have hEf : expect μ f = ∫ y, f (g y) ∂(ν : Measure X) := by
      rw [expect, hμc, integral_map hg.aemeasurable haef]
    have hEc : couplingCost c π = ∫ y, c (g y) y ∂(ν : Measure X) := by
      rw [couplingCost, hπc, integral_map hp.aemeasurable haec]
    have hpt : ∀ y, (⨆ x, (f x - lam * c x y)) - ε ≤ f (g y) - lam * c (g y) y :=
      fun y => (hgspec y).le
    have hmono : ∫ y, ((⨆ x, (f x - lam * c x y)) - ε) ∂(ν : Measure X)
        ≤ ∫ y, (f (g y) - lam * c (g y) y) ∂(ν : Measure X) :=
      integral_mono (hφ.sub (integrable_const ε)) hu hpt
    have hlhs : ∫ y, ((⨆ x, (f x - lam * c x y)) - ε) ∂(ν : Measure X)
        = expect ν (fun y => ⨆ x, (f x - lam * c x y)) - ε := by
      rw [integral_sub hφ (integrable_const ε)]
      simp [expect]
    have hrhs : ∫ y, (f (g y) - lam * c (g y) y) ∂(ν : Measure X)
        = (∫ y, f (g y) ∂(ν : Measure X)) - lam * ∫ y, c (g y) y ∂(ν : Measure X) := by
      rw [integral_sub hfg (hcg.const_mul lam), integral_const_mul]
    rw [hEf, hEc]
    rw [hlhs, hrhs] at hmono
    exact hmono

end ForMathlib.OT
