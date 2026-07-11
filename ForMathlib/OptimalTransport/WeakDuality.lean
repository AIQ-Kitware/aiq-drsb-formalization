/-
# OT-DRO weak duality: the per-coupling Lagrangian bound (Mathlib-staging)

The **always-true `≤` (weak-duality) half** of optimal-transport DRO duality — the
Lagrangian bound that, taken to the `inf` over the multiplier and the `sup` over the
ambiguity ball, gives `v_P ≤ v_D`. This is the reusable kernel behind
`GaoKleywegt2023.weak_duality_prop1` / `BlanchetMurthy2019.wdro_strong_duality` (`≤`
direction) and hence behind the DRSB card cost bounds (`Drsb.wdrsb_cost_bound`,
`Drsb.sdrsb_cost_bound`) — see `PROOF_PIPELINE.md` §0: the cards need ONLY this half,
never the research-grade `≥` (attainment) direction.

The results are stated at Kantorovich generality: two measurable spaces `α`, `β`, a cost
`c : α → β → ℝ`, and **no algebraic or topological structure on either** — nothing in these bounds
refers to a norm, to subtraction, or to `α = β`. The DRSB quadratic cost is one instantiation.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.MeasureTheory.DonskerVaradhan

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ForMathlib.OT

namespace ForMathlib.OT

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Optimal transport cost is bounded by any coupling's cost.** For a nonnegative cost
`c` and any coupling `π ∈ Π(μ, ν)`, `otCost c μ ν ≤ couplingCost c π`. Immediate from
`csInf_le` (the value set is bounded below by `0`, since `couplingCost = ∫ c dπ ≥ 0`).

The always-usable "upper bound by an explicit transport plan" direction of Kantorovich —
the reusable tool for showing a *constructed* measure lies in a Wasserstein ball
(`otCost ≤ (explicit coupling cost) ≤ radius`), needed by every worst-case-measure
construction (Gao–Kleywegt Cor 2(ii), Esfahani–Kuhn Thm 4.4 / Cor 4.6). -/
theorem otCost_le_couplingCost (c : α → β → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) (π : ProbabilityMeasure (α × β))
    (hπ : π ∈ couplings μ ν) :
    otCost c μ ν ≤ couplingCost c π := by
  refine csInf_le ⟨0, ?_⟩ ⟨π, hπ, rfl⟩
  rintro r ⟨π', _, rfl⟩
  exact integral_nonneg (fun z => hc z.1 z.2)

/-- **Per-coupling Lagrangian bound** (the always-true `≤` half of OT-DRO duality).
For any coupling `π ∈ Π(μ, ν)` of a source `μ` with the nominal `ν`, any cost `c`, and
any multiplier `λ` (the `λ ≥ 0` gate matters only for the downstream assembly, not this
bound),
`𝔼_μ[f] ≤ 𝔼_{y∼ν}[ sup_x (f x − λ c(x, y)) ] + λ · 𝔼_π[c]`.

Pointwise `f(x) ≤ φ_λ(y) + λ c(x, y)` with `φ_λ(y) = sup_x (f x − λ c x y)`; integrate
over `π` and use the marginals. Taking `inf_π 𝔼_π[c] = otCost c μ ν ≤ δ` and then
`sup_μ`, `inf_λ` yields `droValue (ball) f ≤ dualValue`. The `sup` boundedness `hbdd`
and the three integrability hypotheses make each expectation well defined.

Ported from the complete proof in `reference/V4.lean` (`wdro_lagrangian_bound`), generalized from
the DRSB quadratic cost `‖x − y‖²` to an arbitrary `c : α → β → ℝ` between two measurable spaces. -/
theorem expect_le_dualIntegrand_add_lam_couplingCost
    (c : α → β → ℝ) (f : α → ℝ) (lam : ℝ) (_hlam : 0 ≤ lam)
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) (π : ProbabilityMeasure (α × β))
    (hπ : π ∈ couplings μ ν)
    (hbdd : ∀ y : β, BddAbove (Set.range (fun x => f x - lam * c x y)))
    (hf : Integrable f (μ : Measure α))
    (hφ : Integrable (fun y => sSup (Set.range (fun x => f x - lam * c x y))) (ν : Measure β))
    (hcost : Integrable (fun z : α × β => c z.1 z.2) (π : Measure (α × β))) :
    expect μ f
      ≤ expect ν (fun y => sSup (Set.range (fun x => f x - lam * c x y)))
        + lam * couplingCost c π := by
  classical
  set g : β → ℝ := fun y => sSup (Set.range (fun x => f x - lam * c x y)) with hgdef
  -- marginal identities: μ = fst_# π, ν = snd_# π
  have hfst : (μ : Measure α) = Measure.map Prod.fst (π : Measure (α × β)) := hπ.1.symm
  have hsnd : (ν : Measure β) = Measure.map Prod.snd (π : Measure (α × β)) := hπ.2.symm
  have hfae : AEStronglyMeasurable f (Measure.map Prod.fst (π : Measure (α × β))) :=
    hfst ▸ hf.1
  have hgae : AEStronglyMeasurable g (Measure.map Prod.snd (π : Measure (α × β))) :=
    hsnd ▸ hφ.1
  -- rewrite both expectations as integrals against π via its marginals
  have e1 : expect μ f = ∫ z, f z.1 ∂(π : Measure (α × β)) := by
    rw [expect, hfst, integral_map measurable_fst.aemeasurable hfae]
  have e2 : expect ν g = ∫ z, g z.2 ∂(π : Measure (α × β)) := by
    rw [expect, hsnd, integral_map measurable_snd.aemeasurable hgae]
  -- transport the integrability hypotheses onto π
  have hfpi : Integrable (fun z : α × β => f z.1) (π : Measure (α × β)) :=
    (integrable_map_measure hfae measurable_fst.aemeasurable).mp (hfst ▸ hf)
  have hgpi : Integrable (fun z : α × β => g z.2) (π : Measure (α × β)) :=
    (integrable_map_measure hgae measurable_snd.aemeasurable).mp (hsnd ▸ hφ)
  -- pointwise: f(x) ≤ φ_λ(y) + λ c(x, y), from x being in the sup's range
  have hpt : ∀ z : α × β, f z.1 ≤ g z.2 + lam * c z.1 z.2 := by
    intro z
    have hmem : f z.1 - lam * c z.1 z.2
        ∈ Set.range (fun x => f x - lam * c x z.2) := ⟨z.1, rfl⟩
    have := le_csSup (hbdd z.2) hmem
    simp only [hgdef]; linarith
  rw [e1, e2, show couplingCost c π = ∫ z, c z.1 z.2 ∂(π : Measure (α × β)) from rfl]
  calc ∫ z, f z.1 ∂(π : Measure (α × β))
      ≤ ∫ z, (g z.2 + lam * c z.1 z.2) ∂(π : Measure (α × β)) :=
        integral_mono hfpi (hgpi.add (hcost.const_mul lam)) hpt
    _ = (∫ z, g z.2 ∂(π : Measure (α × β)))
          + lam * ∫ z, c z.1 z.2 ∂(π : Measure (α × β)) := by
        rw [integral_add hgpi (hcost.const_mul lam), integral_const_mul]

/-- **Ξ-restricted per-coupling Lagrangian bound.** The `Set.image`-over-`Ξ` variant of
`expect_le_dualIntegrand_add_lam_couplingCost`: when the source `μ` is supported on `Ξ`
(`hμΞ`, i.e. `μ ∈ P(Ξ)`), the conjugate `sup` restricts from all of `α` to `Ξ`,
`𝔼_μ[f] ≤ 𝔼_{y∼ν}[ sup_{x∈Ξ} (f x − λ c(x, y)) ] + λ · 𝔼_π[c]`.

The proof is identical to the unrestricted kernel except the pointwise bound
`f(x) ≤ φ_λ^Ξ(y) + λ c(x, y)` needs `x ∈ Ξ` (so that `f x − λ c x y ∈ (·) '' Ξ`), which
holds `π`-a.e. because the first marginal `μ` is `Ξ`-supported — hence `integral_mono_ae`
(the a.e. monotonicity) in place of `integral_mono`. This is the kernel behind the
data-driven **P(Ξ)-restricted** worst-case duality
(`MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual`, Thm 4.2), whose dual `sup` is over
the uncertainty set `Ξ`. `MeasurableSet Ξ` (`hΞ`) is used only to push the a.e.-in-`Ξ`
property through the `Prod.fst` marginal via `ae_map_iff`. -/
theorem expect_le_dualIntegrand_add_lam_couplingCost_restrict
    (c : α → β → ℝ) (f : α → ℝ) (lam : ℝ) (_hlam : 0 ≤ lam)
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) (Ξ : Set α) (hΞ : MeasurableSet Ξ)
    (π : ProbabilityMeasure (α × β)) (hπ : π ∈ couplings μ ν)
    (hμΞ : ∀ᵐ x ∂(μ : Measure α), x ∈ Ξ)
    (hbdd : ∀ y : β, BddAbove ((fun x => f x - lam * c x y) '' Ξ))
    (hf : Integrable f (μ : Measure α))
    (hφ : Integrable (fun y => sSup ((fun x => f x - lam * c x y) '' Ξ)) (ν : Measure β))
    (hcost : Integrable (fun z : α × β => c z.1 z.2) (π : Measure (α × β))) :
    expect μ f
      ≤ expect ν (fun y => sSup ((fun x => f x - lam * c x y) '' Ξ))
        + lam * couplingCost c π := by
  classical
  set g : β → ℝ := fun y => sSup ((fun x => f x - lam * c x y) '' Ξ) with hgdef
  have hfst : (μ : Measure α) = Measure.map Prod.fst (π : Measure (α × β)) := hπ.1.symm
  have hsnd : (ν : Measure β) = Measure.map Prod.snd (π : Measure (α × β)) := hπ.2.symm
  have hfae : AEStronglyMeasurable f (Measure.map Prod.fst (π : Measure (α × β))) :=
    hfst ▸ hf.1
  have hgae : AEStronglyMeasurable g (Measure.map Prod.snd (π : Measure (α × β))) :=
    hsnd ▸ hφ.1
  have e1 : expect μ f = ∫ z, f z.1 ∂(π : Measure (α × β)) := by
    rw [expect, hfst, integral_map measurable_fst.aemeasurable hfae]
  have e2 : expect ν g = ∫ z, g z.2 ∂(π : Measure (α × β)) := by
    rw [expect, hsnd, integral_map measurable_snd.aemeasurable hgae]
  have hfpi : Integrable (fun z : α × β => f z.1) (π : Measure (α × β)) :=
    (integrable_map_measure hfae measurable_fst.aemeasurable).mp (hfst ▸ hf)
  have hgpi : Integrable (fun z : α × β => g z.2) (π : Measure (α × β)) :=
    (integrable_map_measure hgae measurable_snd.aemeasurable).mp (hsnd ▸ hφ)
  -- π-a.e. the first coordinate lies in Ξ (the source μ is Ξ-supported)
  have hπΞ : ∀ᵐ z ∂(π : Measure (α × β)), z.1 ∈ Ξ :=
    (ae_map_iff measurable_fst.aemeasurable hΞ).mp (hfst ▸ hμΞ)
  -- pointwise (π-a.e.): f(x) ≤ φ_λ^Ξ(y) + λ c(x, y), from x ∈ Ξ being in the image's domain
  have hpt : ∀ᵐ z ∂(π : Measure (α × β)), f z.1 ≤ g z.2 + lam * c z.1 z.2 := by
    filter_upwards [hπΞ] with z hz
    have hmem : f z.1 - lam * c z.1 z.2
        ∈ (fun x => f x - lam * c x z.2) '' Ξ := ⟨z.1, hz, rfl⟩
    have := le_csSup (hbdd z.2) hmem
    simp only [hgdef]; linarith
  rw [e1, e2, show couplingCost c π = ∫ z, c z.1 z.2 ∂(π : Measure (α × β)) from rfl]
  calc ∫ z, f z.1 ∂(π : Measure (α × β))
      ≤ ∫ z, (g z.2 + lam * c z.1 z.2) ∂(π : Measure (α × β)) :=
        integral_mono_ae hfpi (hgpi.add (hcost.const_mul lam)) hpt
    _ = (∫ z, g z.2 ∂(π : Measure (α × β)))
          + lam * ∫ z, c z.1 z.2 ∂(π : Measure (α × β)) := by
        rw [integral_add hgpi (hcost.const_mul lam), integral_const_mul]

/-! ## The entropic (Sinkhorn) analogue -/

/-- **Sinkhorn per-conditional-family weak-duality kernel** (the entropic analogue of
`expect_le_dualIntegrand_add_lam_couplingCost`). For a family of conditionals
`P : X → Measure X` (each `≪` the reference `ν`), the nominal `p₀`, and `λ, κ > 0`,
`∫_{x∼p₀} 𝔼_{P_x}[f] ≤ λ·∫_{x∼p₀}(𝔼_{P_x}[c(x,·)] + κ·KL(P_x‖ν)) + 𝔼_{x∼p₀}[v_x(λ)]`,
where `v_x(λ) = λκ·log ∫_ν e^{(f−λc(x,·))/(λκ)}` is the log-partition (soft-max) term.

Proof: the proved Gibbs/Donsker–Varadhan inequality
(`ForMathlib.MeasureTheory.integral_le_klDiv_add_log_integral_exp`) applied to
`A_x = (f − λ c(x,·))/(λκ)` per nominal point `x`, then integrated over `p₀`. Mathlib has
the Gibbs variational principle and kernel integration.  This is the `≤` half behind `WangGaoXie2023.strong_duality` / `Drsb.sdrsb_cost_bound`
(once composed with a disintegration of the ball-witnessing coupling `γ = p₀ ⊗ₘ P`). -/
theorem expect_kernel_le_lam_sinkhornBudget_add_logPartition
    (p₀ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) (c : α → β → ℝ) (f : β → ℝ) (κ lam : ℝ)
    (_hκ : 0 < κ) (hlam : 0 < lam)
    (P : α → Measure β) (hP : ∀ x, IsProbabilityMeasure (P x))
    (hac : ∀ x, P x ≪ (ν : Measure β))
    (hf_P : ∀ x, Integrable f (P x))
    (hc_P : ∀ x, Integrable (fun y => c x y) (P x))
    (h_llr : ∀ x, Integrable (MeasureTheory.llr (P x) (ν : Measure β)) (P x))
    (h_exp : ∀ x, Integrable
        (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure β))
    (hI_f : Integrable (fun x => ∫ y, f y ∂(P x)) (p₀ : Measure α))
    (hI_c : Integrable (fun x => ∫ y, c x y ∂(P x)) (p₀ : Measure α))
    (hI_kl : Integrable (fun x => klReal (P x) (ν : Measure β)) (p₀ : Measure α))
    (hI_lp : Integrable (fun x => lam * κ *
        Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure β)))
        (p₀ : Measure α)) :
    (∫ x, (∫ y, f y ∂(P x)) ∂(p₀ : Measure α))
      ≤ lam * (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure β)) ∂(p₀ : Measure α))
        + ∫ x, (lam * κ *
            Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure β)))
          ∂(p₀ : Measure α) := by
  have hlamκ : (0 : ℝ) < lam * κ := mul_pos hlam _hκ
  have hne : lam * κ ≠ 0 := ne_of_gt hlamκ
  have hpt : ∀ x, (∫ y, f y ∂(P x))
      ≤ lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure β)
        + lam * κ * Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure β)) := by
    intro x
    haveI := hP x
    have hsub : Integrable (fun y => f y - lam * c x y) (P x) :=
      (hf_P x).sub ((hc_P x).const_mul lam)
    have hA_int : Integrable (fun y => (f y - lam * c x y) / (lam * κ)) (P x) :=
      hsub.div_const _
    have hDV := ForMathlib.MeasureTheory.integral_le_klDiv_add_log_integral_exp
      (hac x) hA_int (h_llr x) (h_exp x)
    have hAeq : (∫ y, (f y - lam * c x y) / (lam * κ) ∂(P x))
        = (lam * κ)⁻¹ * ((∫ y, f y ∂(P x)) - lam * ∫ y, c x y ∂(P x)) := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_sub (hf_P x) ((hc_P x).const_mul lam),
        integral_const_mul]
      ring
    rw [hAeq] at hDV
    have hmul := mul_le_mul_of_nonneg_left hDV (le_of_lt hlamκ)
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_add] at hmul
    have hkl : (InformationTheory.klDiv (P x) (ν : Measure β)).toReal
        = klReal (P x) (ν : Measure β) := rfl
    rw [hkl] at hmul
    linarith [hmul]
  have hRHS_int : Integrable
      (fun x => lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure β)
        + lam * κ * Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure β)))
      (p₀ : Measure α) :=
    ((hI_c.const_mul lam).add (hI_kl.const_mul (lam * κ))).add hI_lp
  calc (∫ x, (∫ y, f y ∂(P x)) ∂(p₀ : Measure α))
      ≤ ∫ x, (lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure β)
          + lam * κ * Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure β)))
          ∂(p₀ : Measure α) := integral_mono hI_f hRHS_int hpt
    _ = lam * (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure β)) ∂(p₀ : Measure α))
          + ∫ x, (lam * κ *
              Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure β)))
            ∂(p₀ : Measure α) := by
        have hAB : Integrable (fun x => lam * (∫ y, c x y ∂(P x))
            + lam * κ * klReal (P x) (ν : Measure β)) (p₀ : Measure α) :=
          (hI_c.const_mul lam).add (hI_kl.const_mul (lam * κ))
        have e1 : (∫ x, (lam * (∫ y, c x y ∂(P x)) + lam * κ * klReal (P x) (ν : Measure β)
              + lam * κ * Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure β)))
              ∂(p₀ : Measure α))
            = lam * (∫ x, (∫ y, c x y ∂(P x)) ∂(p₀ : Measure α))
              + lam * κ * (∫ x, klReal (P x) (ν : Measure β) ∂(p₀ : Measure α))
              + ∫ x, (lam * κ * Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure β)))
                  ∂(p₀ : Measure α) := by
          rw [integral_add hAB hI_lp,
            integral_add (hI_c.const_mul lam) (hI_kl.const_mul (lam * κ)),
            integral_const_mul, integral_const_mul]
        have e2 : (∫ x, ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure β)) ∂(p₀ : Measure α))
            = (∫ x, (∫ y, c x y ∂(P x)) ∂(p₀ : Measure α))
              + κ * (∫ x, klReal (P x) (ν : Measure β) ∂(p₀ : Measure α)) := by
          rw [integral_add hI_c (hI_kl.const_mul κ), integral_const_mul]
        rw [e1, e2]; ring

end ForMathlib.OT
