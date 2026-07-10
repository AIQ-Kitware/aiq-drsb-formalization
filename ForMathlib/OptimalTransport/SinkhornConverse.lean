/-
# The Sinkhorn converse Lagrangian bound (Mathlib-staging)

The `≥` half of **entropic/Sinkhorn DRO strong duality** (Wang–Gao–Xie): for every multiplier
`λ > 0` there is a coupling `γ ∈ Π(μ̂, μ)` whose Lagrangian *equals* the dual's inner value,

`𝔼_μ[f] − λ·(𝔼_γ[c] + κ·KL(γ ‖ μ̂⊗ν))  =  𝔼_μ̂[ λκ·log ∫ exp((f − λ c(x,·))/(λκ)) dν ]`.

Unlike the Wasserstein converse bound (`ForMathlib.OT.exists_coupling_lagrangian_ge`), which is
`ε`-approximate because the Donsker–Varadhan supremum *over functions* is not attained, this one is
an **equality**: the Gibbs supremum *over measures* is attained, at the tilted measure. The witness
is therefore explicit — no measurable selection, no `ε`.

The coupling is `γ = μ̂ ⊗ₘ P` for the tilted kernel `P x = ν.tilted ((f − λ c(x,·))/(λκ))`
(`ForMathlib.MeasureTheory.tiltedKernel`). The pointwise identity
(`entropic_gibbs_attained_tilted`) is then integrated against `μ̂`, the transport and entropic terms
disintegrating by `Measure.integral_compProd` and the KL chain rule respectively.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.MeasureTheory.TiltedKernel
import ForMathlib.MeasureTheory.DonskerVaradhan
import ForMathlib.MeasureTheory.KLChainRule

set_option autoImplicit false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ForMathlib.OT

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Measure-level `Integrable.integral_compProd`.** Mathlib has this for kernel composition
(`MeasureTheory.Integrable.integral_compProd`) but not for `μ ⊗ₘ κ`. -/
theorem integrable_integral_compProd {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsSFiniteKernel κ] {g : α × β → ℝ} (hg : Integrable g (μ ⊗ₘ κ)) :
    Integrable (fun x => ∫ y, g (x, y) ∂(κ x)) μ := by
  rw [Measure.compProd] at hg
  simpa using hg.integral_compProd (a := ())

variable {X : Type*} [MeasurableSpace X]

/-- **The Sinkhorn converse Lagrangian bound**, as an *equality*.

For every `λ, κ > 0` there is a coupling `γ ∈ Π(μ̂, μ)` — explicitly `γ = μ̂ ⊗ₘ P` with `P` the
tilted (Gibbs) kernel `P x = ν.tilted ((f − λ c(x,·))/(λκ))` — with

`𝔼_μ[f] − λ·(𝔼_γ[c] + κ·KL(γ‖μ̂⊗ν)) = 𝔼_μ̂[λκ·log ∫ exp((f − λ c(x,·))/(λκ)) dν]`,

the right side being the Wang–Gao–Xie dual's inner (log-partition) term.

This is the entropic analogue of `ForMathlib.OT.exists_coupling_lagrangian_ge`, and it is *sharp*:
where the Wasserstein bound loses an `ε` (its Donsker–Varadhan supremum, taken over *functions*, is
not attained), the entropic one is an equality, because the Gibbs supremum over *measures* **is**
attained — at the tilted measure. Hence no measurable ε-argmax selection is needed here.

The hypotheses are the slice and aggregate integrability conditions of any disintegration argument:
`hexp` normalizes the tilt, `hf_P`/`hc_P` make the per-`x` Gibbs identity meaningful, `hf_norm` and
`hc_norm` are exactly what `Measure.integrable_compProd_iff` asks to assemble the slices into `γ`,
and `hkl` makes the entropic term finite (so `klDiv γ (μ̂⊗ν) ≠ ⊤` — reported in the conclusion,
since `klReal`'s `toReal` would otherwise silently return the junk value `0`). -/
theorem exists_coupling_sinkhorn_lagrangian_eq
    [MeasurableSpace.CountableOrCountablyGenerated X X]
    (μhat ν : ProbabilityMeasure X) (c : X → X → ℝ) (f : X → ℝ) (κ lam : ℝ)
    (hκ : 0 < κ) (hlam : 0 < lam)
    (hfm : Measurable f) (hcm : Measurable fun z : X × X => c z.1 z.2)
    (hexp : ∀ x, Integrable (fun y => Real.exp ((f y - lam * c x y) / (lam * κ))) (ν : Measure X))
    (hf_P : ∀ x, Integrable f ((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ)))
    (hc_P : ∀ x, Integrable (fun y => c x y)
      ((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ)))
    (hf_norm : Integrable (fun x => ∫ y, ‖f y‖
      ∂((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ))) (μhat : Measure X))
    (hc_norm : Integrable (fun x => ∫ y, ‖c x y‖
      ∂((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ))) (μhat : Measure X))
    (hkl : Integrable (fun x => klReal
      ((ν : Measure X).tilted fun y => (f y - lam * c x y) / (lam * κ)) (ν : Measure X))
      (μhat : Measure X)) :
    ∃ (μ : ProbabilityMeasure X) (γ : ProbabilityMeasure (X × X)),
      γ ∈ couplings μhat μ ∧ Integrable f (μ : Measure X) ∧
      Integrable (fun z : X × X => c z.1 z.2) (γ : Measure (X × X)) ∧
      klDiv (γ : Measure (X × X)) (prodMeasure μhat ν) ≠ ⊤ ∧
      expect μ f - lam * sinkhornObjective c κ μhat ν γ
        = expect μhat (fun x => lam * κ *
            Real.log (∫ y, Real.exp ((f y - lam * c x y) / (lam * κ)) ∂(ν : Measure X))) := by
  classical
  haveI : IsProbabilityMeasure (μhat : Measure X) := μhat.2
  haveI : IsProbabilityMeasure (ν : Measure X) := ν.2
  set A : X → X → ℝ := fun x y => (f y - lam * c x y) / (lam * κ) with hAdef
  have hA : Measurable (Function.uncurry A) :=
    (((hfm.comp measurable_snd).sub (measurable_const.mul hcm)).div_const _)
  have hfsnd : Measurable fun z : X × X => f z.2 := hfm.comp measurable_snd
  set P : Kernel X X := ForMathlib.MeasureTheory.tiltedKernel (ν : Measure X) A with hPdef
  have hPapp : ∀ x, P x = (ν : Measure X).tilted (A x) := fun x => by
    rw [hPdef]; exact ForMathlib.MeasureTheory.tiltedKernel_apply _ A hA x
  haveI hMk : IsMarkovKernel P := by
    rw [hPdef]; exact ForMathlib.MeasureTheory.isMarkovKernel_tiltedKernel _ A hA hexp
  -- the tilted slices integrate `A`, hence have finite KL against `ν`
  have hA_P : ∀ x, Integrable (A x) (P x) := fun x => by
    rw [hPapp]; exact ((hf_P x).sub ((hc_P x).const_mul lam)).div_const _
  have hkltop : ∀ x, klDiv (P x) (ν : Measure X) ≠ ⊤ := fun x => by
    rw [hPapp]
    exact ForMathlib.MeasureTheory.klDiv_tilted_ne_top (hexp x) (by rw [← hPapp]; exact hA_P x)
  have hkl' : Integrable (fun x => klReal (P x) (ν : Measure X)) (μhat : Measure X) := by
    simpa only [hPapp] using hkl
  -- the coupling `γ = μ̂ ⊗ₘ P` and its second marginal `μ`
  set γm : Measure (X × X) := (μhat : Measure X) ⊗ₘ P with hγm
  haveI : IsProbabilityMeasure γm := by rw [hγm]; infer_instance
  have hcost_γ : Integrable (fun z : X × X => c z.1 z.2) γm := by
    rw [hγm]
    refine (Measure.integrable_compProd_iff hcm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · exact ae_of_all _ fun x => by rw [hPapp]; exact hc_P x
    · simpa only [hPapp] using hc_norm
  have hfsnd_γ : Integrable (fun z : X × X => f z.2) γm := by
    rw [hγm]
    refine (Measure.integrable_compProd_iff hfsnd.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · exact ae_of_all _ fun x => by rw [hPapp]; exact hf_P x
    · simpa only [hPapp] using hf_norm
  set μm : Measure X := γm.map Prod.snd with hμm
  haveI : IsProbabilityMeasure μm := by
    rw [hμm]; exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hfμ : Integrable f μm := by
    rw [hμm, integrable_map_measure hfm.aestronglyMeasurable measurable_snd.aemeasurable]
    exact hfsnd_γ
  -- the entropic term disintegrates by the KL chain rule
  have hprod : prodMeasure μhat ν = (μhat : Measure X) ⊗ₘ Kernel.const X (ν : Measure X) :=
    Measure.compProd_const.symm
  have hac : (μhat : Measure X) ⊗ₘ P ≪ (μhat : Measure X) ⊗ₘ Kernel.const X (ν : Measure X) := by
    refine Measure.absolutelyContinuous_compProd_right_iff.mpr (ae_of_all _ fun x => ?_)
    rw [hPapp, Kernel.const_apply]
    exact tilted_absolutelyContinuous _ _
  have h_fin : klDiv ((μhat : Measure X) ⊗ₘ P)
      ((μhat : Measure X) ⊗ₘ Kernel.const X (ν : Measure X)) ≠ ⊤ := by
    rw [ForMathlib.MeasureTheory.klDiv_compProd_eq_lintegral _ _ _ hac]
    have heq : ∀ x, klDiv (P x) (Kernel.const X (ν : Measure X) x)
        = ENNReal.ofReal (klReal (P x) (ν : Measure X)) := fun x => by
      rw [Kernel.const_apply, klReal, ENNReal.ofReal_toReal (hkltop x)]
    simp only [heq]
    exact hkl'.lintegral_lt_top.ne
  have hklγ : klReal γm (prodMeasure μhat ν)
      = ∫ x, klReal (P x) (ν : Measure X) ∂(μhat : Measure X) := by
    rw [klReal, hprod, hγm,
      ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_integral _ _ _ hac h_fin]
    simp only [Kernel.const_apply, klReal]
  -- the transport and objective terms disintegrate by `Measure.integral_compProd`
  have hFagg : Integrable (fun x => ∫ y, f y ∂(P x)) (μhat : Measure X) := by
    have := integrable_integral_compProd (μ := (μhat : Measure X)) (κ := P)
      (g := fun z : X × X => f z.2) (by rw [← hγm]; exact hfsnd_γ)
    simpa using this
  have hCagg : Integrable (fun x => ∫ y, c x y ∂(P x)) (μhat : Measure X) := by
    have := integrable_integral_compProd (μ := (μhat : Measure X)) (κ := P)
      (g := fun z : X × X => c z.1 z.2) (by rw [← hγm]; exact hcost_γ)
    simpa using this
  have hexpμ : ∫ y, f y ∂μm = ∫ x, ∫ y, f y ∂(P x) ∂(μhat : Measure X) := by
    rw [hμm, integral_map measurable_snd.aemeasurable hfm.aestronglyMeasurable, hγm]
    exact Measure.integral_compProd (by rw [← hγm]; exact hfsnd_γ)
  have hccost : ∫ z, c z.1 z.2 ∂γm = ∫ x, ∫ y, c x y ∂(P x) ∂(μhat : Measure X) := by
    rw [hγm]; exact Measure.integral_compProd (by rw [← hγm]; exact hcost_γ)
  -- the pointwise Gibbs attainment identity
  have hpt : ∀ x, lam * κ * Real.log (∫ y, Real.exp (A x y) ∂(ν : Measure X))
      = (∫ y, f y ∂(P x)) - lam * ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure X)) := by
    intro x
    rw [hPapp, klReal]
    exact ForMathlib.MeasureTheory.entropic_gibbs_attained_tilted hκ hlam (hexp x) (hf_P x) (hc_P x)
  refine ⟨⟨μm, ‹_›⟩, ⟨γm, ‹_›⟩, ⟨?_, rfl⟩, hfμ, hcost_γ, ?_, ?_⟩
  · show Measure.map Prod.fst γm = (μhat : Measure X)
    rw [hγm]; exact Measure.fst_compProd _ P
  · show klDiv γm (prodMeasure μhat ν) ≠ ⊤
    rw [hprod, hγm]; exact h_fin
  · show (∫ y, f y ∂μm) - lam * ((∫ z, c z.1 z.2 ∂γm) + κ * klReal γm (prodMeasure μhat ν))
      = ∫ x, lam * κ * Real.log (∫ y, Real.exp (A x y) ∂(ν : Measure X)) ∂(μhat : Measure X)
    -- ascribe the lambdas: `Integrable.add` states `Integrable (f + g)`, and the unapplied
    -- `Pi.add` blocks `rw [integral_sub]` from matching (AGENTS.md §6).
    have hkl2 : Integrable (fun x => κ * klReal (P x) (ν : Measure X)) (μhat : Measure X) :=
      hkl'.const_mul κ
    have hG : Integrable
        (fun x => lam * ((∫ y, c x y ∂(P x)) + κ * klReal (P x) (ν : Measure X)))
        (μhat : Measure X) := (hCagg.add hkl2).const_mul lam
    rw [hexpμ, hccost, hklγ, integral_congr_ae (ae_of_all _ hpt),
      integral_sub hFagg hG, integral_const_mul, integral_add hCagg hkl2, integral_const_mul]

end ForMathlib.OT