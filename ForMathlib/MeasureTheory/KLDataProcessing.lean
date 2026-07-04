/-
# Data-processing inequality for the Kullback–Leibler divergence (Mathlib-staging)

For probability measures `μ ≪ ν` with finite `KL(μ‖ν)` and any measurable `g`,
`KL(g_# μ ‖ g_# ν) ≤ KL(μ‖ν)`: coarse-graining (pushing forward by a measurable map) can
only *decrease* relative entropy. This is the **data-processing inequality** for KL — a
cornerstone of information theory that is a genuine gap in Mathlib (which has the KL chain
rule `klDiv_compProd_eq_add` and a conditional Jensen inequality, but no DPI / f-divergence
monotonicity).

STATUS: PROVED, axiom-clean (`propext / Classical.choice / Quot.sound`).

Proof (the textbook convex/Jensen argument, assembled from existing Mathlib pieces):
the Radon–Nikodym derivative of a pushforward is a conditional expectation
(`toReal_rnDeriv_map`: `d(g_#μ)/d(g_#ν) ∘ g =ᵐ[ν] ν[dμ/dν | σ(g)]`), so writing `KL` as the
`ν`-integral of the convex generator `klFun ∘ (dμ/dν)` (`toReal_klDiv_eq_integral_klFun`) and
pulling the pushforward-KL back through `g` (`integral_map`), the two sides differ by a single
application of **conditional Jensen** (`ConvexOn.map_condExp_le` with `convexOn_klFun` on
`Ici 0`) followed by the tower property (`integral_condExp`). Finiteness of `KL(μ‖ν)` gives the
integrability of `klFun ∘ (dμ/dν)` that the conditional-expectation steps need.

Consumed by `ChenGeorgiouPavon2021.dynamic_eq_static_SB` (the `staticSB ≤ dynamicSB` direction:
the endpoint projection `ω ↦ (ω₀,ω₁)` sends a feasible path law to a coupling whose KL against
the reference endpoint law is `≤` the path-measure KL). Upstreamable as-is.
-/
import Mathlib

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace ForMathlib.MeasureTheory

variable {𝓧 𝓨 : Type*} [m𝓧 : MeasurableSpace 𝓧] [m𝓨 : MeasurableSpace 𝓨]

/-- **Data-processing inequality for KL divergence** (real / `toReal` form). For probability
measures `μ ≪ ν` on `𝓧` with finite `KL(μ‖ν)`, and any measurable `g : 𝓧 → 𝓨`,
`KL(g_# μ ‖ g_# ν) ≤ KL(μ‖ν)`. -/
theorem toReal_klDiv_map_le
    (μ ν : Measure 𝓧) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (g : 𝓧 → 𝓨) (hg : Measurable g) (hfin : klDiv μ ν ≠ ⊤) :
    (klDiv (μ.map g) (ν.map g)).toReal ≤ (klDiv μ ν).toReal := by
  classical
  haveI : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  haveI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hmapac : μ.map g ≪ ν.map g := hμν.map hg
  have hm : m𝓨.comap g ≤ m𝓧 := hg.comap_le
  haveI : SigmaFinite (ν.trim hm) := by infer_instance
  -- `F₀ = dμ/dν` (as a real function); the KL generator is `klFun ∘ F₀`.
  set F₀ : 𝓧 → ℝ := fun a => (μ.rnDeriv ν a).toReal with hF₀
  have hllr : Integrable (llr μ ν) μ := (klDiv_ne_top_iff.mp hfin).2
  have hF₀int : Integrable F₀ ν := Measure.integrable_toReal_rnDeriv
  have hklF₀int : Integrable (fun a => klFun (F₀ a)) ν :=
    (integrable_klFun_rnDeriv_iff hμν).mpr hllr
  rw [toReal_klDiv_eq_integral_klFun hmapac, toReal_klDiv_eq_integral_klFun hμν]
  -- pull the pushforward-KL integral back through `g`
  have hLHSmap : (∫ y, klFun ((μ.map g).rnDeriv (ν.map g) y).toReal ∂(ν.map g))
      = ∫ x, klFun ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ∂ν := by
    rw [integral_map hg.aemeasurable]
    exact Measurable.aestronglyMeasurable (by fun_prop)
  rw [hLHSmap]
  -- the pushforward RN-derivative is the conditional expectation of `F₀`
  have hstep1 : (∫ x, klFun ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ∂ν)
      = ∫ x, klFun ((ν[F₀ | m𝓨.comap g]) x) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [toReal_rnDeriv_map (μ := μ) (ν := ν) hμν hg] with x hx
    rw [hx]
  rw [hstep1]
  -- conditional Jensen for the convex generator `klFun` on `[0,∞)`
  have hjensen : (fun x => klFun ((ν[F₀ | m𝓨.comap g]) x))
      ≤ᵐ[ν] ν[fun a => klFun (F₀ a) | m𝓨.comap g] :=
    ConvexOn.map_condExp_le hm convexOn_klFun
      (continuous_klFun.lowerSemicontinuous.lowerSemicontinuousOn _)
      (ae_of_all _ fun a => ENNReal.toReal_nonneg) isClosed_Ici hF₀int hklF₀int
  have hcondint : Integrable (ν[fun a => klFun (F₀ a) | m𝓨.comap g]) ν := integrable_condExp
  have hLHSint : Integrable (fun x => klFun ((ν[F₀ | m𝓨.comap g]) x)) ν := by
    refine hcondint.mono' ?_ ?_
    · exact continuous_klFun.comp_aestronglyMeasurable
        (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
    · filter_upwards [hjensen,
        condExp_nonneg (m := m𝓨.comap g) (μ := ν) (f := F₀)
          (ae_of_all _ fun a => ENNReal.toReal_nonneg)] with x hx hnn
      rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg hnn)]
      exact hx
  calc (∫ x, klFun ((ν[F₀ | m𝓨.comap g]) x) ∂ν)
      ≤ ∫ x, (ν[fun a => klFun (F₀ a) | m𝓨.comap g]) x ∂ν :=
        integral_mono_ae hLHSint hcondint hjensen
    _ = ∫ x, klFun (F₀ x) ∂ν := integral_condExp hm

/-- **The path KL dominates the limit of its finite-dimensional-projection KLs (the `≥` half).**
If a family of measurable maps `gᵢ : 𝓧 → 𝓨 i` (e.g. finite-dimensional coordinate projections of a
path space) push `μ, ν` to images whose KL divergences converge to `L` along a nontrivial filter,
then `L ≤ KL(μ‖ν)`.

Each projection can only *lose* information, so by the data-processing inequality
`toReal_klDiv_map_le` every projected divergence is `≤ KL(μ‖ν)`; passing to the limit keeps the
bound. This is the rigorous **lower-bound half** of any *"KL between path measures = limit of
finite-dimensional (e.g. Euler–Maruyama / Cameron–Martin) KLs"* identity — and, unlike the matching
upper bound (which needs the projections to *exhaust* the σ-algebra, a martingale/Itô-flavoured
statement), it is **Itô-free**: it rests only on the DPI. In the DRSB energy identity
(`ChenGeorgiouPavon2021`), with `gᵢ` the time-grid projections and the projected divergences the
proved discrete control energies `emEnergy`, this yields `𝔼[∫₀¹ ½‖u‖²] ≤ D(P^{u}‖R)` — the `≥`
direction of the continuum (4.19) — with no stochastic integral. -/
theorem le_toReal_klDiv_of_map_tendsto
    (μ ν : Measure 𝓧) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hfin : klDiv μ ν ≠ ⊤)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {𝓨' : ι → Type*} [∀ i, MeasurableSpace (𝓨' i)]
    (g : ∀ i, 𝓧 → 𝓨' i) (hg : ∀ i, Measurable (g i))
    {L : ℝ}
    (hL : Tendsto (fun i => (klDiv (μ.map (g i)) (ν.map (g i))).toReal) l (nhds L)) :
    L ≤ (klDiv μ ν).toReal :=
  le_of_tendsto hL <| Eventually.of_forall fun i =>
    toReal_klDiv_map_le μ ν hμν (g i) (hg i) hfin

end ForMathlib.MeasureTheory
