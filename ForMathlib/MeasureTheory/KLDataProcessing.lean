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

/-- **Conditional-expectation representation of a pushforward KL** (`≤`-half sub-plan, step 1).
For probability measures `μ ≪ ν` and measurable `g`, the pushforward divergence is the `klFun`
integral of the *conditional expectation* of the density `dμ/dν` onto the sub-σ-algebra `comap g`:
`(klDiv (μ.map g) (ν.map g)).toReal = ∫ x, klFun ((ν[dμ/dν | comap g]) x) ∂ν`.

This is the martingale-value representation underlying both the data-processing inequality
(`toReal_klDiv_map_le`, one conditional-Jensen step past this) and the L¹ martingale-convergence
identity `KL(μ‖ν) = limₙ KL(gₙ_#μ ‖ gₙ_#ν)` (Lévy's upward theorem applied to `Mₙ = ν[dμ/dν|comap gₙ]`,
the Itô-free structural core of the continuum energy identity's `≤` half — see
`ROADMAP_ENERGY_IDENTITY.md`).

Proof: express the pushforward KL as `∫ klFun(d(g_#μ)/d(g_#ν))` (`toReal_klDiv_eq_integral_klFun`),
pull the integral back through `g` (`integral_map`), and rewrite the pushed-forward Radon–Nikodym
derivative as the conditional expectation (`toReal_rnDeriv_map`). -/
theorem toReal_klDiv_map_eq_integral_condExp
    (μ ν : Measure 𝓧) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (g : 𝓧 → 𝓨) (hg : Measurable g) :
    (klDiv (μ.map g) (ν.map g)).toReal
      = ∫ x, klFun ((ν[fun a => (μ.rnDeriv ν a).toReal | m𝓨.comap g]) x) ∂ν := by
  classical
  haveI : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  haveI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hmapac : μ.map g ≪ ν.map g := hμν.map hg
  rw [toReal_klDiv_eq_integral_klFun hmapac]
  have hLHSmap : (∫ y, klFun ((μ.map g).rnDeriv (ν.map g) y).toReal ∂(ν.map g))
      = ∫ x, klFun ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ∂ν := by
    rw [integral_map hg.aemeasurable]
    exact Measurable.aestronglyMeasurable (by fun_prop)
  rw [hLHSmap]
  refine integral_congr_ae ?_
  filter_upwards [toReal_rnDeriv_map (μ := μ) (ν := ν) hμν hg] with x hx
  rw [hx]

/-- **`ℝ≥0∞`-valued conditional-expectation representation of a pushforward KL** (`≤`-half
sub-plan, step 2a). The `ℝ≥0∞` companion of `toReal_klDiv_map_eq_integral_condExp`:
`klDiv (μ.map g) (ν.map g) = ∫⁻ x, ENNReal.ofReal (klFun ((ν[dμ/dν | comap g]) x)) ∂ν`.
Working in `ℝ≥0∞` lets the martingale limit use monotone-convergence / Fatou
(`lintegral_liminf_le`) with no finiteness bookkeeping, converting to `toReal` only at the end. -/
theorem klDiv_map_eq_lintegral_ofReal_klFun_condExp
    (μ ν : Measure 𝓧) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (g : 𝓧 → 𝓨) (hg : Measurable g) :
    klDiv (μ.map g) (ν.map g)
      = ∫⁻ x, ENNReal.ofReal
          (klFun ((ν[fun a => (μ.rnDeriv ν a).toReal | m𝓨.comap g]) x)) ∂ν := by
  classical
  haveI : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  haveI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hmapac : μ.map g ≪ ν.map g := hμν.map hg
  have hf : Measurable
      (fun y => ENNReal.ofReal (klFun ((μ.map g).rnDeriv (ν.map g) y).toReal)) :=
    (measurable_klFun.comp
      (Measure.measurable_rnDeriv (μ.map g) (ν.map g)).ennreal_toReal).ennreal_ofReal
  rw [klDiv_eq_lintegral_klFun_of_ac hmapac, lintegral_map hf hg]
  refine lintegral_congr_ae ?_
  filter_upwards [toReal_rnDeriv_map (μ := μ) (ν := ν) hμν hg] with x hx
  rw [hx]

/-- **Data-processing inequality for KL divergence** (`ℝ≥0∞` form; `≤`-half sub-plan, step 2b).
For probability measures `μ ≪ ν` and measurable `g`, `klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν` as
elements of `ℝ≥0∞` — no finiteness hypothesis. Coarse-graining decreases relative entropy.

This is the `ℝ≥0∞` strengthening of `toReal_klDiv_map_le`; it supplies the `limsup ≤ KL(μ‖ν)` bound of
the martingale-convergence limit (each projected divergence is `≤` the full one). Proof: the `ℝ≥0∞`
representation (`klDiv_map_eq_lintegral_ofReal_klFun_condExp`) puts both sides as `klFun` integrals,
and conditional Jensen (`ConvexOn.map_condExp_le` on the convex generator `klFun`) plus
`integral_condExp` gives the pointwise/averaged bound. -/
theorem klDiv_map_le
    (μ ν : Measure 𝓧) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (g : 𝓧 → 𝓨) (hg : Measurable g) :
    klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν := by
  classical
  by_cases hfin : klDiv μ ν = ⊤
  · rw [hfin]; exact le_top
  have hm : m𝓨.comap g ≤ m𝓧 := hg.comap_le
  haveI : SigmaFinite (ν.trim hm) := by infer_instance
  rw [klDiv_map_eq_lintegral_ofReal_klFun_condExp μ ν hμν g hg,
      klDiv_eq_lintegral_klFun_of_ac hμν]
  set F₀ : 𝓧 → ℝ := fun a => (μ.rnDeriv ν a).toReal with hF₀
  have hllr : Integrable (llr μ ν) μ := (klDiv_ne_top_iff.mp hfin).2
  have hF₀int : Integrable F₀ ν := Measure.integrable_toReal_rnDeriv
  have hklF₀int : Integrable (fun a => klFun (F₀ a)) ν :=
    (integrable_klFun_rnDeriv_iff hμν).mpr hllr
  have hcondnn : (0 : 𝓧 → ℝ) ≤ᵐ[ν] ν[fun a => klFun (F₀ a) | m𝓨.comap g] :=
    condExp_nonneg (ae_of_all _ fun a => klFun_nonneg ENNReal.toReal_nonneg)
  have hjensen : (fun x => klFun ((ν[F₀ | m𝓨.comap g]) x))
      ≤ᵐ[ν] ν[fun a => klFun (F₀ a) | m𝓨.comap g] :=
    ConvexOn.map_condExp_le hm convexOn_klFun
      (continuous_klFun.lowerSemicontinuous.lowerSemicontinuousOn _)
      (ae_of_all _ fun a => ENNReal.toReal_nonneg) isClosed_Ici hF₀int hklF₀int
  calc ∫⁻ x, ENNReal.ofReal (klFun ((ν[F₀ | m𝓨.comap g]) x)) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal ((ν[fun a => klFun (F₀ a) | m𝓨.comap g]) x) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hjensen] with x hx using ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal (∫ x, (ν[fun a => klFun (F₀ a) | m𝓨.comap g]) x ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal integrable_condExp hcondnn).symm
    _ = ENNReal.ofReal (∫ x, klFun (F₀ x) ∂ν) := by rw [integral_condExp hm]
    _ = ∫⁻ x, ENNReal.ofReal (klFun (F₀ x)) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hklF₀int
          (ae_of_all _ fun a => klFun_nonneg ENNReal.toReal_nonneg)

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

/-- **Martingale-convergence identity for KL along a generating filtration** (`≤`-half core,
step 2c — the Itô-free structural theorem). For probability measures `μ ≪ ν` with finite `KL`, a
sequence of measurable maps `gₙ : 𝓧 → 𝓨' n` whose induced sub-σ-algebras `comap gₙ` form a
filtration `ℱ` that **generates** `m𝓧` (`⨆ n, ℱ n = m𝓧`), the pushforward divergences converge *up*
to the full divergence:
`(klDiv (μ.map gₙ) (ν.map gₙ)).toReal → (klDiv μ ν).toReal`.

This is the direction the data-processing inequality does **not** give — "the finite-dimensional
projections capture all of the KL" — and it is **Itô-free**: it is Lévy's upward theorem
(`MeasureTheory.Integrable.tendsto_ae_condExp`, which Mathlib has) applied to the density
`Mₙ = ν[dμ/dν | ℱ n]`, plus Fatou (`lintegral_liminf_le`) for `KL ≤ liminf` and the `ℝ≥0∞`
data-processing inequality (`klDiv_map_le`) for `limsup ≤ KL`. Combined with the DPI, it turns
`ChenGeorgiouPavon2021.energy_le_klReal_of_projections` from a `≥` bound into a full `=`, modulo only
the (Itô-flavoured) marginal-KL convergence edge — see `ROADMAP_ENERGY_IDENTITY.md`. -/
theorem klDiv_map_tendsto_toReal
    (μ ν : Measure 𝓧) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hfin : klDiv μ ν ≠ ⊤)
    {𝓨' : ℕ → Type*} [hm𝓨' : ∀ n, MeasurableSpace (𝓨' n)]
    (g : ∀ n, 𝓧 → 𝓨' n) (hg : ∀ n, Measurable (g n))
    (ℱ : MeasureTheory.Filtration ℕ m𝓧)
    (hℱ : ∀ n, ℱ n = (hm𝓨' n).comap (g n))
    (hgen : ⨆ n, ℱ n = m𝓧) :
    Tendsto (fun n => (klDiv (μ.map (g n)) (ν.map (g n))).toReal) atTop
      (nhds (klDiv μ ν).toReal) := by
  classical
  set F₀ : 𝓧 → ℝ := fun a => (μ.rnDeriv ν a).toReal with hF₀
  have hF₀int : Integrable F₀ ν := Measure.integrable_toReal_rnDeriv
  have hF₀meas : StronglyMeasurable[⨆ n, ℱ n] F₀ := by
    rw [hgen]; exact (Measure.measurable_rnDeriv μ ν).ennreal_toReal.stronglyMeasurable
  -- Lévy's upward theorem: the density martingale converges a.e. to `dμ/dν`
  have hlevy : ∀ᵐ x ∂ν, Tendsto (fun n => (ν[F₀ | ℱ n]) x) atTop (nhds (F₀ x)) :=
    hF₀int.tendsto_ae_condExp hF₀meas
  have hklconv : ∀ᵐ x ∂ν,
      Tendsto (fun n => ENNReal.ofReal (klFun ((ν[F₀ | ℱ n]) x))) atTop
        (nhds (ENNReal.ofReal (klFun (F₀ x)))) := by
    filter_upwards [hlevy] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_klFun.tendsto _).comp hx)
  -- ℝ≥0∞ representations of each projected divergence and of the total
  have hbn : ∀ n, klDiv (μ.map (g n)) (ν.map (g n))
      = ∫⁻ x, ENNReal.ofReal (klFun ((ν[F₀ | ℱ n]) x)) ∂ν := by
    intro n
    have h := klDiv_map_eq_lintegral_ofReal_klFun_condExp μ ν hμν (g n) (hg n)
    rw [hℱ n]; exact h
  have hM : klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (F₀ x)) ∂ν :=
    klDiv_eq_lintegral_klFun_of_ac hμν
  have hmeas_n : ∀ n, Measurable
      (fun x => ENNReal.ofReal (klFun ((ν[F₀ | ℱ n]) x))) := fun n =>
    (measurable_klFun.comp
      (stronglyMeasurable_condExp.mono (ℱ.le n)).measurable).ennreal_ofReal
  -- ℝ≥0∞ convergence of the divergences via a liminf/limsup sandwich
  have htends : Tendsto (fun n => klDiv (μ.map (g n)) (ν.map (g n))) atTop
      (nhds (klDiv μ ν)) := by
    simp_rw [hbn]; rw [hM]
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    · -- Fatou: `∫⁻ klFun(F₀) = ∫⁻ liminf klFun(Mₙ) ≤ liminf ∫⁻ klFun(Mₙ)`
      calc ∫⁻ x, ENNReal.ofReal (klFun (F₀ x)) ∂ν
          = ∫⁻ x, liminf (fun n => ENNReal.ofReal (klFun ((ν[F₀ | ℱ n]) x))) atTop ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards [hklconv] with x hx using hx.liminf_eq.symm
        _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (klFun ((ν[F₀ | ℱ n]) x)) ∂ν) atTop :=
            lintegral_liminf_le hmeas_n
    · -- each term `≤ KL` by the ℝ≥0∞ data-processing inequality
      refine limsup_le_of_le ?_ (Eventually.of_forall fun n => ?_)
      · exact isCobounded_le_of_bot
      · rw [← hbn n, ← hM]; exact klDiv_map_le μ ν hμν (g n) (hg n)
  exact (ENNReal.continuousAt_toReal hfin).tendsto.comp htends

end ForMathlib.MeasureTheory
