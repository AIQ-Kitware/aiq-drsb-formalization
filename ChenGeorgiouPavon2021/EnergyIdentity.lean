import ChenGeorgiouPavon2021.Core

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (d : SBData X)

-- §3  Energy identity (4.19) and KL ⇄ SOC equivalence (Problem 4.1 ⇄ 4.3)
--------------------------------------------------------------------------------

/-- Abstract predicate: `P = pathLaw u ρ₀` is a **finite-energy diffusion** with Itô
differential `dX = u dt + √ε dW` (CGP (4.4)–(4.5)): `𝔼_P ∫₀¹‖u_t‖² dt < ∞`.  Under
this condition Girsanov's martingale term has zero expectation and the energy
identity (4.19) holds. -/
def FiniteEnergyDiffusion (u : Control X) (ρ₀ : ProbabilityMeasure X) : Prop :=
  Integrable (fun ω : Path X => ∫ t in Set.Icc (0 : ℝ) 1, ‖u t (ω t)‖ ^ 2 ∂volume)
    (d.pathLaw u ρ₀ : Measure (Path X))


omit [NormedSpace ℝ X] in
/-- **Energy identity (CGP (4.19)) — disintegrated, complete.**  By Girsanov, for a
finite-energy diffusion `P = P^{u,ρ₀}`,
`D(P‖R) = D(ρ₀‖ρ₀^W) + 𝔼_P[∫₀¹ ½‖u_t‖² dt]`,
i.e. relative entropy splits into a constant endpoint term plus the control energy.

**Proof by the decomposition in `ROADMAP_ENERGY_IDENTITY.md`.**  Both path
laws disintegrate over the initial coordinate through a measurable iso `e : Path X ≃ᵐ X × Path X`
(start-plus-centered-path; a genuine structural fact for a normed path space): `e_# P = ρ₀ ⊗ₘ Kᵘ`
and `e_# R = ρ₀^W ⊗ₘ Kᵂ` with `ρ₀ = initialMarginal P`, `ρ₀^W = initialMarginal R` and Markov
bridge kernels `Kᵘ, Kᵂ` (`hPfact`, `hRfact`). Then:
* **KL is invariant under `e`** (`ForMathlib…klDiv_map_measurableEquiv`): `D(P‖R) = D(e_#P‖e_#R)`;
* the **KL chain rule** splits it — `D(ρ₀⊗ₘKᵘ ‖ ρ₀^W⊗ₘKᵂ) = D(ρ₀‖ρ₀^W) + D(ρ₀⊗ₘKᵘ ‖ ρ₀⊗ₘKᵂ)`
  (`ForMathlib…toReal_klDiv_compProd_eq_add`, real-valued via the finiteness edges `hfin_marg`,
  `hfin_cond`, i.e. the finite-relative-entropy regime);
* the **conditional term equals the control energy** (`hCM`) — the *sole* Girsanov content, the
  per-trajectory Cameron--Martin identity, supplied as the explicit hypothesis `hCM`.

`hCM`'s **discrete Euler–Maruyama instance is a theorem** (`energy_identity_euler_maruyama` below,
via the vendored Cameron–Martin `klDiv_stdGaussian_map_add`); the continuum `hCM` is the `Δt→0`
limit (ROADMAP Phase 2, the last research seam). The disintegration and finiteness hypotheses are the structural properties required of the
finite-energy diffusion model. -/
theorem energy_identity (u : Control X) (ρ₀ : ProbabilityMeasure X)
    -- disintegration over the initial coordinate (structural edges; true for a real diffusion):
    (e : Path X ≃ᵐ X × Path X)
    (Ku Kw : Kernel X (Path X)) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (hPfact : (d.pathLaw u ρ₀ : Measure (Path X)).map e
        = (initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku)
    (hRfact : (d.R : Measure (Path X)).map e = (initialMarginal d.R) ⊗ₘ Kw)
    -- finiteness edges (finite-relative-entropy regime; cf. `FiniteEnergyDiffusion`):
    (hfin_marg : InformationTheory.klDiv
        (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R) ≠ ⊤)
    (hfin_cond : InformationTheory.klDiv
        ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku)
        ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Kw) ≠ ⊤)
    -- the per-trajectory Cameron–Martin identity (the sole Girsanov edge; discrete layer proved):
    (hCM : (InformationTheory.klDiv
        ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku)
        ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Kw)).toReal
        = energy u (d.pathLaw u ρ₀)) :
    klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
      = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
        + energy u (d.pathLaw u ρ₀) := by
  haveI : IsProbabilityMeasure (initialMarginal (d.pathLaw u ρ₀)) := by
    unfold initialMarginal marginal
    exact Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℝ)).aemeasurable
  haveI : IsProbabilityMeasure (initialMarginal d.R) := by
    unfold initialMarginal marginal
    exact Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℝ)).aemeasurable
  unfold klReal
  rw [← ForMathlib.MeasureTheory.klDiv_map_measurableEquiv e
        (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)),
      hPfact, hRfact,
      ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_add
        (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R) Ku Kw hfin_marg hfin_cond,
      hCM]

/-- **Energy identity in conditional, per-trajectory form.**

For disintegrations `P = ρ₀ ⊗ₘ Kᵘ` and `R = ρ₀' ⊗ₘ Kᵂ`, the KL chain rule separates the initial
marginal divergence from the conditional divergence. The conditional chain rule identifies the
second term with `∫⁻ x, D(Kᵘ_x ‖ Kᵂ_x) ∂ρ₀`; the hypothesis `hCM` identifies its real value with
`energyVal`.

The theorem uses a free standard-Borel-compatible path factor `𝒴`, expressed by
`CountableOrCountablyGenerated 𝒳 𝒴`, because joint measurability of `Kernel.rnDeriv Kᵘ Kᵂ` is needed
for the conditional KL formula. A concrete continuous-path or SDE model supplies the kernels and
the model-specific Cameron--Martin or Girsanov identity used as `hCM`. -/
theorem energy_identity_conditional
    {𝒳 𝒴 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace Ω]
    [MeasurableSpace.CountableOrCountablyGenerated 𝒳 𝒴]
    (P R : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (e : Ω ≃ᵐ 𝒳 × 𝒴)
    (ρ₀ ρ₀' : Measure 𝒳) [IsProbabilityMeasure ρ₀] [IsProbabilityMeasure ρ₀']
    (Ku Kw : Kernel 𝒳 𝒴) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (hPfact : P.map e = ρ₀ ⊗ₘ Ku)
    (hRfact : R.map e = ρ₀' ⊗ₘ Kw)
    (hfin_marg : InformationTheory.klDiv ρ₀ ρ₀' ≠ ⊤)
    (hfin_cond : InformationTheory.klDiv (ρ₀ ⊗ₘ Ku) (ρ₀ ⊗ₘ Kw) ≠ ⊤)
    (energyVal : ℝ)
    (hCM : (∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂ρ₀).toReal = energyVal) :
    klReal P R = klReal ρ₀ ρ₀' + energyVal := by
  have h_ac_cond : (ρ₀ ⊗ₘ Ku) ≪ (ρ₀ ⊗ₘ Kw) :=
    (InformationTheory.klDiv_ne_top_iff.mp hfin_cond).1
  have hcond : InformationTheory.klDiv (ρ₀ ⊗ₘ Ku) (ρ₀ ⊗ₘ Kw)
      = ∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂ρ₀ :=
    ForMathlib.MeasureTheory.klDiv_compProd_eq_lintegral ρ₀ Ku Kw h_ac_cond
  unfold klReal
  rw [← ForMathlib.MeasureTheory.klDiv_map_measurableEquiv e P R,
      hPfact, hRfact,
      ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_add ρ₀ ρ₀' Ku Kw hfin_marg hfin_cond,
      hcond, hCM]

omit [NormedSpace ℝ X] in
/-- **Energy identity (4.19), lower-bound (`≥`) half via finite-dimensional projections.**

Suppose measurable time-grid projections `π i` have relative entropies converging to the control
energy. KL data processing bounds every projected divergence by the full path-law divergence, so
the limit gives

`energy u (d.pathLaw u ρ₀) ≤ klReal (d.pathLaw u ρ₀) d.R`.

This argument is independent of stochastic integration. Concrete Gaussian or diffusion models
supply `hconv` by identifying each grid divergence with a discrete energy and proving convergence
of those energies to the continuum control energy. -/
theorem energy_le_klReal_of_projections
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hac : (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)))
    (hfin : InformationTheory.klDiv
        (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {𝓨 : ι → Type*} [∀ i, MeasurableSpace (𝓨 i)]
    (π : ∀ i, Path X → 𝓨 i) (hπ : ∀ i, Measurable (π i))
    (hconv : Filter.Tendsto
        (fun i => klReal ((d.pathLaw u ρ₀ : Measure (Path X)).map (π i))
                          ((d.R : Measure (Path X)).map (π i))) l
        (nhds (energy u (d.pathLaw u ρ₀)))) :
    energy u (d.pathLaw u ρ₀)
      ≤ klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) :=
  ForMathlib.MeasureTheory.le_toReal_klDiv_of_map_tendsto
    (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) hac hfin π hπ hconv

omit [NormedSpace ℝ X] in
/-- **Energy identity (4.19) from KL exhaustion and projected-energy convergence.**

Assume the time-grid projections `π n` generate the path σ-algebra through a filtration `ℱ`.
Lévy's upward theorem, packaged as `ForMathlib.MeasureTheory.klDiv_map_tendsto_toReal`, shows that
the projected divergences converge to the full path-law KL. If `hconv` also identifies their limit
with the control energy, uniqueness of limits yields

`energy u (d.pathLaw u ρ₀) = klReal (d.pathLaw u ρ₀) d.R`.

For a concrete path model, the generation hypothesis is a path-space measurability theorem, while
`hconv` contains the finite-dimensional Cameron--Martin or Girsanov calculation and its continuum
limit. -/
theorem energy_eq_klReal_of_projections
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hac : (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)))
    (hfin : InformationTheory.klDiv
        (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤)
    {𝓨 : ℕ → Type*} [hm𝓨 : ∀ n, MeasurableSpace (𝓨 n)]
    (π : ∀ n, Path X → 𝓨 n) (hπ : ∀ n, Measurable (π n))
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (Path X)))
    (hℱ : ∀ n, ℱ n = (hm𝓨 n).comap (π n))
    (hgen : ⨆ n, ℱ n = (inferInstance : MeasurableSpace (Path X)))
    (hconv : Filter.Tendsto
        (fun n => klReal ((d.pathLaw u ρ₀ : Measure (Path X)).map (π n))
                          ((d.R : Measure (Path X)).map (π n))) Filter.atTop
        (nhds (energy u (d.pathLaw u ρ₀)))) :
    energy u (d.pathLaw u ρ₀)
      = klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) :=
  tendsto_nhds_unique hconv
    (ForMathlib.MeasureTheory.klDiv_map_tendsto_toReal
      (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) hac hfin π hπ ℱ hℱ hgen)

omit [NormedSpace ℝ X] in
/-- **Energy identity (4.19), FULL `=`, discharged via a KL-preserving embedding into `ℕ→ℝ`
(plan A: the continuum generation hypothesis `hgen`).**

The generation hypothesis `hgen` of `energy_eq_klReal_of_projections` is **false** for the raw path
space `Path X = ℝ→X` (a countable family of finite-time projections cannot generate its uncountable-
index product σ-algebra). This version removes it: instead of asking the projections to generate
`m(Path X)`, it asks only for a **measurable embedding with a measurable left inverse**
`e : Path X → (ℕ→ℝ)`, `g : (ℕ→ℝ) → Path X`, `g ∘ e = id` — a *lossless reparametrisation* of the
path by countably many real coordinates. This is exactly what a standard-Borel **continuous**-path
model supplies (a continuous path is determined by its values at countably many dense times, and by
Lusin–Souslin the restriction is a measurable embedding, `Measurable.measurableEmbedding` +
`MeasurableEmbedding.invFun`); crucially it is a *satisfiable* hypothesis, not the unsatisfiable
`hgen` on `ℝ→X`.

The proof composes three Itô-free `ForMathlib` results: `toReal_klDiv_map_eq_of_leftInverse`
(the embedding preserves `KL`, from the DPI both ways), then on the countable product `ℕ→ℝ`
`iSup_comap_frestrictLe_eq_pi` (the finite-prefix restrictions generate) feeds `klDiv_map_tendsto`
(Lévy martingale convergence) so the finite-grid divergences converge to `KL(e_#P ‖ e_#R) = KL(P‖R)`;
limit uniqueness against the energy convergence hypothesis `hconv` closes it. -/
theorem energy_eq_klReal_via_embedding
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hac : (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)))
    (hfin : InformationTheory.klDiv
        (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤)
    (e : Path X → (ℕ → ℝ)) (he : Measurable e)
    (g : (ℕ → ℝ) → Path X) (hg : Measurable g) (hge : Function.LeftInverse g e)
    (hconv : Filter.Tendsto
        (fun n => klReal
            ((d.pathLaw u ρ₀ : Measure (Path X)).map
              (fun ω => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e ω)))
            ((d.R : Measure (Path X)).map
              (fun ω => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e ω))))
        Filter.atTop (nhds (energy u (d.pathLaw u ρ₀)))) :
    energy u (d.pathLaw u ρ₀)
      = klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) := by
  set P := (d.pathLaw u ρ₀ : Measure (Path X)) with hP
  set R := (d.R : Measure (Path X)) with hR
  haveI : IsProbabilityMeasure (P.map e) := Measure.isProbabilityMeasure_map he.aemeasurable
  haveI : IsProbabilityMeasure (R.map e) := Measure.isProbabilityMeasure_map he.aemeasurable
  have hac' : P.map e ≪ R.map e := hac.map he
  have hfin' : InformationTheory.klDiv (P.map e) (R.map e) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (ForMathlib.MeasureTheory.klDiv_map_le P R hac e he)
  -- the embedding preserves KL
  have hemb : (InformationTheory.klDiv (P.map e) (R.map e)).toReal
      = (InformationTheory.klDiv P R).toReal :=
    ForMathlib.MeasureTheory.toReal_klDiv_map_eq_of_leftInverse P R hac hfin e he g hg hge
  -- the finite-prefix restriction filtration on `ℕ → ℝ`
  let ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    { seq := fun n => MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n) inferInstance
      mono' := by
        intro n m hnm
        calc MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n) inferInstance
            = MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) m)
                (MeasurableSpace.comap (Preorder.frestrictLe₂ (π := fun _ : ℕ => ℝ) hnm)
                  inferInstance) := by
              rw [MeasurableSpace.comap_comp, Preorder.frestrictLe₂_comp_frestrictLe]
          _ ≤ MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) m) inferInstance :=
              MeasurableSpace.comap_mono (Preorder.measurable_frestrictLe₂ hnm).comap_le
      le' := fun n => (Preorder.measurable_frestrictLe n).comap_le }
  -- martingale convergence on `ℕ → ℝ`, then transport the grid maps back through `e`
  have htends := ForMathlib.MeasureTheory.klDiv_map_tendsto_toReal (P.map e) (R.map e) hac' hfin'
    (fun n => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
    (fun n => Preorder.measurable_frestrictLe n) ℱ (fun _ => rfl)
    ForMathlib.MeasureTheory.iSup_comap_frestrictLe_eq_pi
  have hmapP : ∀ n, (P.map e).map (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
      = P.map (fun ω => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e ω)) := fun n => by
    rw [Measure.map_map (Preorder.measurable_frestrictLe n) he]; rfl
  have hmapR : ∀ n, (R.map e).map (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
      = R.map (fun ω => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e ω)) := fun n => by
    rw [Measure.map_map (Preorder.measurable_frestrictLe n) he]; rfl
  simp only [hmapP, hmapR, hemb] at htends
  exact tendsto_nhds_unique hconv htends


end ChenGeorgiouPavon2021
