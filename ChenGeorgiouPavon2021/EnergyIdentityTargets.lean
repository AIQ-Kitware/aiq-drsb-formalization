/-
# Ideal theorem targets for CGP energy identity / Girsanov edge

The assembly lemmas in `EnergyIdentity.lean` are proof-bearing.  The declarations here are the
remaining mathematical capstones that should eventually replace their explicit hypotheses.
-/

import ChenGeorgiouPavon2021.EnergyIdentity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (d : SBData X)


/-- A non-circular model relation saying that `Ku` and `Kw` are the controlled and reference
conditional path kernels for the same initial-state factorization.

The conditional Girsanov target below is false for arbitrary kernels; this predicate supplies the
missing structural relation without assuming the desired KL/energy equality. -/
structure IsControlledReferenceKernelPair
    (d : SBData X) (u : Control X) (ρ₀ : ProbabilityMeasure X)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴) : Prop where
  exists_common_path_factorization :
    ∃ e : Path X ≃ᵐ X × 𝒴,
      (d.pathLaw u ρ₀ : Measure (Path X)).map e = (ρ₀ : Measure X) ⊗ₘ Ku ∧
      (d.R : Measure (Path X)).map e = (initialMarginal d.R) ⊗ₘ Kw


/-- The real-valued conditional KL seen through a finite projection `π n` of the path-noise
coordinate.  Keeping this sequence named makes the projection-limit seams below explicit: finite
projection laws identify this sequence with a concrete Gaussian/grid expression, and a separate
exhaustion or Riemann-sum theorem supplies its limit. -/
noncomputable def conditionalProjectedKernelKL
    (ρ₀ : ProbabilityMeasure X)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴)
    {𝒵 : ℕ → Type*} [∀ n, MeasurableSpace (𝒵 n)]
    (π : ∀ n, 𝒴 → 𝒵 n) : ℕ → ℝ :=
  fun n : ℕ =>
    (∫⁻ x, InformationTheory.klDiv
      (Measure.map (π n) (Ku x))
      (Measure.map (π n) (Kw x)) ∂(ρ₀ : Measure X)).toReal

/-- Data needed for the KL-exhaustion half of the conditional Girsanov plan.

The field `finite_projection_law` is the finite-dimensional identification step: it says the abstract
projected conditional KL is the concrete projection-level quantity `projectionKL n`.  The field
`projectionKL_tendsto_kernelKL` is the genuine exhaustion theorem for that concrete quantity.  This is
not the conditional energy identity under another name: it does not mention control energy, and it is
only the KL-to-full-kernel limit edge. -/
structure ConditionalKLProjectionLimitData
    (ρ₀ : ProbabilityMeasure X)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴)
    {𝒵 : ℕ → Type*} [∀ n, MeasurableSpace (𝒵 n)]
    (π : ∀ n, 𝒴 → 𝒵 n) where
  projectionKL : ℕ → ℝ
  finite_projection_law : ∀ n, conditionalProjectedKernelKL ρ₀ Ku Kw π n = projectionKL n
  projectionKL_tendsto_kernelKL :
    Filter.Tendsto projectionKL Filter.atTop
      (nhds ((∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂(ρ₀ : Measure X)).toReal))

/-- Data needed for the finite-dimensional Cameron--Martin/Riemann-sum half of the conditional
Girsanov plan.

The field `finite_grid_girsanov` identifies each projected conditional KL with a concrete grid energy.
The field `gridEnergy_tendsto` is then the analytic convergence of those grid energies to the desired
quadratic-control energy value.  This avoids assuming the final conditional KL/energy identity while
exposing the two lower-level facts that a concrete diffusion model must prove. -/
structure ConditionalKLEnergyLimitData
    (ρ₀ : ProbabilityMeasure X)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴)
    {𝒵 : ℕ → Type*} [∀ n, MeasurableSpace (𝒵 n)]
    (π : ∀ n, 𝒴 → 𝒵 n) (energyVal : ℝ) where
  gridEnergy : ℕ → ℝ
  finite_grid_girsanov : ∀ n, conditionalProjectedKernelKL ρ₀ Ku Kw π n = gridEnergy n
  gridEnergy_tendsto : Filter.Tendsto gridEnergy Filter.atTop (nhds energyVal)

/-- Non-circular data package that instantiates the proved disintegrated energy identity.

`FiniteEnergyDiffusion` is only an integrability predicate, so it cannot by itself imply the full
path-law KL identity for an arbitrary abstract `SBData`.  The missing model data are the standard
start-plus-noise disintegration, finite-relative-entropy edges, and the conditional Cameron--Martin
identity.  This structure records exactly those inputs, without assuming the final path-law identity. -/
structure FiniteEnergyDiffusionEnergyIdentityData
    (d : SBData X) (u : Control X) (ρ₀ : ProbabilityMeasure X) where
  e : Path X ≃ᵐ X × Path X
  Ku : Kernel X (Path X)
  Kw : Kernel X (Path X)
  isMarkovKu : IsMarkovKernel Ku
  isMarkovKw : IsMarkovKernel Kw
  hPfact : (d.pathLaw u ρ₀ : Measure (Path X)).map e
      = (initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku
  hRfact : (d.R : Measure (Path X)).map e = (initialMarginal d.R) ⊗ₘ Kw
  hfin_marg : InformationTheory.klDiv
      (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R) ≠ ⊤
  hfin_cond : InformationTheory.klDiv
      ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku)
      ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Kw) ≠ ⊤
  hCM : (InformationTheory.klDiv
      ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku)
      ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Kw)).toReal
      = energy u (d.pathLaw u ρ₀)

omit [NormedSpace ℝ X] in
/-- Projection-level conditional KLs converge to the conditional path-kernel KL.

This is the KL-exhaustion half of the conditional Girsanov proof plan.  For a concrete standard
Borel path-noise carrier `𝒴`, finite measurable projections `π n` should generate the path-noise
sigma-algebra, and the conditional kernel KLs of the projected kernels should increase to the full
conditional kernel KL. -/
theorem conditional_gridKL_tendsto_kernelKL_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfe : FiniteEnergyDiffusion d u ρ₀)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (_hkernel : IsControlledReferenceKernelPair d u ρ₀ Ku Kw)
    {𝒵 : ℕ → Type*} [∀ n, MeasurableSpace (𝒵 n)]
    (π : ∀ n, 𝒴 → 𝒵 n) (_hπ : ∀ n, Measurable (π n))
    (_ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace 𝒴))
    (_hℱ : ∀ n, _ℱ n = (inferInstance : MeasurableSpace (𝒵 n)).comap (π n))
    (_hgen : ⨆ n, _ℱ n = (inferInstance : MeasurableSpace 𝒴))
    (hlimit : ConditionalKLProjectionLimitData ρ₀ Ku Kw π) :
    Filter.Tendsto (conditionalProjectedKernelKL ρ₀ Ku Kw π) Filter.atTop
      (nhds ((∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂(ρ₀ : Measure X)).toReal)) := by
  have hseq : conditionalProjectedKernelKL ρ₀ Ku Kw π = hlimit.projectionKL := by
    funext n
    exact hlimit.finite_projection_law n
  simpa [hseq] using hlimit.projectionKL_tendsto_kernelKL

omit [NormedSpace ℝ X] in
/-- Projection-level conditional KLs converge to the quadratic control energy.

This is the finite-dimensional Girsanov/Riemann-sum half of the conditional proof plan: after
projecting the conditional path kernels to finite grids, their Gaussian Cameron--Martin KLs are the
finite control energies, and those energies converge to the continuum quadratic control energy. -/
theorem conditional_gridKL_tendsto_energy_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfe : FiniteEnergyDiffusion d u ρ₀)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (_hkernel : IsControlledReferenceKernelPair d u ρ₀ Ku Kw)
    (energyVal : ℝ)
    (_henergy : energyVal = energy u (d.pathLaw u ρ₀))
    {𝒵 : ℕ → Type*} [∀ n, MeasurableSpace (𝒵 n)]
    (π : ∀ n, 𝒴 → 𝒵 n) (_hπ : ∀ n, Measurable (π n))
    (hlimit : ConditionalKLEnergyLimitData ρ₀ Ku Kw π energyVal) :
    Filter.Tendsto (conditionalProjectedKernelKL ρ₀ Ku Kw π) Filter.atTop (nhds energyVal) := by
  have hseq : conditionalProjectedKernelKL ρ₀ Ku Kw π = hlimit.gridEnergy := by
    funext n
    exact hlimit.finite_grid_girsanov n
  simpa [hseq] using hlimit.gridEnergy_tendsto

omit [NormedSpace ℝ X] in
/-- Conditional Cameron--Martin/Girsanov target for a controlled diffusion kernel.

The monolithic identity is now reduced to two smaller approximation theorems: finite-grid
conditional KLs converge to the full conditional kernel KL, and the same finite-grid KLs converge to
the quadratic control energy.  The proof here is just uniqueness of limits; the two analytic seams
above remain visible theorem targets. -/
theorem conditional_kl_eq_control_energy_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hfe : FiniteEnergyDiffusion d u ρ₀)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (hkernel : IsControlledReferenceKernelPair d u ρ₀ Ku Kw)
    (energyVal : ℝ)
    (henergy : energyVal = energy u (d.pathLaw u ρ₀))
    {𝒵 : ℕ → Type*} [∀ n, MeasurableSpace (𝒵 n)]
    (π : ∀ n, 𝒴 → 𝒵 n) (hπ : ∀ n, Measurable (π n))
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace 𝒴))
    (hℱ : ∀ n, ℱ n = (inferInstance : MeasurableSpace (𝒵 n)).comap (π n))
    (hgen : ⨆ n, ℱ n = (inferInstance : MeasurableSpace 𝒴))
    (hklLimit : ConditionalKLProjectionLimitData ρ₀ Ku Kw π)
    (henergyLimit : ConditionalKLEnergyLimitData ρ₀ Ku Kw π energyVal) :
    (∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂(ρ₀ : Measure X)).toReal = energyVal := by
  exact tendsto_nhds_unique
    (conditional_gridKL_tendsto_kernelKL_of_finiteEnergyDiffusion
      d u ρ₀ hfe Ku Kw hkernel π hπ ℱ hℱ hgen hklLimit)
    (conditional_gridKL_tendsto_energy_of_finiteEnergyDiffusion
      d u ρ₀ hfe Ku Kw hkernel energyVal henergy π hπ henergyLimit)

omit [NormedSpace ℝ X] in
/-- Full feasible-control energy identity from explicit disintegration and Cameron--Martin data.

This is now an assembly theorem, not an overclaim that finite-energy integrability alone implies the
Girsanov identity for an arbitrary abstract `SBData`.  The hard model work is factored into
`FiniteEnergyDiffusionEnergyIdentityData`: start-path disintegration, finite KL edges, and the
conditional Cameron--Martin identity. -/
theorem klReal_pathLaw_eq_initialKL_add_energy_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hfeas : Feasible d u ρ₀ ρ₁)
    (_hfed : FiniteEnergyDiffusion d u ρ₀)
    (hdata : FiniteEnergyDiffusionEnergyIdentityData d u ρ₀) :
    klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
      = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
        + energy u (d.pathLaw u ρ₀) := by
  letI : IsMarkovKernel hdata.Ku := hdata.isMarkovKu
  letI : IsMarkovKernel hdata.Kw := hdata.isMarkovKw
  exact energy_identity d u ρ₀ hdata.e hdata.Ku hdata.Kw
    hdata.hPfact hdata.hRfact hdata.hfin_marg hdata.hfin_cond hdata.hCM

omit [NormedSpace ℝ X] in
/-- Finite relative entropy of controlled path laws from the explicit finite-energy model data.

Finite-energy integrability alone cannot force finite path-space KL for an arbitrary abstract
`SBData`.  The non-circular finite-KL data are exactly the finite marginal and conditional KL edges in
`FiniteEnergyDiffusionEnergyIdentityData`; the proved chain rule and KL invariance under the
path-factorisation then assemble the full finite-KL fact. -/
theorem pathLaw_klDiv_ne_top_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfed : FiniteEnergyDiffusion d u ρ₀)
    (hdata : FiniteEnergyDiffusionEnergyIdentityData d u ρ₀) :
    InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤ := by
  letI : IsMarkovKernel hdata.Ku := hdata.isMarkovKu
  letI : IsMarkovKernel hdata.Kw := hdata.isMarkovKw
  haveI : IsProbabilityMeasure (initialMarginal (d.pathLaw u ρ₀)) := by
    unfold initialMarginal marginal
    exact Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℝ)).aemeasurable
  haveI : IsProbabilityMeasure (initialMarginal d.R) := by
    unfold initialMarginal marginal
    exact Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℝ)).aemeasurable
  rw [← ForMathlib.MeasureTheory.klDiv_map_measurableEquiv hdata.e
      (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)),
    hdata.hPfact, hdata.hRfact, InformationTheory.klDiv_compProd_eq_add]
  exact ENNReal.add_ne_top.mpr ⟨hdata.hfin_marg, hdata.hfin_cond⟩

omit [NormedSpace ℝ X] in
/-- Absolute continuity of finite-energy controlled path laws with respect to the reference law.

This is now derived from the finite-relative-entropy assembly theorem above. -/
theorem pathLaw_absCont_reference_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hfed : FiniteEnergyDiffusion d u ρ₀)
    (hdata : FiniteEnergyDiffusionEnergyIdentityData d u ρ₀) :
    (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)) := by
  exact (InformationTheory.klDiv_ne_top_iff.mp
    (pathLaw_klDiv_ne_top_of_finiteEnergyDiffusion d u ρ₀ hfed hdata)).1

end ChenGeorgiouPavon2021
