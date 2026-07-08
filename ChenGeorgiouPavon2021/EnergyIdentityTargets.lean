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

/-- Conditional Cameron--Martin/Girsanov target for a controlled diffusion kernel.

This is the model-level theorem that should supply the `hCM` edge of
`energy_identity_conditional`: conditional path-kernel relative entropy is exactly the expected
quadratic control energy. -/
theorem conditional_kl_eq_control_energy_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfe : FiniteEnergyDiffusion d u ρ₀)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (_hkernel : IsControlledReferenceKernelPair d u ρ₀ Ku Kw)
    (energyVal : ℝ)
    (_henergy : energyVal = energy u (d.pathLaw u ρ₀)) :
    (∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂(ρ₀ : Measure X)).toReal = energyVal := by
  sorry

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
