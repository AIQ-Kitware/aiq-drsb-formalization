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

/-- Model-specific Girsanov consequences for a finite-energy controlled diffusion.

The literal finite-energy predicate remains `FiniteEnergyDiffusion`; the additional fields below are
not derivable from an arbitrary abstract `SBData.pathLaw`.  They are the concrete SDE/Girsanov edges
that a real diffusion model must prove before downstream assembly can consume the path law as a
finite-relative-entropy controlled diffusion. -/
structure FiniteEnergyDiffusionModelEdges (u : Control X) (ρ₀ : ProbabilityMeasure X) : Prop where
  finite_energy : FiniteEnergyDiffusion d u ρ₀
  kl_identity :
    klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
      = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
        + energy u (d.pathLaw u ρ₀)
  pathLaw_abs_cont_reference :
    (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X))
  pathLaw_klDiv_ne_top :
    InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤

/-- Conditional Cameron--Martin/Girsanov target for a controlled diffusion kernel.

Finite energy of an abstract `SBData.pathLaw` does not determine arbitrary conditional kernels
`Ku`, `Kw`.  The concrete diffusion model must identify the kernels it constructs and supply the
conditional Cameron--Martin identity for those kernels. -/
theorem conditional_kl_eq_control_energy_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfe : FiniteEnergyDiffusion d u ρ₀)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (energyVal : ℝ)
    (_henergy : energyVal = energy u (d.pathLaw u ρ₀))
    (_hconditional :
      (∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂(ρ₀ : Measure X)).toReal = energyVal) :
    (∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂(ρ₀ : Measure X)).toReal = energyVal := by
  sorry

/-- Full feasible-control energy identity target.

The abstract finite-energy predicate alone is not enough for arbitrary `SBData`.  The honest target
therefore includes the model-specific Girsanov edge bundle that a concrete SDE construction must
supply. -/
theorem klReal_pathLaw_eq_initialKL_add_energy_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hfeas : Feasible d u ρ₀ ρ₁)
    (_hfed : FiniteEnergyDiffusionModelEdges d u ρ₀) :
    klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
      = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
        + energy u (d.pathLaw u ρ₀) := by
  sorry

/-- Absolute continuity of controlled path laws under the finite-energy SDE/Girsanov interface. -/
theorem pathLaw_absCont_reference_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfed : FiniteEnergyDiffusionModelEdges d u ρ₀) :
    (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)) := by
  sorry

/-- Finite relative entropy of controlled path laws under the finite-energy SDE/Girsanov interface. -/
theorem pathLaw_klDiv_ne_top_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfed : FiniteEnergyDiffusionModelEdges d u ρ₀) :
    InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤ := by
  sorry

end ChenGeorgiouPavon2021
