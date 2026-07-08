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

/-- Conditional Cameron--Martin/Girsanov target for a controlled diffusion kernel.

This is the model-level theorem that should supply the `hCM` edge of
`energy_identity_conditional`: conditional path-kernel relative entropy is exactly the expected
quadratic control energy. -/
theorem conditional_kl_eq_control_energy_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfe : FiniteEnergyDiffusion d u ρ₀)
    {𝒴 : Type*} [MeasurableSpace 𝒴]
    (Ku Kw : Kernel X 𝒴) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (energyVal : ℝ)
    (_henergy : energyVal = energy u (d.pathLaw u ρ₀)) :
    (∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂(ρ₀ : Measure X)).toReal = energyVal := by
  sorry

/-- Full feasible-control energy identity target.

Once the disintegration data, finiteness facts, and conditional Cameron--Martin theorem are
available from the concrete SDE model, this theorem should provide the `hEI` hypothesis of
`schrodingerBridge_KL_eq_SOC` for every feasible control. -/
theorem klReal_pathLaw_eq_initialKL_add_energy_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ ρ₁ : ProbabilityMeasure X)
    (_hfeas : Feasible d u ρ₀ ρ₁)
    (_hfed : FiniteEnergyDiffusion d u ρ₀) :
    klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
      = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
        + energy u (d.pathLaw u ρ₀) := by
  sorry

/-- Absolute continuity of finite-energy controlled path laws with respect to the reference law. -/
theorem pathLaw_absCont_reference_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfed : FiniteEnergyDiffusion d u ρ₀) :
    (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)) := by
  sorry

/-- Finite relative entropy of finite-energy controlled path laws. -/
theorem pathLaw_klDiv_ne_top_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfed : FiniteEnergyDiffusion d u ρ₀) :
    InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤ := by
  sorry

end ChenGeorgiouPavon2021
