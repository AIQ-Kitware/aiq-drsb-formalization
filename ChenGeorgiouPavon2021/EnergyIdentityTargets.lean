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

/-- Finite relative entropy of finite-energy controlled path laws.

This remains the genuine probabilistic target. Once it is proved, absolute continuity follows by the
standard finite-KL consequence below. -/
theorem pathLaw_klDiv_ne_top_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (_hfed : FiniteEnergyDiffusion d u ρ₀) :
    InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤ := by
  sorry

/-- Absolute continuity of finite-energy controlled path laws with respect to the reference law.

This is now derived from the still-visible finite-relative-entropy target above. The remaining
probabilistic content is to prove that finite-energy controlled diffusions have finite KL against the
reference path law; absolute continuity is then the standard `klDiv_ne_top` consequence. -/
theorem pathLaw_absCont_reference_of_finiteEnergyDiffusion
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hfed : FiniteEnergyDiffusion d u ρ₀) :
    (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)) := by
  exact (InformationTheory.klDiv_ne_top_iff.mp
    (pathLaw_klDiv_ne_top_of_finiteEnergyDiffusion d u ρ₀ hfed)).1

end ChenGeorgiouPavon2021
