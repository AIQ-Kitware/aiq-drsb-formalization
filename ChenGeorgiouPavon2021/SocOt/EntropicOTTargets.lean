/-
# Ideal theorem targets for static SB / entropic OT optimizer structure
-/

import ChenGeorgiouPavon2021.SocOt.EntropicOT

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (d : SBData X)

/-- Feasibility target for the Schrödinger product-form coupling. -/
theorem schrodinger_product_coupling_feasible
    (φhat0 φ1 : X → ℝ) (ρ₀ ρ₁ : ProbabilityMeasure X)
    (π_prod : ProbabilityMeasure (X × X))
    (_hπprod : (π_prod : Measure (X × X))
        = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2))) :
    π_prod ∈ couplings ρ₀ ρ₁ := by
  sorry

/-- Optimality target for the Schrödinger product-form coupling. -/
theorem schrodinger_product_coupling_optimal
    (φhat0 φ1 : X → ℝ) (ρ₀ ρ₁ : ProbabilityMeasure X)
    (π_prod : ProbabilityMeasure (X × X))
    (_hπprod : (π_prod : Measure (X × X))
        = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2))) :
    klReal (π_prod : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ := by
  sorry

/-- Uniqueness target for the static KL projection over endpoint couplings. -/
theorem staticSB_klProjection_unique
    (ρ₀ ρ₁ : ProbabilityMeasure X) :
    ∀ π π' : ProbabilityMeasure (X × X),
      π ∈ couplings ρ₀ ρ₁ →
      klReal (π : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ →
      π' ∈ couplings ρ₀ ρ₁ →
      klReal (π' : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ →
      π = π' := by
  sorry

/-- Existence/attainment target for the static Schrödinger bridge optimizer. -/
theorem staticSB_optimizer_exists
    (ρ₀ ρ₁ : ProbabilityMeasure X) :
    ∃ π_star : ProbabilityMeasure (X × X),
      π_star ∈ couplings ρ₀ ρ₁ ∧
      klReal (π_star : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ := by
  sorry

end ChenGeorgiouPavon2021
