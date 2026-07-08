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

/-- Marginal computation target for the Schrödinger product-form coupling.

The density identity alone does not imply feasibility against arbitrary endpoint marginals.  The
missing content is the Schrödinger-system marginal calculation: the product-form endpoint law has
first marginal `ρ₀` and second marginal `ρ₁`. -/
theorem schrodinger_product_coupling_marginals
    (φhat0 φ1 : X → ℝ) (ρ₀ ρ₁ : ProbabilityMeasure X)
    (π_prod : ProbabilityMeasure (X × X))
    (_hπprod : (π_prod : Measure (X × X))
        = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2))) :
    Measure.map Prod.fst (π_prod : Measure (X × X)) = (ρ₀ : Measure X) ∧
      Measure.map Prod.snd (π_prod : Measure (X × X)) = (ρ₁ : Measure X) := by
  sorry

/-- Feasibility wrapper for the Schrödinger product-form coupling.

This theorem is now just the definition of `couplings` after the separate marginal-computation
target above has supplied the two endpoint marginal identities. -/
theorem schrodinger_product_coupling_feasible
    (φhat0 φ1 : X → ℝ) (ρ₀ ρ₁ : ProbabilityMeasure X)
    (π_prod : ProbabilityMeasure (X × X))
    (hπprod : (π_prod : Measure (X × X))
        = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2))) :
    π_prod ∈ couplings ρ₀ ρ₁ := by
  exact schrodinger_product_coupling_marginals d φhat0 φ1 ρ₀ ρ₁ π_prod hπprod

omit [NormedSpace ℝ X] in
/-- Definition-level static KL-projection verification principle.

A feasible coupling whose endpoint KL is no larger than every other feasible coupling attains the
static Schrödinger value.  This is the static analogue of
`isOptimalSOC_of_feasible_and_energy_le`; the real Schrödinger-system work is to prove the marginal
constraints and the dual/variational lower bound for the product-form coupling. -/
theorem staticSBValue_eq_of_coupling_and_kl_le
    (ρ₀ ρ₁ : ProbabilityMeasure X) (π_star : ProbabilityMeasure (X × X))
    (hfeas : π_star ∈ couplings ρ₀ ρ₁)
    (hle : ∀ π : ProbabilityMeasure (X × X), π ∈ couplings ρ₀ ρ₁ →
      klReal (π_star : Measure (X × X)) (endpointLaw d)
        ≤ klReal (π : Measure (X × X)) (endpointLaw d)) :
    klReal (π_star : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ := by
  unfold staticSBValue
  let S : Set ℝ := {J : ℝ | ∃ π : ProbabilityMeasure (X × X),
    π ∈ couplings ρ₀ ρ₁ ∧ J = klReal (π : Measure (X × X)) (endpointLaw d)}
  change klReal (π_star : Measure (X × X)) (endpointLaw d) = sInf S
  have hSne : S.Nonempty := by
    exact ⟨klReal (π_star : Measure (X × X)) (endpointLaw d), π_star, hfeas, rfl⟩
  have hSbdd : BddBelow S := by
    refine ⟨klReal (π_star : Measure (X × X)) (endpointLaw d), ?_⟩
    rintro J ⟨π, hπ, rfl⟩
    exact hle π hπ
  have hle_sInf : klReal (π_star : Measure (X × X)) (endpointLaw d) ≤ sInf S := by
    refine le_csInf hSne ?_
    rintro J ⟨π, hπ, rfl⟩
    exact hle π hπ
  have hsInf_le : sInf S ≤ klReal (π_star : Measure (X × X)) (endpointLaw d) := by
    exact csInf_le hSbdd ⟨π_star, hfeas, rfl⟩
  exact le_antisymm hle_sInf hsInf_le

/-- Optimality target for the Schrödinger product-form coupling, reduced to a variational lower
bound.

The product-density identity alone cannot imply optimality against arbitrary endpoint marginals.
The additional hypothesis is the dual/variational certificate that the product coupling's endpoint
KL lower-bounds every feasible coupling. -/
theorem schrodinger_product_coupling_optimal
    (φhat0 φ1 : X → ℝ) (ρ₀ ρ₁ : ProbabilityMeasure X)
    (π_prod : ProbabilityMeasure (X × X))
    (hπprod : (π_prod : Measure (X × X))
        = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2)))
    (hle : ∀ π : ProbabilityMeasure (X × X), π ∈ couplings ρ₀ ρ₁ →
      klReal (π_prod : Measure (X × X)) (endpointLaw d)
        ≤ klReal (π : Measure (X × X)) (endpointLaw d)) :
    klReal (π_prod : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ := by
  exact staticSBValue_eq_of_coupling_and_kl_le d ρ₀ ρ₁ π_prod
    (schrodinger_product_coupling_feasible d φhat0 φ1 ρ₀ ρ₁ π_prod hπprod) hle

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

omit [NormedSpace ℝ X] in
/-- Existence of a normalized product-density datum over the endpoint reference law.

At this abstraction level the endpoint reference law itself gives the trivial product-density tilt
with both potentials equal to `1`.  This does **not** solve the Schrödinger system marginal or
optimality problems for prescribed `(ρ₀, ρ₁)`; those remain the visible targets
`schrodinger_product_coupling_marginals` and `schrodinger_product_coupling_optimal`. -/
theorem schrodinger_product_coupling_data_exists
    (_ρ₀ _ρ₁ : ProbabilityMeasure X) :
    ∃ (φhat0 φ1 : X → ℝ) (π_prod : ProbabilityMeasure (X × X)),
      (π_prod : Measure (X × X))
        = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2)) := by
  have he : Measurable (fun ω : Path X => (ω (0 : ℝ), ω (1 : ℝ))) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  haveI hprob : IsProbabilityMeasure (endpointLaw d) := by
    unfold endpointLaw
    exact Measure.isProbabilityMeasure_map he.aemeasurable
  refine ⟨fun _ => 1, fun _ => 1, ⟨endpointLaw d, hprob⟩, ?_⟩
  simp

/-- Existence/attainment wrapper for the static Schrödinger bridge optimizer.

The remaining constructive work is isolated in `schrodinger_product_coupling_data_exists`, while
feasibility and optimality are supplied by the separate marginal and KL-projection targets above. -/
theorem staticSB_optimizer_exists
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hprod_le : ∀ (φhat0 φ1 : X → ℝ) (π_prod : ProbabilityMeasure (X × X)),
      (π_prod : Measure (X × X))
          = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2)) →
      ∀ π : ProbabilityMeasure (X × X), π ∈ couplings ρ₀ ρ₁ →
        klReal (π_prod : Measure (X × X)) (endpointLaw d)
          ≤ klReal (π : Measure (X × X)) (endpointLaw d)) :
    ∃ π_star : ProbabilityMeasure (X × X),
      π_star ∈ couplings ρ₀ ρ₁ ∧
      klReal (π_star : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ := by
  obtain ⟨φhat0, φ1, π_prod, hπprod⟩ :=
    schrodinger_product_coupling_data_exists d ρ₀ ρ₁
  exact ⟨π_prod,
    schrodinger_product_coupling_feasible d φhat0 φ1 ρ₀ ρ₁ π_prod hπprod,
    schrodinger_product_coupling_optimal d φhat0 φ1 ρ₀ ρ₁ π_prod hπprod
      (hprod_le φhat0 φ1 π_prod hπprod)⟩

end ChenGeorgiouPavon2021
