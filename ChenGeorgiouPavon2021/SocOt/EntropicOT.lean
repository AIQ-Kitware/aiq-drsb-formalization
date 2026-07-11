/-
# CGP entropic optimal-transport wrappers

This module contains quadratic transport cost, entropic-OT value, the static
SB-to-entropic-OT wrapper, and product-form optimal-coupling assembly.
-/

import ChenGeorgiouPavon2021.SocOt.Static

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (d : SBData X)

/-- Quadratic transport cost `∫∫ ½‖x−y‖² dπ` of a coupling (CGP (4.9)–(4.10)). -/
noncomputable def transportCostHalfSq (π : ProbabilityMeasure (X × X)) : ℝ :=
  ∫ z, (1 / 2 : ℝ) * ‖z.1 - z.2‖ ^ 2 ∂(π : Measure (X × X))

/-- **Entropic regularization of OMT (CGP (4.10)).**  The Schrödinger bridge is an
entropic regularization of quadratic OMT: the objective is
`∫∫ ½‖x−y‖² dπ + ε ∫∫ π log π`.

Abstracted: `negEntropy π = ∫∫ π(x,y) log π(x,y) dx dy` is carried abstractly (it
requires the coupling density). As `ε → 0` this reduces to the Kantorovich cost. -/
noncomputable def entropicRegOMTObjective (ε : ℝ)
    (negEntropy : ProbabilityMeasure (X × X) → ℝ) (π : ProbabilityMeasure (X × X)) : ℝ :=
  transportCostHalfSq π + ε * negEntropy π

/-- **Entropic-OT value = static SB against the Gibbs kernel (CGP §7, (7.13)).**
`min { D(π‖π_B) : π ∈ Π(ρ₀,ρ₁) }` with `π_B ∝ exp(−c/ε)` the Boltzmann/Gibbs kernel
(CGP (7.10),(7.14)). -/
noncomputable def entropicOTValue (πB : ProbabilityMeasure (X × X))
    (ρ₀ ρ₁ : ProbabilityMeasure X) : ℝ :=
  sInf { J : ℝ | ∃ π : ProbabilityMeasure (X × X),
    π ∈ couplings ρ₀ ρ₁ ∧ J = klReal (π : Measure (X × X)) (πB : Measure (X × X)) }

omit [NormedSpace ℝ X] in
/-- **Static SB = entropic OT (CGP §I.3 / §7, (4.9)–(4.10), (7.13)).**  When the
reference endpoint law is the Gibbs kernel `ρ₀₁^W = π_B ∝ exp(−c/ε)`, the static
Schrödinger problem (4.7) coincides with the entropic-OT / Sinkhorn problem (7.13). -/
theorem staticSB_eq_entropicOT (πB : ProbabilityMeasure (X × X))
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hgibbs : (πB : Measure (X × X)) = endpointLaw d) :
    staticSBValue d ρ₀ ρ₁ = entropicOTValue πB ρ₀ ρ₁ := by
  -- Both values are `sInf` over the SAME coupling set of `klReal π (·)`; with the
  -- Gibbs-kernel identification `πB = R₀₁` the two reference measures coincide, so the
  -- objective — hence the whole infimum — is identical. (Content-free once the endpoint
  -- law IS the entropic-OT reference; the mathematics is (7.13)'s setup, not this rewrite.)
  simp only [staticSBValue, entropicOTValue, hgibbs]

omit [NormedSpace ℝ X] in
/-- **Product-form (Schrödinger factorization) of the optimal coupling (CGP (4.11);
static form (7.17)).**  The optimal coupling density factors as
`ρ*₀₁(x,y) = φ̂(x)·p(0,x,1,y)·φ(y)`, with `(φ̂,φ)` solving the Schrödinger system.

`φhat0`, `φ1` are the Schrödinger potentials. The reference transition density `p` is the
density of the reference endpoint law `R₀₁ = endpointLaw` w.r.t. Lebesgue, so *relative to
`R₀₁`* the optimal coupling's density is just the potential product `φ̂(x)·φ(y)` — the form used
here (`dπ*/dR₀₁ = φ̂(x)·φ(y)`, i.e. `π* = R₀₁.withDensity (φ̂(x)·φ(y))`); multiplying by
`dR₀₁/dLeb = p` recovers the printed `φ̂·p·φ` form.

The factorization is expressed as an equality of measures, so the density is interpreted in the
usual almost-everywhere sense.  The hypotheses separate the Schrödinger-system construction from
this uniqueness wrapper: `hπprod` gives the product-density measure, `hprodfeas` and `hprodopt`
verify that it is an optimal coupling, and `huniq` identifies it with `π_star`. -/
theorem optimal_coupling_factorization
    (φhat0 φ1 : X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X) (π_star π_prod : ProbabilityMeasure (X × X))
    -- π_star is the static Schrödinger optimizer (Problem 4.2):
    (hfeas : π_star ∈ couplings ρ₀ ρ₁)
    (hopt : klReal (π_star : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁)
    -- π_prod is the Schrödinger product-form coupling: `dπ_prod/dR₀₁ = φ̂(x)·φ(y)` (CGP (4.11)):
    (hπprod : (π_prod : Measure (X × X))
        = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2)))
    -- verification: the product-form coupling is feasible and optimal (the SDE/OT content):
    (hprodfeas : π_prod ∈ couplings ρ₀ ρ₁)
    (hprodopt : klReal (π_prod : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁)
    -- uniqueness of the KL-projection optimizer (strict convexity of KL over the coupling set):
    (huniq : ∀ π π' : ProbabilityMeasure (X × X),
        π ∈ couplings ρ₀ ρ₁ →
        klReal (π : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ →
        π' ∈ couplings ρ₀ ρ₁ →
        klReal (π' : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ →
        π = π') :
    (π_star : Measure (X × X))
      = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2)) := by
  rw [huniq π_star π_prod hfeas hopt hprodfeas hprodopt]
  exact hπprod

--------------------------------------------------------------------------------

end ChenGeorgiouPavon2021
