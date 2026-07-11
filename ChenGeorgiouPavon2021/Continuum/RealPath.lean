import ChenGeorgiouPavon2021.SequenceGaussian

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

--------------------------------------------------------------------------------
-- §3.M4  Continuum Cameron--Martin / Wiener path-law interface
--------------------------------------------------------------------------------

/-- Real-valued path space used by the M4 Wiener transport interface.  The existing
`Path X` abstraction is intentionally broad; M4 specializes to the scalar Wiener
case so the dyadic increment maps can be stated concretely. -/
abbrev RealPath : Type := Path ℝ

/-- Dyadic mesh size `2⁻ⁿ` for level `n`. -/
noncomputable def dyadicMesh (level : ℕ) : ℝ := ((2 : ℝ) ^ level)⁻¹

/-- Dyadic mesh size as a nonnegative real, for APIs such as `gaussianReal` whose
variance parameter is `NNReal`. -/
noncomputable def dyadicMeshNNReal (level : ℕ) : NNReal :=
  ⟨dyadicMesh level, by
    unfold dyadicMesh
    positivity⟩

@[simp] lemma coe_dyadicMeshNNReal (level : ℕ) :
    (dyadicMeshNNReal level : ℝ) = dyadicMesh level := rfl

/-- Dyadic time `i / 2ⁿ` at level `n`.  The declarations below use the finite
range `i : Fin (2^n)` for increments, so the right endpoint is `i + 1`. -/
noncomputable def dyadicTime (level i : ℕ) : ℝ := (i : ℝ) / ((2 : ℝ) ^ level)

/-- Raw dyadic increment of a real path over interval `[i/2ⁿ, (i+1)/2ⁿ]`. -/
noncomputable def dyadicIncrement (level : ℕ) (ω : RealPath) (i : Fin (2 ^ level)) : ℝ :=
  ω (dyadicTime level (i.1 + 1)) - ω (dyadicTime level i.1)

/-- Vector of raw dyadic increments at level `n`. -/
noncomputable def dyadicIncrementMap (level : ℕ) : RealPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => dyadicIncrement level ω i

/-- Normalized dyadic increment.  Under standard Wiener measure this should be a
standard normal coordinate: `(W_{t+Δt}-W_t)/sqrt(Δt)`. -/
noncomputable def normalizedDyadicIncrement (level : ℕ) (ω : RealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  dyadicIncrement level ω i / Real.sqrt (dyadicMesh level)

/-- Vector of normalized dyadic increments at level `n`. -/
noncomputable def normalizedDyadicIncrementMap (level : ℕ) :
    RealPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => normalizedDyadicIncrement level ω i

/-- Finite dyadic Cameron--Martin energy of a deterministic shift path: the
finite-dimensional Gaussian cost of its normalized increment vector. -/
noncomputable def dyadicPathEnergy (level : ℕ) (h : RealPath) : ℝ :=
  2⁻¹ * ∑ i : Fin (2 ^ level), normalizedDyadicIncrementMap level h i ^ 2

/-- Continuum Cameron--Martin energy `½ ∫₀¹ |h'(t)|² dt`. -/
noncomputable def cameronMartinPathEnergy (hderiv : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1, 2⁻¹ * hderiv t ^ 2 ∂volume

/-- Path-level Cameron--Martin interface for M4.

The first field records the usual square-integrability of the derivative.  The
second field records the continuum-limit theorem needed by the dyadic interface:
the finite dyadic Cameron--Martin energies converge to the continuum energy.
Future work should replace this interface field by a proof from the chosen
Sobolev/absolutely-continuous path representation. -/
structure IsCameronMartinPath (h : RealPath) (hderiv : ℝ → ℝ) : Prop where
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  dyadic_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))

/-- Abstract standard-Wiener interface needed for M4.

The first field says that each normalized dyadic increment vector has the
canonical finite-dimensional standard Gaussian law.  The second field records
the projection/exhaustion KL convergence needed to pass from dyadic finite-grid
KLs to the full path-law KL.  Future work should discharge both fields from
Mathlib Brownian motion / Wiener measure APIs and the path-law filtration
exhaustion theorem, rather than assume them. -/
structure IsStandardWiener (W : ProbabilityMeasure RealPath) : Prop where
  normalized_dyadic_law : ∀ level : ℕ,
    Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- Dyadic normalized-increment KL exhaustion for a path-space law.

This is kept as a separate interface from `IsStandardWiener`: the latter is the
finite-dimensional Wiener law, while this field is the path-space filtration/exhaustion theorem
needed to pass finite-grid KLs to full path-law KL. -/
structure HasDyadicKLExhaustion (W : ProbabilityMeasure RealPath) : Prop where
  normalized_dyadic_kl_tendsto : ∀ (h : RealPath),
    (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath) →
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedDyadicIncrementMap level)
            ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
          (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)))

end ChenGeorgiouPavon2021
