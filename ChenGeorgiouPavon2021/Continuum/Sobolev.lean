/-
# Continuum frontier: Sobolev to dyadic Cameron--Martin energy

This module contains the ordinary Sobolev/Cameron--Martin path interface and
the wrapper into the dyadic `IsCameronMartinPath` interface.
-/

import ChenGeorgiouPavon2021.Continuum.WienerDyadic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- A concrete Sobolev/Cameron--Martin path interface, deliberately separate from
`IsCameronMartinPath`.

The fields name the usual mathematical ingredients without baking the dyadic-energy
limit into the definition.  The theorem `isCameronMartinPath_of_sobolevCameronMartinPath`
below is the remaining analysis capstone: prove that these ordinary hypotheses imply the
dyadic energy convergence required by the M4 interface. -/
structure IsSobolevCameronMartinPath (h : RealPath) (hderiv : ℝ → ℝ) : Prop where
  /-- Provisional field for the ordinary absolute-continuity hypothesis on `h`.
  A concrete AC-path API should replace the current lightweight proposition. -/
  absolutely_continuous_path : True
  /-- Provisional field saying `hderiv` represents the a.e. derivative of `h`.
  It is separated from square integrability so a concrete derivative relation can replace `True`. -/
  derivative_represents_path : True
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  /-- Dyadic finite-difference energies converge to the continuum Cameron--Martin energy.
  This is the explicit analysis obligation that a future concrete AC/Sobolev API should
  prove from the ordinary path hypotheses above. -/
  dyadic_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))

/-- Sobolev/AC Cameron--Martin paths realize the dyadic-energy interface.

This is the real path-analysis capstone behind `IsCameronMartinPath`: show that if `h`
is absolutely continuous with square-integrable derivative `hderiv`, then the dyadic finite
energies converge to `1/2 ∫ hderiv^2`. -/
theorem isCameronMartinPath_of_sobolevCameronMartinPath
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hSob : IsSobolevCameronMartinPath h hderiv) :
    IsCameronMartinPath h hderiv := by
  exact ⟨hSob.square_integrable, hSob.dyadic_energy_tendsto⟩


/-- Dyadic finite-difference quotient on the ambient real-time carrier.

This is the unnormalized slope `(h(t_{i+1}) - h(t_i)) / (t_{i+1} - t_i)`, written against
the repository's existing `dyadicMesh` and `dyadicIncrement` primitives. -/
noncomputable def dyadicDifferenceQuotient (level : ℕ) (h : RealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  dyadicIncrement level h i / dyadicMesh level

/-- Pure Riemann-sum expression for the dyadic Cameron--Martin energy.

This is intentionally separated from `dyadicPathEnergy`: that definition is phrased as the
finite-dimensional Gaussian cost of normalized increments, whereas this expression is the usual
`∑ ½ |difference quotient|² Δt` Sobolev energy sum. -/
noncomputable def dyadicDifferenceQuotientRiemannEnergy (level : ℕ) (h : RealPath) : ℝ :=
  ∑ i : Fin (2 ^ level),
    dyadicMesh level * (2⁻¹ * dyadicDifferenceQuotient level h i ^ 2)

/-- Left-endpoint Riemann sums for the derivative-square Cameron--Martin energy. -/
noncomputable def dyadicDerivativeSquareRiemannEnergy (level : ℕ)
    (hderiv : ℝ → ℝ) : ℝ :=
  ∑ i : Fin (2 ^ level),
    dyadicMesh level * (2⁻¹ * hderiv (dyadicTime level i.1) ^ 2)

/-- Analytic Cameron--Martin path predicate on the ambient real-time carrier.

This is stronger and more concrete than the lightweight dyadic `IsCameronMartinPath` interface:
`h` is anchored at zero, reconstructed on `[0,1]` as the integral of its derivative, and the
derivative is square-integrable.  The additional fields expose the analytic Riemann-sum and
finite-difference regularity seams needed to assemble dyadic energy convergence without making
the final `dyadicPathEnergy` conclusion a hypothesis. -/
structure IsAnalyticCameronMartinPath (h : RealPath) (hderiv : ℝ → ℝ) : Prop where
  anchored : h 0 = 0
  interval_reconstruction : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    h t = ∫ s in Set.Ioc (0 : ℝ) t, hderiv s ∂volume
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  /-- Explicit regularity seam: dyadic finite-difference quotients approximate the derivative in
  the mesh-weighted squared-error norm. -/
  difference_quotient_l2_tendsto_derivative :
    Filter.Tendsto
      (fun level : ℕ =>
        ∑ i : Fin (2 ^ level),
          dyadicMesh level *
            ((dyadicDifferenceQuotient level h i - hderiv (dyadicTime level i.1)) ^ 2))
      Filter.atTop (nhds (0 : ℝ))
  /-- Explicit regularity seam: left-endpoint Riemann sums of the derivative-square energy
  converge to the continuum Cameron--Martin energy. -/
  derivative_square_riemann_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => dyadicDerivativeSquareRiemannEnergy level hderiv)
      Filter.atTop (nhds (cameronMartinPathEnergy hderiv))
  /-- Explicit regularity seam: finite-difference energy and derivative-square Riemann energy
  have asymptotically zero difference. -/
  difference_quotient_energy_sub_derivative_square_tendsto_zero :
    Filter.Tendsto
      (fun level : ℕ =>
        dyadicDifferenceQuotientRiemannEnergy level h
          - dyadicDerivativeSquareRiemannEnergy level hderiv)
      Filter.atTop (nhds (0 : ℝ))

/-- Dyadic mesh sizes are strictly positive. -/
lemma dyadicMesh_pos (level : ℕ) : 0 < dyadicMesh level := by
  unfold dyadicMesh
  positivity

/-- Dyadic mesh sizes are nonzero. -/
lemma dyadicMesh_ne_zero (level : ℕ) : dyadicMesh level ≠ 0 :=
  ne_of_gt (dyadicMesh_pos level)

/-- The dyadic mesh tends to zero.

This is the generic mesh-control fact needed before the analytic finite-difference and Riemann-sum
arguments can be connected to the dyadic interface. -/
theorem dyadicMesh_tendsto_zero :
    Filter.Tendsto dyadicMesh Filter.atTop (nhds (0 : ℝ)) := by
  unfold dyadicMesh
  have htwo : (1 : ℝ) < 2 := by norm_num
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt htwo)

/-- Analytic seam: dyadic finite-difference quotients approximate the derivative in squared
left-endpoint Riemann-sum norm.

For a future concrete AC/Sobolev API this should follow from absolute continuity plus the chosen
regular representative of the derivative.  It is deliberately not the final energy statement: it only
records the local slope-to-derivative approximation. -/
theorem dyadicDifferenceQuotient_l2_tendsto_derivative_of_analyticCameronMartinPath
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticCameronMartinPath h hderiv) :
    Filter.Tendsto
      (fun level : ℕ =>
        ∑ i : Fin (2 ^ level),
          dyadicMesh level *
            ((dyadicDifferenceQuotient level h i - hderiv (dyadicTime level i.1)) ^ 2))
      Filter.atTop (nhds (0 : ℝ)) := by
  exact hA.difference_quotient_l2_tendsto_derivative

/-- Analytic seam: derivative-square dyadic Riemann sums converge to the continuum
Cameron--Martin energy.

This is the ordinary Riemann/Lebesgue-sum convergence side of the Sobolev capstone, independent of
the path finite differences. -/
theorem dyadicDerivativeSquareRiemannEnergy_tendsto_cameronMartinPathEnergy
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => dyadicDerivativeSquareRiemannEnergy level hderiv)
      Filter.atTop (nhds (cameronMartinPathEnergy hderiv)) := by
  exact hA.derivative_square_riemann_energy_tendsto

/-- Analytic seam: the pure difference-quotient energy has the same asymptotic value as the
derivative-square Riemann-sum energy.

This is the quantitative energy-comparison form of the finite-difference approximation.  It is weaker
than a full pointwise derivative theorem and exactly strong enough to combine with the derivative-square
Riemann-sum convergence seam below. -/
theorem dyadicDifferenceQuotientRiemannEnergy_sub_derivativeSquareRiemannEnergy_tendsto_zero
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticCameronMartinPath h hderiv) :
    Filter.Tendsto
      (fun level : ℕ =>
        dyadicDifferenceQuotientRiemannEnergy level h
          - dyadicDerivativeSquareRiemannEnergy level hderiv)
      Filter.atTop (nhds (0 : ℝ)) := by
  exact hA.difference_quotient_energy_sub_derivative_square_tendsto_zero

/-- Squared dyadic difference-quotient energies converge to the continuum
Cameron--Martin energy.

Mathematically this only assembles two analytic seams: energy comparison against the
derivative-square dyadic Riemann sums, and convergence of those Riemann sums to the continuum energy.
It is the pure Sobolev/Riemann-sum target before translating back to the repository's
normalized-increment Gaussian-cost definition. -/
theorem dyadicDifferenceQuotientRiemannEnergy_tendsto_cameronMartinPathEnergy
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => dyadicDifferenceQuotientRiemannEnergy level h)
      Filter.atTop (nhds (cameronMartinPathEnergy hderiv)) := by
  have hclose :=
    dyadicDifferenceQuotientRiemannEnergy_sub_derivativeSquareRiemannEnergy_tendsto_zero
      h hderiv hA
  have hderivEnergy :=
    dyadicDerivativeSquareRiemannEnergy_tendsto_cameronMartinPathEnergy h hderiv hA
  simpa [sub_add_cancel] using hclose.add hderivEnergy

/-- Squaring the normalized dyadic increment converts the Gaussian normalization into
the mesh-weighted squared finite-difference quotient. -/
lemma normalizedDyadicIncrement_sq_eq_mesh_mul_differenceQuotient_sq
    (level : ℕ) (h : RealPath) (i : Fin (2 ^ level)) :
    normalizedDyadicIncrementMap level h i ^ 2
      = dyadicMesh level * dyadicDifferenceQuotient level h i ^ 2 := by
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicDifferenceQuotient
  have hmesh_nonneg : 0 ≤ dyadicMesh level := le_of_lt (dyadicMesh_pos level)
  have hmesh_ne : dyadicMesh level ≠ 0 := dyadicMesh_ne_zero level
  rw [div_pow, Real.sq_sqrt hmesh_nonneg]
  field_simp [hmesh_ne]

/-- The CGP normalized-increment dyadic energy is the pure finite-difference Riemann-sum energy.

This is a finite algebra bridge using positivity of the dyadic mesh and `Real.sq_sqrt`; it contains no
continuum analysis. -/
theorem dyadicPathEnergy_eq_dyadicDifferenceQuotientRiemannEnergy
    (level : ℕ) (h : RealPath) :
    dyadicPathEnergy level h = dyadicDifferenceQuotientRiemannEnergy level h := by
  unfold dyadicPathEnergy dyadicDifferenceQuotientRiemannEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [normalizedDyadicIncrement_sq_eq_mesh_mul_differenceQuotient_sq]
  ring

/-- Sobolev/Riemann-sum capstone on the ambient carrier.

This is the real-analysis theorem target behind the ambient `IsCameronMartinPath` wrapper: finite
dyadic difference energies for an analytically defined Cameron--Martin path converge to
`½ ∫₀¹ |h'|²`.  The proof is reduced to named seams for mesh convergence, finite-difference
approximation, Riemann-sum convergence, and the finite algebra bridge from CGP normalized increments
to pure Sobolev sums. -/
theorem dyadicPathEnergy_tendsto_of_analyticCameronMartinPath
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  simpa [dyadicPathEnergy_eq_dyadicDifferenceQuotientRiemannEnergy] using
    dyadicDifferenceQuotientRiemannEnergy_tendsto_cameronMartinPathEnergy h hderiv hA

/-- Analytically defined Cameron--Martin paths realize the dyadic `IsCameronMartinPath` interface
once the Riemann-sum capstone is available. -/
theorem isCameronMartinPath_of_analyticCameronMartinPath
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticCameronMartinPath h hderiv) :
    IsCameronMartinPath h hderiv := by
  exact ⟨hA.square_integrable,
    dyadicPathEnergy_tendsto_of_analyticCameronMartinPath h hderiv hA⟩

/-- Extend an interval path to the ambient real-time carrier by clamping times to `[0,1]`. -/
noncomputable def extendIntervalPathToRealPath (h : IntervalPath) : RealPath :=
  fun t : ℝ => h (clampUnitInterval t)

/-- Analytic Cameron--Martin path predicate on the corrected interval carrier. -/
structure IsAnalyticIntervalCameronMartinPath (h : IntervalPath) (hderiv : ℝ → ℝ) : Prop where
  anchored : IntervalPathAnchored h
  interval_reconstruction : ∀ t : UnitInterval,
    h t = ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), hderiv s ∂volume
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  /-- Explicit regularity seam for the clamped ambient extension. -/
  difference_quotient_l2_tendsto_derivative_extend :
    Filter.Tendsto
      (fun level : ℕ =>
        ∑ i : Fin (2 ^ level),
          dyadicMesh level *
            ((dyadicDifferenceQuotient level (extendIntervalPathToRealPath h) i
                - hderiv (dyadicTime level i.1)) ^ 2))
      Filter.atTop (nhds (0 : ℝ))
  /-- Explicit derivative-square Riemann-sum convergence seam. -/
  derivative_square_riemann_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => dyadicDerivativeSquareRiemannEnergy level hderiv)
      Filter.atTop (nhds (cameronMartinPathEnergy hderiv))
  /-- Explicit finite-difference versus derivative-square energy comparison seam for the clamped
  ambient extension. -/
  difference_quotient_energy_sub_derivative_square_tendsto_zero_extend :
    Filter.Tendsto
      (fun level : ℕ =>
        dyadicDifferenceQuotientRiemannEnergy level (extendIntervalPathToRealPath h)
          - dyadicDerivativeSquareRiemannEnergy level hderiv)
      Filter.atTop (nhds (0 : ℝ))

/-- Interval and ambient normalized dyadic increments agree after clamped extension. -/
theorem normalizedIntervalDyadicIncrementMap_eq_normalizedDyadicIncrementMap_extend
    (level : ℕ) (h : IntervalPath) :
    normalizedIntervalDyadicIncrementMap level h
      = normalizedDyadicIncrementMap level (extendIntervalPathToRealPath h) := by
  funext i
  unfold normalizedIntervalDyadicIncrementMap normalizedIntervalDyadicIncrement
    intervalDyadicIncrement normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement
    extendIntervalPathToRealPath intervalDyadicTime
  rfl

/-- Interval and ambient dyadic Cameron--Martin energies agree after clamped extension. -/
theorem intervalDyadicPathEnergy_eq_dyadicPathEnergy_extend
    (level : ℕ) (h : IntervalPath) :
    intervalDyadicPathEnergy level h
      = dyadicPathEnergy level (extendIntervalPathToRealPath h) := by
  unfold intervalDyadicPathEnergy dyadicPathEnergy
  rw [normalizedIntervalDyadicIncrementMap_eq_normalizedDyadicIncrementMap_extend]

/-- Analytic interval Cameron--Martin data extend to analytic data on the ambient real-time carrier. -/
theorem isAnalyticCameronMartinPath_extend_of_analyticIntervalCameronMartinPath
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticIntervalCameronMartinPath h hderiv) :
    IsAnalyticCameronMartinPath (extendIntervalPathToRealPath h) hderiv := by
  refine {
    anchored := ?_,
    interval_reconstruction := ?_,
    square_integrable := hA.square_integrable,
    difference_quotient_l2_tendsto_derivative :=
      hA.difference_quotient_l2_tendsto_derivative_extend,
    derivative_square_riemann_energy_tendsto :=
      hA.derivative_square_riemann_energy_tendsto,
    difference_quotient_energy_sub_derivative_square_tendsto_zero :=
      hA.difference_quotient_energy_sub_derivative_square_tendsto_zero_extend
  }
  · unfold extendIntervalPathToRealPath
    rw [show clampUnitInterval (0 : ℝ) = unitIntervalZero by
      apply Subtype.ext
      simp [unitIntervalZero, coe_clampUnitInterval]]
    exact hA.anchored
  · intro t ht
    unfold extendIntervalPathToRealPath
    rw [show clampUnitInterval t = (⟨t, ht⟩ : UnitInterval) by
      apply Subtype.ext
      rw [coe_clampUnitInterval]
      rw [min_eq_right ht.2, max_eq_right ht.1]]
    exact hA.interval_reconstruction ⟨t, ht⟩

/-- Sobolev/Riemann-sum capstone on the corrected interval carrier.

This is the interval-carrier analogue of
`dyadicPathEnergy_tendsto_of_analyticCameronMartinPath`; it is the remaining analytic theorem needed
to package an analytic interval path as an `IsIntervalCameronMartinPath`. -/
theorem intervalDyadicPathEnergy_tendsto_of_analyticIntervalCameronMartinPath
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticIntervalCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => intervalDyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  have hreal := dyadicPathEnergy_tendsto_of_analyticCameronMartinPath
    (extendIntervalPathToRealPath h) hderiv
    (isAnalyticCameronMartinPath_extend_of_analyticIntervalCameronMartinPath h hderiv hA)
  simpa [intervalDyadicPathEnergy_eq_dyadicPathEnergy_extend] using hreal

/-- Analytically defined interval Cameron--Martin paths realize the dyadic interval interface once
the interval Riemann-sum capstone is available. -/
theorem isIntervalCameronMartinPath_of_analyticIntervalCameronMartinPath
    (h : IntervalPath) (hderiv : ℝ → ℝ)
    (hA : IsAnalyticIntervalCameronMartinPath h hderiv) :
    IsIntervalCameronMartinPath h hderiv := by
  exact {
    anchored := hA.anchored
    square_integrable := hA.square_integrable
    dyadic_energy_tendsto :=
      intervalDyadicPathEnergy_tendsto_of_analyticIntervalCameronMartinPath h hderiv hA
  }

end ChenGeorgiouPavon2021
