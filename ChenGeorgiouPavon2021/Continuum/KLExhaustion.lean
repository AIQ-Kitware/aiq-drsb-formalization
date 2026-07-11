/-
# Continuum frontier: dyadic generation and KL exhaustion

This module contains the generation bound for the ambient `RealPath` function space and the
assembly wrapper around the explicit `HasDyadicKLExhaustion` interface.

Dyadic normalized increments over `[0,1]` do not generate the full product measurable space on
`RealPath := ℝ → ℝ`.  The continuum roadmap (`PLAN_CONTINUUM_CLOSURE.md`) therefore places the full
generation theorem on the canonical anchored continuous interval carrier.  At the ambient-function
level this module proves the one-sided measurability bound
`dyadicNormalizedIncrementMap_iSup_comap_le_standardWienerRealPathMeasure`.
-/

import ChenGeorgiouPavon2021.Continuum.WienerDyadic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- The dyadic normalized-increment maps are measurable as maps out of the current `RealPath`
measurable space.

Dyadic increments over `[0,1]` do not determine arbitrary real-time paths or an absolute anchor on
the ambient `RealPath` carrier.  The theorem therefore states the one-sided generation bound; the
full KL-exhaustion result is expressed separately by
`klDiv_tendsto_of_dyadicNormalizedIncrementMap_generates`.
-/
theorem dyadicNormalizedIncrementMap_iSup_comap_le_standardWienerRealPathMeasure
    (_W : ProbabilityMeasure RealPath)
    (_hWmeasure : ((_W : ProbabilityMeasure RealPath) : Measure RealPath) = standardWienerRealPathMeasure) :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
      ≤ (inferInstance : MeasurableSpace RealPath) := by
  refine iSup_le ?_
  intro level
  exact (measurable_normalizedDyadicIncrementMap level).comap_le

/-- KL data processing along dyadic normalized-increment projections converges to full path KL,
provided by the explicit `HasDyadicKLExhaustion` interface.

The one-sided measurability bound is insufficient on `RealPath := ℝ → ℝ`.  This theorem therefore
assembles the conclusion from the KL-exhaustion interface.  A concrete continuous-path
instantiation requires the corresponding generating-filtration theorem. -/
theorem klDiv_tendsto_of_dyadicNormalizedIncrementMap_generates
    (W : ProbabilityMeasure RealPath)
    (_hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedDyadicIncrementMap level)
            ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
          (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath))) := by
  exact hKL.normalized_dyadic_kl_tendsto h hac

/-- Packaging lemma for an explicitly supplied dyadic KL-exhaustion interface.

The measure identity alone does not imply KL exhaustion; the path-space filtration/exhaustion
theorem is represented by the explicit hypothesis `hKL`. -/
theorem hasDyadicKLExhaustion_standardWienerRealPathMeasure
    (W : ProbabilityMeasure RealPath)
    (_hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W) :
    HasDyadicKLExhaustion W := by
  exact hKL


/-- General KL-exhaustion theorem from an explicitly generated dyadic filtration.

This is the reusable information-theory capstone needed by the interval Wiener wrapper.  Generation
alone is not enough as a bare proposition: the KL martingale theorem also needs the dyadic
sub-σ-algebras packaged as a filtration and identified with the normalized-increment projections.
With those structural data, the result follows from the Mathlib-style KL martingale convergence
theorem `ForMathlib.MeasureTheory.klDiv_map_tendsto`. -/
theorem hasIntervalDyadicKLExhaustion_of_dyadicGeneration
    (W : ProbabilityMeasure IntervalPath)
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace IntervalPath))
    (hℱ : ∀ level : ℕ,
      ℱ level = MeasurableSpace.comap (normalizedIntervalDyadicIncrementMap level)
        (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
    (hgen : ⨆ level : ℕ, ℱ level = (inferInstance : MeasurableSpace IntervalPath)) :
    HasIntervalDyadicKLExhaustion W := by
  constructor
  intro h hac
  have hshift : Measurable (fun ω : IntervalPath => ω + h) := by
    fun_prop
  haveI : IsProbabilityMeasure
      ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h)) :=
    Measure.isProbabilityMeasure_map hshift.aemeasurable
  exact ForMathlib.MeasureTheory.klDiv_map_tendsto
    ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
    (W : Measure IntervalPath) hac
    (fun level : ℕ => normalizedIntervalDyadicIncrementMap level)
    (fun level : ℕ => measurable_normalizedIntervalDyadicIncrementMap level)
    ℱ hℱ hgen

end ChenGeorgiouPavon2021
