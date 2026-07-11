import ChenGeorgiouPavon2021.Continuum.RealPath

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-! ### Interval-path carrier for the M4 continuum frontier

The ambient `RealPath := ℝ → ℝ` carrier is useful for compatibility with the CGP
wrappers, but it is too broad for a theorem saying that dyadic increments on `[0,1]` generate all
path information.  The declarations in this block introduce a narrow interval-path interface for the
next continuum proof step.  They intentionally prove only finite-projection facts and leave full
path-space generation/KL exhaustion and Cameron--Martin quasi-invariance as explicit interfaces.
-/

/-- The closed unit interval `[0,1]`, as a subtype used for canonical interval paths. -/
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1

/-- The left endpoint of the interval carrier. -/
def unitIntervalZero : UnitInterval :=
  ⟨0, by constructor <;> norm_num⟩

/-- The right endpoint of the interval carrier. -/
def unitIntervalOne : UnitInterval :=
  ⟨1, by constructor <;> norm_num⟩

/-- Clamp a real time to the closed unit interval.

Using a clamped representative lets the low-level projection maps be total without adding proof
obligations at every dyadic endpoint.  The analytic generation theorem below is still an explicit
interface, not a theorem about this lightweight carrier. -/
noncomputable def clampUnitInterval (t : ℝ) : UnitInterval :=
  ⟨max 0 (min 1 t), by
    constructor
    · exact le_max_left 0 (min 1 t)
    · exact max_le (by norm_num) (min_le_left 1 t)⟩

@[simp] theorem coe_clampUnitInterval (t : ℝ) :
    ((clampUnitInterval t : UnitInterval) : ℝ) = max 0 (min 1 t) := rfl

/-- Canonical scalar paths on `[0,1]` for the future continuum theorem carrier.

This is deliberately not identified with `RealPath`; interval dyadic increments should generate this
carrier, not arbitrary real-time coordinates.  Anchoring and continuity/Sobolev regularity are kept as
separate predicates/interfaces so downstream wrappers can distinguish proved finite-grid facts from
continuum assumptions. -/
abbrev IntervalPath : Type := UnitInterval → ℝ

/-- Anchoring predicate for interval paths, matching Brownian/Cameron--Martin convention `h(0)=0`. -/
def IntervalPathAnchored (ω : IntervalPath) : Prop :=
  ω unitIntervalZero = 0

/-- Dyadic time on the interval carrier. -/
noncomputable def intervalDyadicTime (level i : ℕ) : UnitInterval :=
  clampUnitInterval (dyadicTime level i)

/-- Raw dyadic increment of an interval path. -/
noncomputable def intervalDyadicIncrement (level : ℕ) (ω : IntervalPath)
    (i : Fin (2 ^ level)) : ℝ :=
  ω (intervalDyadicTime level (i.1 + 1)) - ω (intervalDyadicTime level i.1)

/-- Vector of raw dyadic increments for interval paths. -/
noncomputable def intervalDyadicIncrementMap (level : ℕ) :
    IntervalPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => intervalDyadicIncrement level ω i

/-- Normalized dyadic increment on the interval carrier. -/
noncomputable def normalizedIntervalDyadicIncrement (level : ℕ) (ω : IntervalPath)
    (i : Fin (2 ^ level)) : ℝ :=
  intervalDyadicIncrement level ω i / Real.sqrt (dyadicMesh level)

/-- Vector of normalized dyadic increments for interval paths. -/
noncomputable def normalizedIntervalDyadicIncrementMap (level : ℕ) :
    IntervalPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => normalizedIntervalDyadicIncrement level ω i

/-- Finite dyadic Cameron--Martin energy on the interval carrier. -/
noncomputable def intervalDyadicPathEnergy (level : ℕ) (h : IntervalPath) : ℝ :=
  2⁻¹ * ∑ i : Fin (2 ^ level), normalizedIntervalDyadicIncrementMap level h i ^ 2

/-- Interval Cameron--Martin interface.

This is the interval-carrier analogue of `IsCameronMartinPath`.  It includes the Brownian anchor and
keeps the Sobolev-to-dyadic-energy theorem as an explicit field until the repository chooses a real
AC/Sobolev path API. -/
structure IsIntervalCameronMartinPath (h : IntervalPath) (hderiv : ℝ → ℝ) : Prop where
  anchored : IntervalPathAnchored h
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  dyadic_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => intervalDyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))

/-- Standard-Wiener finite-dimensional interface on the corrected interval carrier. -/
structure IsStandardIntervalWiener (W : ProbabilityMeasure IntervalPath) : Prop where
  normalized_dyadic_law : ∀ level : ℕ,
    Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- Path-space dyadic KL exhaustion on the corrected interval carrier.

This is intentionally an interface: it should be proved later from a genuine generating-filtration
result for the chosen interval path measurable space, not inferred from the ambient `RealPath`
interface. -/
structure HasIntervalDyadicKLExhaustion (W : ProbabilityMeasure IntervalPath) : Prop where
  normalized_dyadic_kl_tendsto : ∀ (h : IntervalPath),
    (W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h) ≪ (W : Measure IntervalPath) →
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedIntervalDyadicIncrementMap level)
            ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h)))
          (Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath)))

/-- Generation interface for interval dyadic normalized increments.

Unlike the intentionally weakened `RealPath` one-sided lemma, this is the *right shape* of the future
carrier theorem: the dyadic projection filtration should generate the chosen interval path
measurable space for the selected Brownian/continuous/anchored carrier.  The target measurable space
is an explicit parameter so this declaration does not falsely claim that dyadic increments generate
the default product sigma-algebra on all functions `[0,1] → ℝ`. -/
structure HasIntervalDyadicGeneration (𝓜 : MeasurableSpace IntervalPath) : Prop where
  normalized_dyadic_iSup_comap_eq :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedIntervalDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ))) = 𝓜

/-- The interval normalized-increment maps are measurable. -/
theorem measurable_normalizedIntervalDyadicIncrementMap (level : ℕ) :
    Measurable (normalizedIntervalDyadicIncrementMap level) := by
  unfold normalizedIntervalDyadicIncrementMap normalizedIntervalDyadicIncrement intervalDyadicIncrement
  fun_prop

/-- The sigma-algebra generated by interval dyadic projections is bounded above by the interval path
measurable space.  The reverse inclusion is the explicit `HasIntervalDyadicGeneration` interface. -/
theorem normalizedIntervalDyadicIncrementMap_iSup_comap_le :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedIntervalDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
      ≤ (inferInstance : MeasurableSpace IntervalPath) := by
  refine iSup_le ?_
  intro level
  exact (measurable_normalizedIntervalDyadicIncrementMap level).comap_le

/-- Interval normalized dyadic increments commute with deterministic path addition. -/
theorem normalizedIntervalDyadicIncrementMap_add (level : ℕ) (ω h : IntervalPath) :
    normalizedIntervalDyadicIncrementMap level (ω + h)
      = normalizedIntervalDyadicIncrementMap level ω + normalizedIntervalDyadicIncrementMap level h := by
  funext i
  unfold normalizedIntervalDyadicIncrementMap normalizedIntervalDyadicIncrement intervalDyadicIncrement
  simp [Pi.add_apply]
  ring

/-- Interval finite-dimensional Wiener projection law wrapper. -/
theorem normalizedIntervalDyadicIncrementMap_wiener_law
    (W : ProbabilityMeasure IntervalPath) (hW : IsStandardIntervalWiener W) (level : ℕ) :
    Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  exact hW.normalized_dyadic_law level

/-- Shifted interval Wiener projection law: finite-dimensional dyadic increments are translated by the
increment vector of the deterministic shift. -/
theorem normalizedIntervalDyadicIncrementMap_shifted_wiener_law
    (W : ProbabilityMeasure IntervalPath) (hW : IsStandardIntervalWiener W)
    (level : ℕ) (h : IntervalPath) :
    Measure.map (normalizedIntervalDyadicIncrementMap level)
        ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
      = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedIntervalDyadicIncrementMap level h) := by
  let N : IntervalPath → (Fin (2 ^ level) → ℝ) := normalizedIntervalDyadicIncrementMap level
  let v : Fin (2 ^ level) → ℝ := normalizedIntervalDyadicIncrementMap level h
  have hN : Measurable N := measurable_normalizedIntervalDyadicIncrementMap level
  have hshift : Measurable (fun ω : IntervalPath => ω + h) := by fun_prop
  have hshiftFin : Measurable (fun x : Fin (2 ^ level) → ℝ => x + v) := by fun_prop
  have hcomp : N ∘ (fun ω : IntervalPath => ω + h) =
      (fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N := by
    funext ω
    exact normalizedIntervalDyadicIncrementMap_add level ω h
  calc
    Measure.map N ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        = (W : Measure IntervalPath).map (N ∘ (fun ω : IntervalPath => ω + h)) := by
            rw [Measure.map_map hN hshift]
    _ = (W : Measure IntervalPath).map ((fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N) := by
            rw [hcomp]
    _ = ((W : Measure IntervalPath).map N).map (fun x : Fin (2 ^ level) → ℝ => x + v) := by
            rw [Measure.map_map hshiftFin hN]
    _ = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedIntervalDyadicIncrementMap level h) := by
            change ((W : Measure IntervalPath).map (normalizedIntervalDyadicIncrementMap level)).map
                (fun x : Fin (2 ^ level) → ℝ => x + normalizedIntervalDyadicIncrementMap level h) = _
            rw [normalizedIntervalDyadicIncrementMap_wiener_law W hW level]

/-- Finite-dimensional interval Cameron--Martin KL identity on each dyadic projection. -/
theorem klDiv_normalizedIntervalDyadicIncrement_shifted_wiener
    (W : ProbabilityMeasure IntervalPath) (hW : IsStandardIntervalWiener W)
    (level : ℕ) (h : IntervalPath) :
    InformationTheory.klDiv
        (Measure.map (normalizedIntervalDyadicIncrementMap level)
          ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h)))
        (Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath))
      = ENNReal.ofReal (intervalDyadicPathEnergy level h) := by
  rw [normalizedIntervalDyadicIncrementMap_shifted_wiener_law W hW level h,
    normalizedIntervalDyadicIncrementMap_wiener_law W hW level]
  simpa [intervalDyadicPathEnergy] using
    (ForMathlib.MeasureTheory.klDiv_stdGaussian_map_add
      (normalizedIntervalDyadicIncrementMap level h))

/-- Interval dyadic finite-grid energies converge to continuum Cameron--Martin energy under the
explicit interval Cameron--Martin interface. -/
theorem intervalDyadicPathEnergy_tendsto_cameronMartinPathEnergy
    (h : IntervalPath) (hderiv : ℝ → ℝ) (hCM : IsIntervalCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => intervalDyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  exact hCM.dyadic_energy_tendsto

/-- Interval path-space KL exhaustion, exposed as an explicit interface. -/
theorem klDiv_normalizedIntervalDyadicIncrement_tendsto_path_kl
    (W : ProbabilityMeasure IntervalPath) (h : IntervalPath)
    (hKL : HasIntervalDyadicKLExhaustion W)
    (hac : (W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h) ≪
        (W : Measure IntervalPath)) :
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedIntervalDyadicIncrementMap level)
            ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h)))
          (Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath))) := by
  exact hKL.normalized_dyadic_kl_tendsto h hac


end ChenGeorgiouPavon2021
