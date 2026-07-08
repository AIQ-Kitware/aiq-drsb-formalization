import ChenGeorgiouPavon2021.Continuum.IntervalPath

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Nonnegative-time real path space used by the concrete `wienerMeasure` construction.

The CGP-facing M4 scaffold above keeps `RealPath := Path ℝ` so existing endpoint/path-law
statements remain stable.  The vendored Kolmogorov construction of standard Wiener measure,
however, naturally lives on `NNReal → ℝ`.  This parallel nonnegative-time staging namespace is the
place where we discharge the "real Wiener measure satisfies the finite-dimensional standard-normal
increment law" capstone before transporting it back to whatever final CGP path representation is
chosen. -/
abbrev WienerRealPath : Type := NNReal → ℝ

/-- Dyadic time `i / 2ⁿ` as a nonnegative real. -/
noncomputable def dyadicTimeNNReal (level i : ℕ) : NNReal :=
  ⟨(i : ℝ) / ((2 : ℝ) ^ level), by positivity⟩

/-- Raw dyadic increment on the concrete nonnegative-time Wiener path space. -/
noncomputable def wienerDyadicIncrement (level : ℕ) (ω : WienerRealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  ω (dyadicTimeNNReal level (i.1 + 1)) - ω (dyadicTimeNNReal level i.1)

/-- Normalized dyadic increment on `NNReal → ℝ` paths. -/
noncomputable def normalizedWienerDyadicIncrement (level : ℕ) (ω : WienerRealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  wienerDyadicIncrement level ω i / Real.sqrt (dyadicMesh level)

/-- Vector of normalized dyadic increments for the concrete nonnegative-time Wiener path space. -/
noncomputable def normalizedWienerDyadicIncrementMap (level : ℕ) :
    WienerRealPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => normalizedWienerDyadicIncrement level ω i

/-- Concrete standard Wiener measure on nonnegative-time real paths. -/
noncomputable def standardWienerMeasure : Measure WienerRealPath :=
  ForMathlib.MeasureTheory.wienerMeasure

/-- The concrete Wiener measure is a probability measure. -/
instance isProbabilityMeasure_standardWienerMeasure : IsProbabilityMeasure standardWienerMeasure := by
  dsimp [standardWienerMeasure]
  infer_instance

/-- Concrete standard-Wiener interface for measures on `NNReal → ℝ`.

This is the first real-Wiener capstone that follows directly from the vendored Kolmogorov
extension: the canonical coordinate process on `NNReal → ℝ` has the Brownian projective-family law.
The stronger normalized-dyadic-product law is now a downstream consequence target, not an implicit
`sorry` hidden inside this interface. -/
structure IsConcreteStandardWiener (W : Measure WienerRealPath) : Prop where
  is_probability : IsProbabilityMeasure W
  is_preBrownian : ProbabilityTheory.IsPreBrownianReal (fun t (ω : WienerRealPath) => ω t) W

/-- The canonical coordinate process under the vendored Wiener measure is a pre-Brownian motion.

This discharges the concrete projective-family part of the "real Wiener measure" capstone: every
finite coordinate marginal of `standardWienerMeasure` is exactly `BrownianReal.projectiveFamily`.
The proof is a direct wrapper around `ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure`. -/
theorem isPreBrownianReal_standardWienerMeasure :
    ProbabilityTheory.IsPreBrownianReal (fun t (ω : WienerRealPath) => ω t)
      standardWienerMeasure := by
  refine ProbabilityTheory.IsPreBrownianReal.mk' ?_
  intro I
  refine ⟨?_, ?_⟩
  · fun_prop
  · simpa [standardWienerMeasure] using
      (ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure I)

/-- The vendored concrete Wiener measure satisfies the focused nonnegative-time standard-Wiener
interface. -/
theorem isConcreteStandardWiener_standardWienerMeasure :
    IsConcreteStandardWiener standardWienerMeasure := by
  exact ⟨inferInstance, isPreBrownianReal_standardWienerMeasure⟩

/-- Finite-dimensional coordinate law of the concrete Wiener measure.

This is the direct projective-limit marginal statement: restricting a Wiener path to any finite set
of nonnegative times has Mathlib's Brownian projective-family law on that finite coordinate set. -/
theorem standardWienerMeasure_finite_coordinate_law (I : Finset NNReal) :
    Measure.map (fun ω : WienerRealPath => I.restrict ω) standardWienerMeasure
      = ProbabilityTheory.BrownianReal.projectiveFamily I := by
  simpa [standardWienerMeasure] using
    (ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure I)

/-- The dyadic endpoint grid `{0, 1/2ⁿ, ..., 1}` as a finite set of nonnegative times. -/
noncomputable def wienerDyadicGrid (level : ℕ) : Finset NNReal :=
  (Finset.range (2 ^ level + 1)).image (fun i : ℕ => dyadicTimeNNReal level i)

/-- Dyadic endpoint times belong to the level grid. -/
lemma dyadicTimeNNReal_mem_wienerDyadicGrid
    (level i : ℕ) (hi : i ≤ 2 ^ level) :
    dyadicTimeNNReal level i ∈ wienerDyadicGrid level := by
  classical
  refine Finset.mem_image.mpr ?_
  refine ⟨i, ?_, rfl⟩
  simpa [Nat.lt_succ_iff] using hi

/-- A dyadic endpoint, bundled as an element of the dyadic grid. -/
noncomputable def wienerDyadicGridPoint (level i : ℕ) (hi : i ≤ 2 ^ level) :
    wienerDyadicGrid level :=
  ⟨dyadicTimeNNReal level i, dyadicTimeNNReal_mem_wienerDyadicGrid level i hi⟩

/-- Normalized dyadic increment as a linear map out of the finite dyadic endpoint vector. -/
noncomputable def normalizedWienerDyadicIncrementFromGrid (level : ℕ) :
    ((wienerDyadicGrid level) → ℝ) → (Fin (2 ^ level) → ℝ) :=
  fun x i =>
    (x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
        - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2)))
      / Real.sqrt (dyadicMesh level)

/-- The finite-grid normalized-increment map factors through restriction to the dyadic endpoint grid. -/
theorem normalizedWienerDyadicIncrementMap_eq_fromGrid (level : ℕ) :
    normalizedWienerDyadicIncrementMap level
      = normalizedWienerDyadicIncrementFromGrid level ∘
          (fun ω : WienerRealPath => (wienerDyadicGrid level).restrict ω) := by
  funext ω i
  simp [normalizedWienerDyadicIncrementMap, normalizedWienerDyadicIncrementFromGrid,
    normalizedWienerDyadicIncrement, wienerDyadicIncrement, Function.comp,
    wienerDyadicGridPoint]

/-- The normalized dyadic increment law under Wiener measure reduces to a finite-dimensional
Brownian projective-family statement on the dyadic endpoint grid.

This is the main structural reduction needed before invoking independent-increment/product-Gaussian
lemmas for `BrownianReal.projectiveFamily`. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_reduce_to_projectiveFamily
    (level : ℕ) :
    Measure.map (normalizedWienerDyadicIncrementMap level) standardWienerMeasure
      = Measure.map (normalizedWienerDyadicIncrementFromGrid level)
          (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)) := by
  rw [normalizedWienerDyadicIncrementMap_eq_fromGrid level]
  let r : WienerRealPath → (wienerDyadicGrid level → ℝ) :=
    fun ω => (wienerDyadicGrid level).restrict ω
  let g : (wienerDyadicGrid level → ℝ) → (Fin (2 ^ level) → ℝ) :=
    normalizedWienerDyadicIncrementFromGrid level
  have hr : Measurable r := by
    dsimp [r]
    exact (wienerDyadicGrid level).measurable_restrict
  have hg : Measurable g := by
    dsimp [g]
    unfold normalizedWienerDyadicIncrementFromGrid dyadicMesh
    fun_prop
  have hmap : Measure.map g (Measure.map r standardWienerMeasure)
      = Measure.map (g ∘ r) standardWienerMeasure :=
    Measure.map_map hg hr
  change Measure.map (g ∘ r) standardWienerMeasure =
    Measure.map g (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
  rw [← hmap]
  rw [standardWienerMeasure_finite_coordinate_law (wienerDyadicGrid level)]

/-- Remaining Brownian finite-dimensional algebra capstone: under the Brownian projective-family law
on dyadic endpoint coordinates, normalized consecutive increments are iid standard Gaussian.

This is now the single finite-dimensional theorem left between the concrete Wiener construction and
the sequence-model Cameron--Martin theorem. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_law_target : Prop :=
  ∀ level : ℕ,
    Measure.map (normalizedWienerDyadicIncrementFromGrid level)
        (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- One-dimensional Brownian increment normalization target on the concrete dyadic grid.

For each dyadic edge, the corresponding normalized increment should have law `N(0,1)`.
This is the coordinate-level theorem that should follow from Mathlib's Brownian increment law
`measurePreserving_eval_sub_eval_projectiveFamily` plus the scaling `Δt = 2⁻ˡᵉᵛᵉˡ`. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_coord_law_target : Prop :=
  ∀ (level : ℕ) (i : Fin (2 ^ level)),
    Measure.map (fun x : wienerDyadicGrid level → ℝ =>
        normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = gaussianReal 0 1

/-- Finite-dimensional independence target for normalized dyadic increments.

Together with the coordinate law above, this is the product-law route to
`brownianProjectiveFamily_normalizedDyadicIncrement_law_target`.  It isolates the remaining
Brownian covariance/independent-increment work from the already-proved projective-limit reduction. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_indepFun_target : Prop :=
  ∀ level : ℕ,
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun x : wienerDyadicGrid level → ℝ =>
          normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))

/-- Next concrete capstone, now exposed as an ordinary theorem target instead of a hidden interface
field: derive the iid standard-normal law of normalized dyadic increments from
`isPreBrownianReal_standardWienerMeasure`, Brownian independent increments, and the Gaussian
product/normalization lemmas. -/
def normalizedWienerDyadicIncrementMap_standardWiener_law_target : Prop :=
  ∀ level : ℕ,
    Measure.map (normalizedWienerDyadicIncrementMap level) standardWienerMeasure
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- Concrete normalized dyadic iid-Gaussian law for the vendored Wiener measure, assuming the finite
Brownian projective-family increment algebra. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_of_projectiveFamily
    (hproj : brownianProjectiveFamily_normalizedDyadicIncrement_law_target) :
    normalizedWienerDyadicIncrementMap_standardWiener_law_target := by
  intro level
  rw [normalizedWienerDyadicIncrementMap_standardWiener_law_reduce_to_projectiveFamily level]
  exact hproj level


/-! ### M4 concrete Wiener finite-dimensional theorem ladder

The declarations in this block spell out the remaining concrete Wiener proof obligations that
turn the vendored Kolmogorov/Wiener construction on `NNReal → ℝ` into the dyadic iid Gaussian
interface used by the abstract M4 Cameron--Martin theorem.  The large Brownian independent-
increment and path-space KL-exhaustion facts are intentionally exposed as theorem statements so
we can fill them in one by one without changing downstream theorem names. -/

/-- The length of each dyadic interval is exactly the dyadic mesh. -/
theorem dyadicTimeNNReal_succ_sub (level : ℕ) (i : Fin (2 ^ level)) :
    ((dyadicTimeNNReal level (i.1 + 1) : ℝ) - (dyadicTimeNNReal level i.1 : ℝ))
      = dyadicMesh level := by
  rw [show (dyadicTimeNNReal level (i.1 + 1) : ℝ)
      = (((i.1 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ level)) by rfl]
  rw [show (dyadicTimeNNReal level i.1 : ℝ)
      = (((i.1 : ℕ) : ℝ) / ((2 : ℝ) ^ level)) by rfl]
  unfold dyadicMesh
  have hpow : ((2 : ℝ) ^ level) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow]
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- Scaling a centered one-dimensional Gaussian by its standard deviation gives `N(0,1)`.

This is the scalar normalization lemma needed after Brownian increments give variance equal to
`dyadicMesh level`. -/
theorem gaussianReal_map_div_sqrt_self {σ2 : NNReal} (hσ2 : 0 < (σ2 : ℝ)) :
    Measure.map (fun x : ℝ => x / Real.sqrt (σ2 : ℝ)) (gaussianReal 0 σ2) = gaussianReal 0 1 := by
  let L : ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun x : ℝ => x / Real.sqrt (σ2 : ℝ)
      map_add' := by
        intro x y
        ring
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply]
        ring_nf }
  calc
    Measure.map (fun x : ℝ => x / Real.sqrt (σ2 : ℝ)) (gaussianReal 0 σ2)
        = Measure.map L (gaussianReal 0 σ2) := by rfl
    _ = gaussianReal (L 0) (((L 1) ^ 2).toNNReal * σ2) := by
        exact gaussianReal_map_linearMap (μ := 0) (v := σ2) L
    _ = gaussianReal 0 1 := by
        apply (gaussianReal_ext_iff).2
        constructor
        · simp [L]
        · ext
          have hsqrt_pos : 0 < Real.sqrt (σ2 : ℝ) := Real.sqrt_pos.2 hσ2
          have hsqrt_ne : Real.sqrt (σ2 : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
          have hsqrt_sq : Real.sqrt (σ2 : ℝ) ^ 2 = (σ2 : ℝ) := by
            rw [Real.sq_sqrt (le_of_lt hσ2)]
          have hcalc : ((1 / Real.sqrt (σ2 : ℝ)) ^ 2) * (σ2 : ℝ) = (1 : ℝ) := by
            calc
              ((1 / Real.sqrt (σ2 : ℝ)) ^ 2) * (σ2 : ℝ)
                  = ((1 / Real.sqrt (σ2 : ℝ)) ^ 2) * (Real.sqrt (σ2 : ℝ) ^ 2) := by
                    rw [hsqrt_sq]
              _ = 1 := by
                    field_simp [hsqrt_ne]
          change ((((1 / Real.sqrt (σ2 : ℝ)) ^ 2).toNNReal : ℝ) * (σ2 : ℝ)) = (1 : ℝ)
          rw [Real.toNNReal_of_nonneg (sq_nonneg (1 / Real.sqrt (σ2 : ℝ)))]
          exact hcalc

/-- The nonnegative distance between consecutive dyadic endpoints is the dyadic mesh. -/
theorem nndist_dyadicTimeNNReal_succ (level : ℕ) (i : Fin (2 ^ level)) :
    nndist (dyadicTimeNNReal level (i.1 + 1)) (dyadicTimeNNReal level i.1)
      = dyadicMeshNNReal level := by
  ext
  rw [coe_nndist]
  change dist ((dyadicTimeNNReal level (i.1 + 1) : ℝ))
      ((dyadicTimeNNReal level i.1 : ℝ)) = dyadicMesh level
  rw [Real.dist_eq, abs_of_nonneg]
  · exact dyadicTimeNNReal_succ_sub level i
  · rw [dyadicTimeNNReal_succ_sub level i]
    unfold dyadicMesh
    positivity

/-- Raw dyadic Brownian increment law under the finite Brownian projective family.

This is the coordinate-law theorem before variance normalization. -/
theorem brownianProjectiveFamily_dyadicIncrement_law
    (level : ℕ) (i : Fin (2 ^ level)) :
    Measure.map (fun x : wienerDyadicGrid level → ℝ =>
        x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
          - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2)))
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = gaussianReal 0 (dyadicMeshNNReal level) := by
  let t0 : NNReal := dyadicTimeNNReal level i.1
  let t1 : NNReal := dyadicTimeNNReal level (i.1 + 1)
  let r : WienerRealPath → (wienerDyadicGrid level → ℝ) :=
    fun ω => (wienerDyadicGrid level).restrict ω
  let rawGrid : (wienerDyadicGrid level → ℝ) → ℝ := fun x =>
    x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
      - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2))
  let rawPath : WienerRealPath → ℝ := fun ω => ω t1 - ω t0
  have hr : Measurable r := by
    dsimp [r]
    exact (wienerDyadicGrid level).measurable_restrict
  have hrawGrid : Measurable rawGrid := by
    dsimp [rawGrid]
    fun_prop
  have hcomp : rawGrid ∘ r = rawPath := by
    funext ω
    simp [rawGrid, r, rawPath, t0, t1, wienerDyadicGridPoint]
  have hmap : Measure.map rawGrid
        (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = Measure.map rawPath standardWienerMeasure := by
    rw [← standardWienerMeasure_finite_coordinate_law (wienerDyadicGrid level)]
    rw [Measure.map_map hrawGrid hr]
    rw [hcomp]
  rw [hmap]
  have hlaw := isPreBrownianReal_standardWienerMeasure.hasLaw_sub t1 t0
  have hvar : nndist t1 t0 = dyadicMeshNNReal level := by
    simpa [t0, t1] using nndist_dyadicTimeNNReal_succ level i
  rw [← hvar]
  exact hlaw.map_eq

/-- Normalized dyadic Brownian increments have standard normal one-dimensional law. -/
theorem brownianProjectiveFamily_normalizedDyadicIncrement_coord_law
    (level : ℕ) (i : Fin (2 ^ level)) :
    Measure.map (fun x : wienerDyadicGrid level → ℝ =>
        normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = gaussianReal 0 1 := by
  let raw : (wienerDyadicGrid level → ℝ) → ℝ := fun x =>
    x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
      - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2))
  let scale : ℝ → ℝ := fun y => y / Real.sqrt (dyadicMesh level)
  have hraw : Measurable raw := by
    dsimp [raw]
    fun_prop
  have hscale : Measurable scale := by
    dsimp [scale]
    fun_prop
  have hfun : (fun x : wienerDyadicGrid level → ℝ =>
        normalizedWienerDyadicIncrementFromGrid level x i) = scale ∘ raw := by
    funext x
    simp [raw, scale, normalizedWienerDyadicIncrementFromGrid]
  rw [hfun]
  rw [← Measure.map_map (μ := ProbabilityTheory.BrownianReal.projectiveFamily
    (wienerDyadicGrid level)) hscale hraw]
  rw [brownianProjectiveFamily_dyadicIncrement_law level i]
  exact gaussianReal_map_div_sqrt_self (σ2 := dyadicMeshNNReal level) (by
    change 0 < dyadicMesh level
    unfold dyadicMesh
    positivity)

/-- Dyadic endpoints form a monotone nonnegative-time sequence. -/
theorem monotone_dyadicTimeNNReal (level : ℕ) :
    Monotone (fun n : ℕ => dyadicTimeNNReal level n) := by
  intro a b hab
  rw [← NNReal.coe_le_coe]
  change ((a : ℝ) / ((2 : ℝ) ^ level)) ≤ ((b : ℝ) / ((2 : ℝ) ^ level))
  have hden_nonneg : 0 ≤ ((2 : ℝ) ^ level) := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hab) hden_nonneg

/-- Dyadic Brownian increments are independent under the concrete vendored Wiener measure. -/
theorem standardWienerMeasure_dyadicIncrement_indepFun
    (level : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun ω : WienerRealPath =>
          ω (dyadicTimeNNReal level (i.1 + 1)) - ω (dyadicTimeNNReal level i.1))
      standardWienerMeasure := by
  have hnat : ProbabilityTheory.iIndepFun
      (fun n : ℕ =>
        fun ω : WienerRealPath =>
          ω (dyadicTimeNNReal level (n + 1)) - ω (dyadicTimeNNReal level n))
      standardWienerMeasure := by
    exact (ProbabilityTheory.IsPreBrownianReal.hasIndepIncrements
      isPreBrownianReal_standardWienerMeasure).nat
        (t := fun n : ℕ => dyadicTimeNNReal level n)
        (monotone_dyadicTimeNNReal level)
  have hinj : Function.Injective (fun i : Fin (2 ^ level) => i.1) := by
    intro i j hij
    ext
    exact hij
  simpa [Function.comp] using
    (hnat.precomp (g := fun i : Fin (2 ^ level) => i.1) hinj)

/-- Raw dyadic Brownian increments over disjoint adjacent intervals are independent. -/
theorem brownianProjectiveFamily_dyadicIncrement_indepFun
    (level : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun x : wienerDyadicGrid level → ℝ =>
          x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
            - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2)))
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)) := by
  let r : WienerRealPath → (wienerDyadicGrid level → ℝ) :=
    fun ω => (wienerDyadicGrid level).restrict ω
  let rawGrid : Fin (2 ^ level) → ((wienerDyadicGrid level → ℝ) → ℝ) := fun i x =>
    x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
      - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2))
  let rawPath : Fin (2 ^ level) → (WienerRealPath → ℝ) := fun i ω =>
    ω (dyadicTimeNNReal level (i.1 + 1)) - ω (dyadicTimeNNReal level i.1)
  have hr : Measurable r := by
    dsimp [r]
    fun_prop
  have hrawGrid_meas : ∀ i : Fin (2 ^ level), Measurable (rawGrid i) := by
    intro i
    dsimp [rawGrid]
    fun_prop
  have hvecGrid_meas : Measurable (fun x : wienerDyadicGrid level → ℝ => fun i => rawGrid i x) := by
    dsimp [rawGrid]
    fun_prop
  have hcomp : (fun i : Fin (2 ^ level) => rawGrid i ∘ r) = rawPath := by
    funext i ω
    simp [rawGrid, rawPath, r, wienerDyadicGridPoint]
  have hindepPath := standardWienerMeasure_dyadicIncrement_indepFun level
  have hindepComp : ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) => rawGrid i ∘ r) standardWienerMeasure := by
    rw [hcomp]
    exact hindepPath
  have hprodPath :
      Measure.map (fun ω : WienerRealPath => fun i : Fin (2 ^ level) => (rawGrid i ∘ r) ω)
          standardWienerMeasure
        = Measure.pi (fun i : Fin (2 ^ level) =>
            Measure.map (rawGrid i ∘ r) standardWienerMeasure) := by
    simpa [Function.comp] using
      (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (μ := standardWienerMeasure)
        (f := fun i : Fin (2 ^ level) => rawGrid i ∘ r)
        (by
          intro i
          exact ((hrawGrid_meas i).comp hr).aemeasurable)).mp hindepComp
  have hprojective :
      ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)
        = Measure.map r standardWienerMeasure := by
    exact (standardWienerMeasure_finite_coordinate_law (wienerDyadicGrid level)).symm
  refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (μ := ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      (f := rawGrid)
      (by
        intro i
        exact (hrawGrid_meas i).aemeasurable)).mpr ?_
  rw [hprojective]
  calc
    Measure.map (fun x : wienerDyadicGrid level → ℝ => fun i : Fin (2 ^ level) => rawGrid i x)
        (Measure.map r standardWienerMeasure)
        = Measure.map (((fun x : wienerDyadicGrid level → ℝ =>
              fun i : Fin (2 ^ level) => rawGrid i x) ∘ r))
            standardWienerMeasure := by
          exact (Measure.map_map (μ := standardWienerMeasure) hvecGrid_meas hr)
    _ = Measure.map (fun ω : WienerRealPath => fun i : Fin (2 ^ level) => rawGrid i (r ω))
            standardWienerMeasure := by
          rfl
    _ = Measure.pi (fun i : Fin (2 ^ level) =>
          Measure.map (rawGrid i ∘ r) standardWienerMeasure) := by
          simpa [Function.comp] using hprodPath
    _ = Measure.pi (fun i : Fin (2 ^ level) =>
          Measure.map (rawGrid i) (Measure.map r standardWienerMeasure)) := by
          congr
          funext i
          simpa [Function.comp] using
            (Measure.map_map (μ := standardWienerMeasure) (hrawGrid_meas i) hr).symm

/-- Normalizing independent dyadic increments preserves independence. -/
theorem brownianProjectiveFamily_normalizedDyadicIncrement_indepFun
    (level : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun x : wienerDyadicGrid level → ℝ =>
          normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)) := by
  have hraw := brownianProjectiveFamily_dyadicIncrement_indepFun level
  let scale : ℝ → ℝ := fun y => y / Real.sqrt (dyadicMesh level)
  have hscale : Measurable scale := by
    dsimp [scale]
    fun_prop
  have hcomp := hraw.comp (fun _ : Fin (2 ^ level) => scale) (fun _ => hscale)
  convert hcomp using 3
  · simp [normalizedWienerDyadicIncrementFromGrid, scale, Function.comp]

/-- Product-law assembly: independent standard-normal coordinates form the finite standard
Gaussian product measure. -/
theorem map_eq_stdGaussian_of_iIndepFun_coord_gaussian
    {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ι → ℝ}
    (hf : Measurable f)
    (hcoord : ∀ i : ι, Measure.map (fun x : Ω => f x i) μ = gaussianReal 0 1)
    (hindep : ProbabilityTheory.iIndepFun (fun i : ι => fun x : Ω => f x i) μ) :
    Measure.map f μ = ForMathlib.MeasureTheory.stdGaussian ι := by
  have hprod : Measure.map f μ = Measure.pi (fun i : ι => Measure.map (fun x : Ω => f x i) μ) := by
    simpa [Function.comp] using
      (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (μ := μ) (f := fun i : ι => fun x : Ω => f x i)
        (by
          intro i
          exact ((measurable_pi_apply i).comp hf).aemeasurable)).mp hindep
  rw [hprod]
  unfold ForMathlib.MeasureTheory.stdGaussian
  congr
  funext i
  exact hcoord i

/-- Finite Brownian projective-family algebra: normalized dyadic increments are iid standard
Gaussian. -/
theorem brownianProjectiveFamily_normalizedDyadicIncrement_law
    (level : ℕ) :
    Measure.map (normalizedWienerDyadicIncrementFromGrid level)
        (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  have hmeas : Measurable (normalizedWienerDyadicIncrementFromGrid level) := by
    unfold normalizedWienerDyadicIncrementFromGrid dyadicMesh
    fun_prop
  exact map_eq_stdGaussian_of_iIndepFun_coord_gaussian
    (μ := ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
    (f := normalizedWienerDyadicIncrementFromGrid level)
    hmeas
    (brownianProjectiveFamily_normalizedDyadicIncrement_coord_law level)
    (brownianProjectiveFamily_normalizedDyadicIncrement_indepFun level)

/-- Concrete normalized dyadic iid-Gaussian law for the vendored Wiener measure. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law
    (level : ℕ) :
    Measure.map (normalizedWienerDyadicIncrementMap level) standardWienerMeasure
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  rw [normalizedWienerDyadicIncrementMap_standardWiener_law_reduce_to_projectiveFamily level]
  exact brownianProjectiveFamily_normalizedDyadicIncrement_law level

/-- The previous theorem discharges the target `Prop` used by earlier roadmap notes. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_done :
    normalizedWienerDyadicIncrementMap_standardWiener_law_target := by
  intro level
  exact normalizedWienerDyadicIncrementMap_standardWiener_law level

/-- Extension map from nonnegative-time Wiener paths to the current real-time `RealPath` scaffold.

The extension freezes the negative-time query by evaluating at `max t 0`.  The M4 theorem only uses
nonnegative dyadic times, so the normalized dyadic increments commute with this extension. -/
noncomputable def wienerToRealPath (ω : WienerRealPath) : RealPath :=
  fun t : ℝ => ω ⟨max t 0, by exact le_max_right t 0⟩

/-- Measurability of the nonnegative-time-to-real-time Wiener path extension. -/
theorem measurable_wienerToRealPath : Measurable wienerToRealPath := by
  unfold wienerToRealPath
  fun_prop

/-- Real-time path measure obtained by transporting the vendored concrete Wiener measure. -/
noncomputable def standardWienerRealPathMeasure : Measure RealPath :=
  Measure.map wienerToRealPath standardWienerMeasure

/-- The transported real-time Wiener path measure is a probability measure. -/
instance isProbabilityMeasure_standardWienerRealPathMeasure :
    IsProbabilityMeasure standardWienerRealPathMeasure := by
  unfold standardWienerRealPathMeasure
  exact Measure.isProbabilityMeasure_map measurable_wienerToRealPath.aemeasurable

/-- Normalized dyadic increments commute with the nonnegative-time-to-real-time extension. -/
theorem normalizedDyadicIncrementMap_wienerToRealPath
    (level : ℕ) (ω : WienerRealPath) :
    normalizedDyadicIncrementMap level (wienerToRealPath ω)
      = normalizedWienerDyadicIncrementMap level ω := by
  funext i
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement
    normalizedWienerDyadicIncrementMap normalizedWienerDyadicIncrement wienerDyadicIncrement
    wienerToRealPath
  have hsucc_nn :
      (⟨max (dyadicTime level (i.1 + 1)) 0,
          by exact le_max_right (dyadicTime level (i.1 + 1)) 0⟩ : NNReal)
        = dyadicTimeNNReal level (i.1 + 1) := by
    ext
    change max ((((i.1 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))) (0 : ℝ)
      = (((i.1 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))
    exact max_eq_left (by positivity)
  have hi_nn :
      (⟨max (dyadicTime level i.1) 0,
          by exact le_max_right (dyadicTime level i.1) 0⟩ : NNReal)
        = dyadicTimeNNReal level i.1 := by
    ext
    change max ((((i.1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))) (0 : ℝ)
      = (((i.1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))
    exact max_eq_left (by positivity)
  rw [hsucc_nn, hi_nn]

/-- Concrete-to-abstract transport interface for the real Wiener capstone.

A map `Φ : (NNReal → ℝ) → RealPath` transports the concrete vendored Wiener measure into the
current CGP-facing `RealPath` scaffold if it is measurable, preserves all normalized dyadic
increment maps, and satisfies the path-space KL exhaustion theorem after transport. -/
structure ConcreteWienerTransport (Φ : WienerRealPath → RealPath) : Prop where
  measurable : Measurable Φ
  normalized_dyadic_commutes : ∀ level : ℕ,
    normalizedDyadicIncrementMap level ∘ Φ = normalizedWienerDyadicIncrementMap level

/-- The canonical extension map is the intended concrete-to-abstract Wiener transport. -/
theorem concreteWienerTransport_wienerToRealPath :
    ConcreteWienerTransport wienerToRealPath := by
  refine ⟨measurable_wienerToRealPath, ?_⟩
  intro level
  funext ω
  exact normalizedDyadicIncrementMap_wienerToRealPath level ω

/-- Transporting the concrete Wiener law through a valid concrete-to-abstract map gives the
finite-dimensional normalized-dyadic Gaussian laws required by `IsStandardWiener`. -/
theorem normalizedDyadicIncrementMap_concrete_transport_law
    (Φ : WienerRealPath → RealPath) (hΦ : ConcreteWienerTransport Φ) (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level) (Measure.map Φ standardWienerMeasure)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  have hN : Measurable (normalizedDyadicIncrementMap level) := by
    unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement dyadicMesh dyadicTime
    fun_prop
  have hmap :
      Measure.map (normalizedDyadicIncrementMap level) (Measure.map Φ standardWienerMeasure)
        = Measure.map (normalizedDyadicIncrementMap level ∘ Φ) standardWienerMeasure := by
    simpa using (Measure.map_map (μ := standardWienerMeasure) hN hΦ.measurable)
  rw [hmap, hΦ.normalized_dyadic_commutes level]
  exact normalizedWienerDyadicIncrementMap_standardWiener_law level

/-- Any probability-measure wrapper around the transported concrete Wiener law satisfies the
abstract `IsStandardWiener` interface used by the M4 path-level theorem. -/
theorem isStandardWiener_of_concrete_transport
    (Φ : WienerRealPath → RealPath) (hΦ : ConcreteWienerTransport Φ)
    (W : ProbabilityMeasure RealPath)
    (hW : (W : Measure RealPath) = Measure.map Φ standardWienerMeasure) :
    IsStandardWiener W := by
  constructor
  · intro level
    rw [hW]
    exact normalizedDyadicIncrementMap_concrete_transport_law Φ hΦ level

/-- The canonical transported real-time Wiener law satisfies `IsStandardWiener`, modulo choosing any
`ProbabilityMeasure` wrapper whose underlying measure is `standardWienerRealPathMeasure`. -/
theorem isStandardWiener_standardWienerRealPathMeasure
    (W : ProbabilityMeasure RealPath)
    (hW : (W : Measure RealPath) = standardWienerRealPathMeasure) :
    IsStandardWiener W := by
  unfold standardWienerRealPathMeasure at hW
  exact isStandardWiener_of_concrete_transport wienerToRealPath
    concreteWienerTransport_wienerToRealPath W hW

/-- M4.1: dyadic normalized increment maps are measurable. -/
theorem measurable_normalizedDyadicIncrementMap (level : ℕ) :
    Measurable (normalizedDyadicIncrementMap level) := by
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement dyadicMesh dyadicTime
  fun_prop

/-- M4.1: normalized increments commute with deterministic path shifts. -/
theorem normalizedDyadicIncrementMap_add (level : ℕ) (ω h : RealPath) :
    normalizedDyadicIncrementMap level (ω + h)
      = normalizedDyadicIncrementMap level ω + normalizedDyadicIncrementMap level h := by
  funext i
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement
  simp [Pi.add_apply]
  ring

/-- M4.2: standard Wiener measure has standard-normal normalized dyadic
increments.  This is exposed as a theorem wrapper around `IsStandardWiener` so
downstream statements do not inspect the structure field directly. -/
theorem normalizedDyadicIncrementMap_wiener_law (W : ProbabilityMeasure RealPath)
    (hW : IsStandardWiener W) (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  exact hW.normalized_dyadic_law level

/-- M4.2/M4.3: after shifting a Wiener path by a deterministic path `h`, the
normalized dyadic increment law is the finite-dimensional standard Gaussian
shifted by the normalized increment vector of `h`. -/
theorem normalizedDyadicIncrementMap_shifted_wiener_law
    (W : ProbabilityMeasure RealPath) (hW : IsStandardWiener W)
    (level : ℕ) (h : RealPath) :
    Measure.map (normalizedDyadicIncrementMap level)
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
      = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) := by
  let N : RealPath → (Fin (2 ^ level) → ℝ) := normalizedDyadicIncrementMap level
  let v : Fin (2 ^ level) → ℝ := normalizedDyadicIncrementMap level h
  have hN : Measurable N := measurable_normalizedDyadicIncrementMap level
  have hshift : Measurable (fun ω : RealPath => ω + h) := by fun_prop
  have hshiftFin : Measurable (fun x : Fin (2 ^ level) → ℝ => x + v) := by fun_prop
  have hcomp : N ∘ (fun ω : RealPath => ω + h) =
      (fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N := by
    funext ω
    exact normalizedDyadicIncrementMap_add level ω h
  calc
    Measure.map N ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        = (W : Measure RealPath).map (N ∘ (fun ω : RealPath => ω + h)) := by
            rw [Measure.map_map hN hshift]
    _ = (W : Measure RealPath).map ((fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N) := by
            rw [hcomp]
    _ = ((W : Measure RealPath).map N).map (fun x : Fin (2 ^ level) → ℝ => x + v) := by
            rw [Measure.map_map hshiftFin hN]
    _ = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) := by
            change ((W : Measure RealPath).map (normalizedDyadicIncrementMap level)).map
                (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) = _
            rw [normalizedDyadicIncrementMap_wiener_law W hW level]

/-- M4.3: finite dyadic projection of the deterministic Wiener shift has exactly
the finite-dimensional Cameron--Martin cost. -/
theorem klDiv_normalizedDyadicIncrement_shifted_wiener
    (W : ProbabilityMeasure RealPath) (hW : IsStandardWiener W)
    (level : ℕ) (h : RealPath) :
    InformationTheory.klDiv
        (Measure.map (normalizedDyadicIncrementMap level)
          ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
        (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath))
      = ENNReal.ofReal (dyadicPathEnergy level h) := by
  rw [normalizedDyadicIncrementMap_shifted_wiener_law W hW level h,
    normalizedDyadicIncrementMap_wiener_law W hW level]
  simpa [dyadicPathEnergy] using
    (ForMathlib.MeasureTheory.klDiv_stdGaussian_map_add
      (normalizedDyadicIncrementMap level h))

/-- M4.4: dyadic finite-grid Cameron--Martin energies converge to the continuum
energy of a Cameron--Martin path. -/
theorem dyadicPathEnergy_tendsto_cameronMartinPathEnergy
    (h : RealPath) (hderiv : ℝ → ℝ) (hCM : IsCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  exact hCM.dyadic_energy_tendsto

/-- M4.5: dyadic normalized-increment KLs converge to the full path-law KL.
This is the path-level projection/exhaustion analogue of the sequence-model
prefix KL convergence theorem. -/
theorem klDiv_normalizedDyadicIncrement_tendsto_path_kl
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hKL : HasDyadicKLExhaustion W)
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

/-- M4 final ENNReal form: path-level deterministic Cameron--Martin identity for
standard Wiener measure.  This is the continuum theorem that should eventually
replace the abstract `hCM` edge in `energy_identity`. -/
theorem klDiv_wiener_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  have hkl := klDiv_normalizedDyadicIncrement_tendsto_path_kl W h hKL hac
  have hkl' : Filter.Tendsto (fun level : ℕ => ENNReal.ofReal (dyadicPathEnergy level h))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath))) := by
    simpa [klDiv_normalizedDyadicIncrement_shifted_wiener W hW] using hkl
  have henergy : Filter.Tendsto (fun level : ℕ => ENNReal.ofReal (dyadicPathEnergy level h))
      Filter.atTop (nhds (ENNReal.ofReal (cameronMartinPathEnergy hderiv))) := by
    exact (ENNReal.continuous_ofReal.tendsto (cameronMartinPathEnergy hderiv)).comp
      (dyadicPathEnergy_tendsto_cameronMartinPathEnergy h hderiv hCM)
  exact tendsto_nhds_unique hkl' henergy

/-- M4 final real-valued form: the path-level `klReal` identity used by the CGP
energy-identity edge. -/
theorem klReal_wiener_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  rw [klReal, klDiv_wiener_shift_eq_cameronMartinPathEnergy W h hderiv hW hKL hCM hac]
  exact ENNReal.toReal_ofReal (by
    unfold cameronMartinPathEnergy
    positivity)

/-- M4-to-CGP bridge: if a CGP conditional path-kernel edge is represented as a
standard Wiener law shifted by a Cameron--Martin path, then the abstract `hCM`
term required by `energy_identity` is supplied by the path-level theorem above.
The remaining future work is to instantiate these hypotheses for the actual
SDE/feedback kernels of CGP. -/
theorem hCM_from_wiener_shift_scaffold
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ) (E : ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath))
    (henergy : E = cameronMartinPathEnergy hderiv) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = E := by
  rw [henergy]
  exact klReal_wiener_shift_eq_cameronMartinPathEnergy W h hderiv hW hKL hCM hac


/-- End-to-end M4 Wiener-shift theorem for the transported concrete Wiener measure. -/
theorem klDiv_standardWienerRealPath_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  exact klDiv_wiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardWiener_standardWienerRealPathMeasure W hWmeasure) hKL hCM hac

/-- Real-valued end-to-end M4 Wiener-shift theorem for the transported concrete Wiener measure. -/
theorem klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_wiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardWiener_standardWienerRealPathMeasure W hWmeasure) hKL hCM hac


end ChenGeorgiouPavon2021
