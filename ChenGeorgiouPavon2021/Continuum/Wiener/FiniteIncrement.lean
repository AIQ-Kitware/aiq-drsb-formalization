/-
# Finite Brownian dyadic increment algebra

This module proves the finite-dimensional Brownian increment, normalization,
independence, and product-Gaussian assembly theorems for dyadic increments.
-/

import ChenGeorgiouPavon2021.Continuum.Wiener.Projective

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-! ### M4 concrete Wiener finite-dimensional theorem ladder

The declarations in this block connect the Kolmogorov/Wiener construction on `NNReal → ℝ` to the
dyadic iid Gaussian interface used by the M4 Cameron--Martin theorem.  Brownian increment laws,
normalization, independence, and product assembly are separated into reusable theorem steps. -/

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

/-- Packaged target form of the normalized dyadic iid-Gaussian law. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_done :
    normalizedWienerDyadicIncrementMapStandardWienerLawTarget := by
  intro level
  exact normalizedWienerDyadicIncrementMap_standardWiener_law level

end ChenGeorgiouPavon2021
