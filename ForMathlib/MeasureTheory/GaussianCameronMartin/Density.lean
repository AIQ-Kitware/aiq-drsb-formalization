/-
# Sequence Gaussian Cameron--Martin: finite-density process

This module contains finite-dimensional Cameron--Martin density formulas,
prefix local-density identities, and the L² bounds used by the absolute
continuity theorem.
-/

import ForMathlib.MeasureTheory.GaussianCameronMartin.InfiniteKL

set_option autoImplicit false

open MeasureTheory Real InformationTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace ForMathlib.MeasureTheory

/-- The finite-prefix Cameron-Martin density process for a deterministic shift `c`.
It is real-valued and depends only on coordinates `≤ n`.  The split-sum form is
used because it is the normal form Lean tends to prefer for finite sums of
subtractions. -/
noncomputable def cmDensityProcess (c : RealSeq) (n : ℕ) (x : RealSeq) : ℝ :=
  Real.exp ((∑ i : Finset.Iic n, c i * x i) - (∑ i : Finset.Iic n, 2⁻¹ * c i ^ 2))

/-- The density process is nonnegative. -/
theorem cmDensityProcess_nonneg (c : RealSeq) (n : ℕ) :
    (0 : RealSeq → ℝ) ≤ᵐ[stdSeqGaussian] cmDensityProcess c n := by
  filter_upwards with x
  unfold cmDensityProcess
  exact Real.exp_nonneg _

/-- The density process is strictly positive pointwise. -/
theorem cmDensityProcess_pos (c : RealSeq) (n : ℕ) (x : RealSeq) :
    0 < cmDensityProcess c n x := by
  unfold cmDensityProcess
  exact Real.exp_pos _

/-- The finite-prefix density, written on the restricted coordinate space, agrees with
`cmDensityProcess` after restriction.  This is the subtype-sum bridge used by M2.5. -/
theorem cmDensityProcess_restrict (c : RealSeq) (n : ℕ) (x : RealSeq) :
    Real.exp
        ((∑ i : Finset.Iic n, prefixRestrict n c i * prefixRestrict n x i)
          - (∑ i : Finset.Iic n, 2⁻¹ * prefixRestrict n c i ^ 2))
      = cmDensityProcess c n x := by
  rfl

/-- One-dimensional Cameron--Martin density for a shifted unit-variance Gaussian.  This is
`PLAN_CONTINUUM_CLOSURE.md` M2.1, staged here rather than by editing the vendored
finite-dimensional KL proof. -/
theorem gaussianReal_shift_eq_withDensity (c : ℝ) :
    gaussianReal c 1 = (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (c * x - 2⁻¹ * c ^ 2))) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hac : gaussianReal c 1 ≪ gaussianReal 0 1 :=
    (gaussianReal_absolutelyContinuous c h1).trans (gaussianReal_absolutelyContinuous' 0 h1)
  have hvol0 : gaussianReal 0 1 ≪ volume := gaussianReal_absolutelyContinuous 0 h1
  have hrn_volume : (gaussianReal c 1).rnDeriv (gaussianReal 0 1) =ᵐ[volume]
      fun x => (gaussianPDF 0 1 x)⁻¹ * gaussianPDF c 1 x := by
    have h := Measure.rnDeriv_withDensity_right (gaussianReal c 1) volume
      (f := gaussianPDF 0 1) (measurable_gaussianPDF 0 1).aemeasurable
      (ae_of_all _ fun x => (gaussianPDF_pos 0 h1 x).ne')
      (ae_of_all _ fun _ => gaussianPDF_lt_top.ne)
    rw [← gaussianReal_of_var_ne_zero 0 h1] at h
    filter_upwards [h, rnDeriv_gaussianReal c 1] with x hx hxrn
    rw [hx, hxrn]
  have hden : (gaussianReal c 1).rnDeriv (gaussianReal 0 1) =ᵐ[gaussianReal 0 1]
      fun x => ENNReal.ofReal (Real.exp (c * x - 2⁻¹ * c ^ 2)) := by
    filter_upwards [hvol0.ae_le hrn_volume] with x hx
    rw [hx]
    have hs : Real.sqrt (2 * π) ≠ 0 := by positivity
    have hpdf : (gaussianPDFReal 0 1 x)⁻¹ * gaussianPDFReal c 1 x
        = Real.exp (c * x - 2⁻¹ * c ^ 2) := by
      simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one]
      rw [mul_inv, inv_inv, ← Real.exp_neg, mul_mul_mul_comm, mul_inv_cancel₀ hs, one_mul,
        ← Real.exp_add]
      congr 1
      ring
    have hdenom_ne_zero : gaussianPDF 0 1 x ≠ 0 := (gaussianPDF_pos 0 h1 x).ne'
    have hratio_ne_top : ((gaussianPDF 0 1 x)⁻¹ * gaussianPDF c 1 x) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp [hdenom_ne_zero]) gaussianPDF_lt_top.ne
    have hratio_toReal : ((gaussianPDF 0 1 x)⁻¹ * gaussianPDF c 1 x).toReal
        = Real.exp (c * x - 2⁻¹ * c ^ 2) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
      rw [toReal_gaussianPDF, toReal_gaussianPDF, hpdf]
    rw [← ENNReal.ofReal_toReal hratio_ne_top, hratio_toReal]
  calc
    gaussianReal c 1
        = (gaussianReal 0 1).withDensity
            ((gaussianReal c 1).rnDeriv (gaussianReal 0 1)) := by
          exact (Measure.withDensity_rnDeriv_eq
            (μ := gaussianReal c 1) (ν := gaussianReal 0 1) hac).symm
    _ = (gaussianReal 0 1).withDensity
          (fun x => ENNReal.ofReal (Real.exp (c * x - 2⁻¹ * c ^ 2))) := by
          ext s hs
          rw [withDensity_apply _ hs, withDensity_apply _ hs]
          exact lintegral_congr_ae (ae_restrict_of_ae hden)

/-- Finite-dimensional shifted standard Gaussian law as a product of shifted one-dimensional
Gaussian factors.  This factors out the `hmap` calculation used inside the vendored
`klDiv_stdGaussian_map_add` proof. -/
theorem stdGaussian_map_add_eq_pi_gaussianReal {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    (stdGaussian ι).map (· + h) = Measure.pi (fun i => gaussianReal (h i) 1) := by
  unfold stdGaussian
  change (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x i => x i + h i) =
    Measure.pi (fun i => gaussianReal (h i) 1)
  rw [show (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x i => x i + h i) =
      Measure.pi (fun i => (gaussianReal 0 1).map (fun x : ℝ => x + h i)) by
        simpa using (Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
          (f := fun i (x : ℝ) => x + h i) (hf := fun i => by fun_prop))]
  exact congrArg Measure.pi <| funext fun i => by
    simpa using gaussianReal_map_add_const (μ := 0) (v := 1) (y := h i)

/-- Finite-dimensional Cameron--Martin density in split-sum form.  The split form is
chosen to match the already-defined sequence prefix density process definitionally after
restriction. -/
noncomputable def finiteCmDensity {ι : Type*} [Fintype ι] (h : ι → ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp ((∑ i, h i * x i) - (∑ i, 2⁻¹ * h i ^ 2))

/-- Split-sum and single-sum finite-dimensional Cameron--Martin densities agree. -/
theorem finiteCmDensity_eq_exp_sum {ι : Type*} [Fintype ι] (h : ι → ℝ) (x : ι → ℝ) :
    finiteCmDensity h x = Real.exp (∑ i, (h i * x i - 2⁻¹ * h i ^ 2)) := by
  unfold finiteCmDensity
  congr 1
  rw [Finset.sum_sub_distrib]

/-- The finite-dimensional Cameron--Martin density is measurable. -/
theorem measurable_finiteCmDensity {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    Measurable (finiteCmDensity h) := by
  classical
  unfold finiteCmDensity
  fun_prop

attribute [fun_prop] measurable_finiteCmDensity

/-- Product bookkeeping for positive exponential densities embedded into `ℝ≥0∞`. -/
theorem prod_ofReal_exp_eq_ofReal_exp_sum_finset {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    s.prod (fun i => ENNReal.ofReal (Real.exp (a i))) =
      ENNReal.ofReal (Real.exp (s.sum a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his, Real.exp_add, ih]
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- Product bookkeeping for positive exponential densities embedded into `ℝ≥0∞`. -/
theorem prod_ofReal_exp_eq_ofReal_exp_sum {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∏ i, ENNReal.ofReal (Real.exp (a i))) =
      ENNReal.ofReal (Real.exp (∑ i, a i)) := by
  classical
  simpa using prod_ofReal_exp_eq_ofReal_exp_sum_finset (Finset.univ : Finset ι) a

/-- Finite-dimensional Cameron--Martin density theorem in split-sum form.  This is the
M2.3 density theorem in the shape consumed by the prefix-local-density calculation. -/
theorem stdGaussian_map_add_eq_withDensity_finiteCmDensity {ι : Type*} [Fintype ι]
    (h : ι → ℝ) :
    (stdGaussian ι).map (· + h) = (stdGaussian ι).withDensity
      (fun x => ENNReal.ofReal (finiteCmDensity h x)) := by
  rw [stdGaussian_map_add_eq_pi_gaussianReal h]
  unfold stdGaussian
  have hcoord : (fun i : ι => gaussianReal (h i) 1)
      = fun i : ι => (gaussianReal 0 1).withDensity
          (fun x => ENNReal.ofReal (Real.exp (h i * x - 2⁻¹ * h i ^ 2))) := by
    funext i
    exact gaussianReal_shift_eq_withDensity (h i)
  rw [hcoord]
  rw [pi_withDensity (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun i x => ENNReal.ofReal (Real.exp (h i * x - 2⁻¹ * h i ^ 2)))
    (hf := by intro i; fun_prop)]
  congr 1
  funext x
  rw [finiteCmDensity_eq_exp_sum]
  exact prod_ofReal_exp_eq_ofReal_exp_sum
    (fun i : ι => h i * x i - 2⁻¹ * h i ^ 2)

/-- Finite-dimensional Cameron--Martin density theorem in the roadmap's single-sum form. -/
theorem stdGaussian_map_add_eq_withDensity {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    (stdGaussian ι).map (· + h) = (stdGaussian ι).withDensity
      (fun x => ENNReal.ofReal (Real.exp (∑ i, (h i * x i - 2⁻¹ * h i ^ 2)))) := by
  rw [stdGaussian_map_add_eq_withDensity_finiteCmDensity h]
  congr 1
  funext x
  rw [finiteCmDensity_eq_exp_sum]

/-- The finite-dimensional density, evaluated on a prefix restriction, is exactly the
sequence density process. -/
theorem finiteCmDensity_prefixRestrict (c : RealSeq) (n : ℕ) (x : RealSeq) :
    finiteCmDensity (prefixRestrict n c) (prefixRestrict n x) = cmDensityProcess c n x := by
  rfl

/-- Prefix filtration generated by the first `n + 1` sequence coordinates. -/
noncomputable def prefixFiltration : Filtration ℕ (inferInstance : MeasurableSpace RealSeq) :=
  { seq := fun n => MeasurableSpace.comap (prefixRestrict n) inferInstance
    mono' := by
      intro n m hnm
      change MeasurableSpace.comap (prefixRestrict n) inferInstance ≤
        MeasurableSpace.comap (prefixRestrict m) inferInstance
      rw [← preorder_frestrictLe_eq_prefixRestrict n, ← preorder_frestrictLe_eq_prefixRestrict m]
      calc MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance
          = MeasurableSpace.comap (Preorder.frestrictLe m)
              (MeasurableSpace.comap (Preorder.frestrictLe₂ hnm) inferInstance) := by
            rw [MeasurableSpace.comap_comp, Preorder.frestrictLe₂_comp_frestrictLe]
        _ ≤ MeasurableSpace.comap (Preorder.frestrictLe m) inferInstance :=
            MeasurableSpace.comap_mono (Preorder.measurable_frestrictLe₂ hnm).comap_le
    le' := fun n => (measurable_prefixRestrict n).comap_le }

/-- Local density identity on a prefix cylinder.  This is the concrete preimage form of
`PLAN_CONTINUUM_CLOSURE.md` M2.5. -/
theorem map_add_eq_lintegral_cmDensityProcess_preimage (c : RealSeq) (n : ℕ)
    {t : Set (PrefixSpace n)} (ht : MeasurableSet t) :
    (stdSeqGaussian.map (fun x : RealSeq => x + c)) (prefixRestrict n ⁻¹' t)
      = ∫⁻ x in prefixRestrict n ⁻¹' t,
          ENNReal.ofReal (cmDensityProcess c n x) ∂stdSeqGaussian := by
  have hprefix : Measurable (prefixRestrict n) := measurable_prefixRestrict n
  have hfdens : Measurable
      (fun y : PrefixSpace n => ENNReal.ofReal (finiteCmDensity (prefixRestrict n c) y)) := by
    exact (measurable_finiteCmDensity (prefixRestrict n c)).ennreal_ofReal
  calc
    (stdSeqGaussian.map (fun x : RealSeq => x + c)) (prefixRestrict n ⁻¹' t)
        = ((stdSeqGaussian.map (fun x : RealSeq => x + c)).map (prefixRestrict n)) t := by
            rw [Measure.map_apply hprefix ht]
    _ = ((stdGaussian (Finset.Iic n)).map
          (fun y : PrefixSpace n => y + prefixRestrict n c)) t := by
            rw [stdSeqGaussian_map_add_map_prefixRestrict]
    _ = ((stdGaussian (Finset.Iic n)).withDensity
          (fun y : PrefixSpace n => ENNReal.ofReal
            (finiteCmDensity (prefixRestrict n c) y))) t := by
            rw [stdGaussian_map_add_eq_withDensity_finiteCmDensity]
    _ = ∫⁻ y in t, ENNReal.ofReal (finiteCmDensity (prefixRestrict n c) y)
          ∂stdGaussian (Finset.Iic n) := by
            rw [withDensity_apply _ ht]
    _ = ∫⁻ y in t, ENNReal.ofReal (finiteCmDensity (prefixRestrict n c) y)
          ∂(stdSeqGaussian.map (prefixRestrict n)) := by
            rw [stdSeqGaussian_map_prefixRestrict]
    _ = ∫⁻ x in prefixRestrict n ⁻¹' t,
          ENNReal.ofReal (finiteCmDensity (prefixRestrict n c) (prefixRestrict n x))
          ∂stdSeqGaussian := by
            rw [setLIntegral_map ht hfdens hprefix]
    _ = ∫⁻ x in prefixRestrict n ⁻¹' t,
          ENNReal.ofReal (cmDensityProcess c n x) ∂stdSeqGaussian := by
            simp [finiteCmDensity_prefixRestrict]

/-- Local density identity on every set measurable with respect to the prefix filtration.
This is the interface expected by the martingale absolute-continuity criterion. -/
theorem map_add_eq_lintegral_cmDensityProcess (c : RealSeq) (n : ℕ) {s : Set RealSeq}
    (hs : MeasurableSet[prefixFiltration n] s) :
    (stdSeqGaussian.map (fun x : RealSeq => x + c)) s
      = ∫⁻ x in s, ENNReal.ofReal (cmDensityProcess c n x) ∂stdSeqGaussian := by
  change MeasurableSet[MeasurableSpace.comap (prefixRestrict n) inferInstance] s at hs
  rcases hs with ⟨t, ht, rfl⟩
  exact map_add_eq_lintegral_cmDensityProcess_preimage c n ht

/-- Finite-dimensional Cameron--Martin densities are strictly positive. -/
theorem finiteCmDensity_pos {ι : Type*} [Fintype ι] (h : ι → ℝ) (x : ι → ℝ) :
    0 < finiteCmDensity h x := by
  unfold finiteCmDensity
  exact Real.exp_pos _

/-- Pointwise square identity for the finite-dimensional Cameron--Martin density.  The
square of the `h`-density is a finite constant times the `2h`-density.  This avoids a
separate Gaussian MGF proof in the L²-bound step. -/
theorem finiteCmDensity_sq_eq_const_mul_two {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (x : ι → ℝ) :
    finiteCmDensity h x ^ 2 =
      Real.exp (∑ i, h i ^ 2) * finiteCmDensity (fun i => 2 * h i) x := by
  classical
  rw [finiteCmDensity_eq_exp_sum, finiteCmDensity_eq_exp_sum]
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- `ℝ≥0∞` form of `finiteCmDensity_sq_eq_const_mul_two`. -/
theorem ofReal_finiteCmDensity_sq_eq_const_mul_two {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (x : ι → ℝ) :
    ENNReal.ofReal (finiteCmDensity h x) ^ 2 =
      ENNReal.ofReal (Real.exp (∑ i, h i ^ 2)) *
        ENNReal.ofReal (finiteCmDensity (fun i => 2 * h i) x) := by
  rw [sq, ← ENNReal.ofReal_mul (le_of_lt (finiteCmDensity_pos h x))]
  rw [show finiteCmDensity h x * finiteCmDensity h x = finiteCmDensity h x ^ 2 by rw [sq]]
  rw [finiteCmDensity_sq_eq_const_mul_two]
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- Exact finite-dimensional L² moment of the Cameron--Martin density. -/
theorem lintegral_sq_finiteCmDensity {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    ∫⁻ x, ENNReal.ofReal (finiteCmDensity h x) ^ 2 ∂stdGaussian ι
      = ENNReal.ofReal (Real.exp (∑ i, h i ^ 2)) := by
  classical
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (∑ i, h i ^ 2))
  let f2 : (ι → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (finiteCmDensity (fun i => 2 * h i) x)
  have hf2 : Measurable f2 := by
    unfold f2
    fun_prop
  have hmass : ∫⁻ x, f2 x ∂stdGaussian ι = 1 := by
    rw [← setLIntegral_univ]
    change ∫⁻ x in Set.univ, ENNReal.ofReal (finiteCmDensity (fun i => 2 * h i) x)
        ∂stdGaussian ι = 1
    rw [← withDensity_apply _ MeasurableSet.univ]
    rw [← stdGaussian_map_add_eq_withDensity_finiteCmDensity (fun i : ι => 2 * h i)]
    haveI : IsProbabilityMeasure
        ((stdGaussian ι).map (fun x : ι → ℝ => x + fun i => 2 * h i)) :=
      Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable
        (fun x : ι → ℝ => x + fun i => 2 * h i) (stdGaussian ι))
    simp
  calc
    ∫⁻ x, ENNReal.ofReal (finiteCmDensity h x) ^ 2 ∂stdGaussian ι
        = ∫⁻ x, C * f2 x ∂stdGaussian ι := by
            refine lintegral_congr fun x => ?_
            change ENNReal.ofReal (finiteCmDensity h x) ^ 2 =
              ENNReal.ofReal (Real.exp (∑ i, h i ^ 2)) *
                ENNReal.ofReal (finiteCmDensity (fun i => 2 * h i) x)
            exact ofReal_finiteCmDensity_sq_eq_const_mul_two h x
    _ = C * ∫⁻ x, f2 x ∂stdGaussian ι := by
            rw [lintegral_const_mul _ hf2]
    _ = ENNReal.ofReal (Real.exp (∑ i, h i ^ 2)) := by
            rw [hmass]
            simp [C]

/-- Exact finite-prefix L² moment of the sequence Cameron--Martin density process. -/
theorem lintegral_sq_cmDensityProcess_exact (c : RealSeq) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (cmDensityProcess c n x) ^ 2 ∂stdSeqGaussian
      = ENNReal.ofReal (Real.exp (∑ i : Finset.Iic n, c i ^ 2)) := by
  classical
  let f : PrefixSpace n → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (finiteCmDensity (prefixRestrict n c) y) ^ 2
  have hf : Measurable f := by
    unfold f
    fun_prop
  calc
    ∫⁻ x, ENNReal.ofReal (cmDensityProcess c n x) ^ 2 ∂stdSeqGaussian
        = ∫⁻ x, f (prefixRestrict n x) ∂stdSeqGaussian := by
            refine lintegral_congr fun x => ?_
            unfold f
            rw [finiteCmDensity_prefixRestrict]
    _ = ∫⁻ y, f y ∂(stdSeqGaussian.map (prefixRestrict n)) := by
            rw [lintegral_map hf (measurable_prefixRestrict n)]
    _ = ∫⁻ y, f y ∂stdGaussian (Finset.Iic n) := by
            rw [stdSeqGaussian_map_prefixRestrict]
    _ = ENNReal.ofReal (Real.exp (∑ i : Finset.Iic n, c i ^ 2)) := by
            unfold f
            simpa using lintegral_sq_finiteCmDensity (prefixRestrict n c)

/-- Prefix square sums are twice the corresponding prefix Cameron--Martin energy. -/
theorem prefix_square_sum_eq_two_mul_cmPrefixEnergy (c : RealSeq) (n : ℕ) :
    (∑ i : Finset.Iic n, c i ^ 2) = 2 * cmPrefixEnergy c n := by
  rw [cmPrefixEnergy_eq_cmPartialEnergy_succ, cmPartialEnergy]
  calc
    (∑ i : Finset.Iic n, c i ^ 2)
        = (Finset.Iic n).sum (fun i => c i ^ 2) := by
          simpa using
            (Finset.sum_attach (s := Finset.Iic n) (f := fun i : ℕ => c i ^ 2))
    _ = (Finset.range (n + 1)).sum (fun i => c i ^ 2) := by
          rw [sum_Iic_eq_sum_range_succ]
    _ = 2 * (2⁻¹ * (Finset.range (n + 1)).sum (fun i => c i ^ 2)) := by
          ring

/-- Prefix energies are monotone in the prefix length. -/
theorem monotone_cmPrefixEnergy (c : RealSeq) : Monotone (cmPrefixEnergy c) := by
  exact monotone_nat_of_le_succ (cmPrefixEnergy_le_succ c)

/-- Under square summability, every finite-prefix energy is bounded by the total energy. -/
theorem cmPrefixEnergy_le_total_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) (n : ℕ) :
    cmPrefixEnergy c n ≤ cmTotalEnergy c := by
  have hconv := cmPrefixEnergy_tendsto_total_of_summable c hsum
  have hmono := monotone_cmPrefixEnergy c
  exact ge_of_tendsto hconv (eventually_atTop.2 ⟨n, fun m hm => hmono hm⟩)

/-- Uniform L² bound for the finite-prefix density process under square summability.
This is `PLAN_CONTINUUM_CLOSURE.md` M2.7. -/
theorem lintegral_sq_cmDensityProcess_le (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    ∀ n, ∫⁻ x, ENNReal.ofReal (cmDensityProcess c n x) ^ 2 ∂stdSeqGaussian
      ≤ ENNReal.ofReal (Real.exp (2 * cmTotalEnergy c)) := by
  intro n
  rw [lintegral_sq_cmDensityProcess_exact]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  calc
    (∑ i : Finset.Iic n, c i ^ 2) = 2 * cmPrefixEnergy c n :=
      prefix_square_sum_eq_two_mul_cmPrefixEnergy c n
    _ ≤ 2 * cmTotalEnergy c := by
      gcongr
      exact cmPrefixEnergy_le_total_of_summable c hsum n

end ForMathlib.MeasureTheory
