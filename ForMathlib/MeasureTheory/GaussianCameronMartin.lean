/-
# Infinite-dimensional Cameron-Martin staging for iid Gaussian sequences

This file starts the dependency queue in `PLAN_CONTINUUM_CLOSURE.md` for the
sequence-model Cameron-Martin/Kakutani theorem.  The goal theorem is the iid
sequence-coordinate identity

  `KL((stdSeqGaussian).map (· + c) || stdSeqGaussian) = 1/2 * tsum (c n)^2`

for square-summable `c`.  This file intentionally focuses on the stable
finite-prefix marginal layer first: the canonical product law, its prefix
marginals, shift/restriction commutation, the finite-prefix shifted marginal,
and the real finite-prefix density process.

The filtration/generation layer is already available separately via
`(iSup_comap_frestrictLe_eq_pi (ι := ℕ) (α := fun _ : ℕ => ℝ))` and the `Preorder.frestrictLe`-based construction
used in `PathEmbedding.lean`; we keep this file on the exact `Finset.restrict`
shape expected by `Measure.infinitePi_map_restrict`.
-/
import ForMathlib.MeasureTheory.GaussianEntropy
import ForMathlib.MeasureTheory.KLDataProcessing
import ForMathlib.MeasureTheory.PiWithDensity
import ForMathlib.MeasureTheory.AbsoluteContinuityMartingale

open MeasureTheory Real InformationTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace ForMathlib.MeasureTheory

/-- The ambient sequence-coordinate space used for the sequence-model
Cameron-Martin/Kakutani staging layer. -/
abbrev RealSeq : Type := ℕ → ℝ

/-- The first `n + 1` coordinates, written as a function space on the lower interval
`Finset.Iic n`. -/
abbrev PrefixSpace (n : ℕ) : Type := Finset.Iic n → ℝ

/-- Restriction to the first `n + 1` coordinates, in the exact form consumed by
`Measure.infinitePi_map_restrict`. -/
abbrev prefixRestrict (n : ℕ) : RealSeq → PrefixSpace n :=
  (Finset.Iic n).restrict

/-- The canonical iid standard-Gaussian sequence law on `ℕ → ℝ`.  This is the
sequence-coordinate reference measure for the deterministic Cameron-Martin/Kakutani
closure plan. -/
noncomputable def stdSeqGaussian : Measure RealSeq :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure stdSeqGaussian := by
  unfold stdSeqGaussian
  infer_instance

/-- The prefix-restriction map is measurable. -/
theorem measurable_prefixRestrict (n : ℕ) : Measurable (prefixRestrict n) := by
  unfold prefixRestrict
  exact (Finset.Iic n).measurable_restrict

/-- Deterministic translation of the sequence-coordinate space is measurable. -/
theorem measurable_shift (c : RealSeq) : Measurable (fun x : RealSeq => x + c) := by
  fun_prop

/-- Prefix marginals of the iid sequence model are the corresponding finite-dimensional
standard Gaussian laws.  This is `PLAN_CONTINUUM_CLOSURE.md` M2.4. -/
theorem stdSeqGaussian_map_prefixRestrict (n : ℕ) :
    stdSeqGaussian.map (prefixRestrict n) = stdGaussian (Finset.Iic n) := by
  unfold stdSeqGaussian stdGaussian prefixRestrict
  simpa using
    (Measure.infinitePi_map_restrict (μ := fun _ : ℕ => gaussianReal 0 1)
      (I := Finset.Iic n))

/-- Backwards-compatible name for the prefix-marginal theorem. -/
theorem stdSeqGaussian_map_frestrictLe (n : ℕ) :
    stdSeqGaussian.map (prefixRestrict n) = stdGaussian (Finset.Iic n) :=
  stdSeqGaussian_map_prefixRestrict n

/-- Mathlib's order-prefix restriction spelling is extensionally the same map as the
`Finset.restrict` spelling used by `Measure.infinitePi_map_restrict`.  Keeping this as a
separate bridge lets the finite-prefix API use the exact `Finset.restrict` theorem while
the martingale/KL convergence API can keep using `Preorder.frestrictLe`. -/
theorem preorder_frestrictLe_eq_prefixRestrict (n : ℕ) :
    (Preorder.frestrictLe n : RealSeq → PrefixSpace n) = prefixRestrict n := by
  funext x i
  rfl

/-- Restricting a pointwise shift is the same as shifting the restriction. -/
theorem prefixRestrict_add (c : RealSeq) (n : ℕ) (x : RealSeq) :
    prefixRestrict n (x + c) = prefixRestrict n x + prefixRestrict n c := by
  funext i
  rfl

/-- Backwards-compatible name for the shift/restriction commutation lemma. -/
theorem frestrictLe_add (c : RealSeq) (n : ℕ) (x : RealSeq) :
    prefixRestrict n (x + c) = prefixRestrict n x + prefixRestrict n c :=
  prefixRestrict_add c n x

/-- The shifted sequence law, projected to a finite prefix, is the finite-dimensional
standard Gaussian shifted by the restricted vector.  This is the finite-grid marginal
identity used by M2.5/M3.1. -/
theorem stdSeqGaussian_map_add_map_prefixRestrict (c : RealSeq) (n : ℕ) :
    (stdSeqGaussian.map (fun x : RealSeq => x + c)).map (prefixRestrict n)
      = (stdGaussian (Finset.Iic n)).map
        (fun x : PrefixSpace n => x + prefixRestrict n c) := by
  have hshift : Measurable (fun x : RealSeq => x + c) := by fun_prop
  have hprefix : Measurable (prefixRestrict n) := by
    unfold prefixRestrict
    exact (Finset.Iic n).measurable_restrict
  have hshift_fin : Measurable (fun x : PrefixSpace n => x + prefixRestrict n c) := by fun_prop
  have hcomp : (prefixRestrict n) ∘ (fun x : RealSeq => x + c)
      = (fun x : PrefixSpace n => x + prefixRestrict n c) ∘ (prefixRestrict n) := by
    funext x
    exact prefixRestrict_add c n x
  calc (stdSeqGaussian.map (fun x : RealSeq => x + c)).map (prefixRestrict n)
      = stdSeqGaussian.map ((prefixRestrict n) ∘ (fun x : RealSeq => x + c)) := by
          rw [Measure.map_map hprefix hshift]
    _ = stdSeqGaussian.map
          ((fun x : PrefixSpace n => x + prefixRestrict n c) ∘ (prefixRestrict n)) := by
          rw [hcomp]
    _ = (stdSeqGaussian.map (prefixRestrict n)).map
          (fun x : PrefixSpace n => x + prefixRestrict n c) := by
          rw [Measure.map_map hshift_fin hprefix]
    _ = (stdGaussian (Finset.Iic n)).map
          (fun x : PrefixSpace n => x + prefixRestrict n c) := by
          rw [stdSeqGaussian_map_prefixRestrict]

/-- Backwards-compatible name for the shifted finite-prefix marginal theorem. -/
theorem stdSeqGaussian_map_add_map_frestrictLe (c : RealSeq) (n : ℕ) :
    (stdSeqGaussian.map (fun x : RealSeq => x + c)).map (prefixRestrict n)
      = (stdGaussian (Finset.Iic n)).map
        (fun x : PrefixSpace n => x + prefixRestrict n c) :=
  stdSeqGaussian_map_add_map_prefixRestrict c n

/-- Finite-prefix Cameron--Martin energy for the deterministic shift `c`, restricted to
the first `n + 1` sequence coordinates.  This is the finite-dimensional quantity that
converges to `½‖c‖²` in the eventual sequence-model theorem. -/
noncomputable def cmPrefixEnergy (c : RealSeq) (n : ℕ) : ℝ :=
  2⁻¹ * ∑ i : Finset.Iic n, (prefixRestrict n c i) ^ 2

/-- Finite-prefix Cameron--Martin energy is nonnegative. -/
theorem cmPrefixEnergy_nonneg (c : RealSeq) (n : ℕ) :
    0 ≤ cmPrefixEnergy c n := by
  unfold cmPrefixEnergy
  positivity

/-- Total sequence Cameron--Martin energy, written as one half of the square series.
This is the target value for the sequence-model Cameron--Martin identity when the
shift vector is square-summable. -/
noncomputable def cmTotalEnergy (c : RealSeq) : ℝ :=
  2⁻¹ * ∑' n : ℕ, c n ^ 2

/-- Range-indexed partial Cameron--Martin energies.  This spelling intentionally uses
`Finset.sum` directly, rather than big-operator `in` notation, so it is stable across the
parser/API differences that showed up in the previous source pass.  It sums the first `n`
coordinates, i.e. indices in `Finset.range n`. -/
noncomputable def cmPartialEnergy (c : RealSeq) (n : ℕ) : ℝ :=
  2⁻¹ * (Finset.range n).sum (fun i => c i ^ 2)

/-- Total sequence Cameron--Martin energy is nonnegative. -/
theorem cmTotalEnergy_nonneg (c : RealSeq) :
    0 ≤ cmTotalEnergy c := by
  unfold cmTotalEnergy
  exact mul_nonneg (by positivity) (tsum_nonneg (fun n => sq_nonneg (c n)))

/-- Range-indexed partial Cameron--Martin energies are nonnegative. -/
theorem cmPartialEnergy_nonneg (c : RealSeq) (n : ℕ) :
    0 ≤ cmPartialEnergy c n := by
  unfold cmPartialEnergy
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => sq_nonneg (c i)))

/-- The empty range has zero Cameron--Martin energy. -/
theorem cmPartialEnergy_zero (c : RealSeq) :
    cmPartialEnergy c 0 = 0 := by
  simp [cmPartialEnergy]

/-- Successor equation for range-indexed partial Cameron--Martin energies. -/
theorem cmPartialEnergy_succ (c : RealSeq) (n : ℕ) :
    cmPartialEnergy c (n + 1) = cmPartialEnergy c n + 2⁻¹ * c n ^ 2 := by
  unfold cmPartialEnergy
  rw [Finset.sum_range_succ]
  ring

/-- Range-indexed partial Cameron--Martin energies are increasing one step at a time. -/
theorem cmPartialEnergy_le_succ (c : RealSeq) (n : ℕ) :
    cmPartialEnergy c n ≤ cmPartialEnergy c (n + 1) := by
  rw [cmPartialEnergy_succ]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg (c n)))

/-- Pure-series convergence of range-indexed partial Cameron--Martin energies.
This is the square-summable side of the eventual sequence-model identity; a later bridge
identifies the `Finset.Iic n` prefix energy with these shifted range partial sums. -/
theorem cmPartialEnergy_tendsto_total_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    Tendsto (cmPartialEnergy c) atTop (nhds (cmTotalEnergy c)) := by
  unfold cmPartialEnergy cmTotalEnergy
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((hsum.hasSum.tendsto_sum_nat).const_mul (2⁻¹))

/-- Lower intervals in `ℕ` have the same sum as the corresponding successor range.
This small finite-set bridge keeps the sequence-model Cameron--Martin file from depending
on a particular spelling of the Mathlib `Iic = range` theorem. -/
theorem sum_Iic_eq_sum_range_succ (f : ℕ → ℝ) (n : ℕ) :
    (Finset.Iic n).sum f = (Finset.range (n + 1)).sum f := by
  have hIic : Finset.Iic n = Finset.range (n + 1) := by
    ext i
    simp
  rw [hIic]

/-- The `Finset.Iic n` finite-prefix energy is the same as the range-indexed
partial energy through coordinate `n`, i.e. the first `n + 1` coordinates.  This
is the pure finite-set bridge between the Gaussian-prefix layer and the ordinary
series API on `ℕ`. -/
theorem cmPrefixEnergy_eq_cmPartialEnergy_succ (c : RealSeq) (n : ℕ) :
    cmPrefixEnergy c n = cmPartialEnergy c (n + 1) := by
  unfold cmPrefixEnergy cmPartialEnergy prefixRestrict
  calc
    2⁻¹ * (∑ i : Finset.Iic n, c ↑i ^ 2)
        = 2⁻¹ * (Finset.Iic n).sum (fun i => c i ^ 2) := by
          congr 1
          simpa using
            (Finset.sum_attach (s := Finset.Iic n) (f := fun i : ℕ => c i ^ 2))
    _ = 2⁻¹ * (Finset.range (n + 1)).sum (fun i => c i ^ 2) := by
          rw [sum_Iic_eq_sum_range_succ]

/-- Finite-prefix energies are monotone in the prefix length. -/
theorem cmPrefixEnergy_le_succ (c : RealSeq) (n : ℕ) :
    cmPrefixEnergy c n ≤ cmPrefixEnergy c (n + 1) := by
  rw [cmPrefixEnergy_eq_cmPartialEnergy_succ c n,
    cmPrefixEnergy_eq_cmPartialEnergy_succ c (n + 1)]
  exact cmPartialEnergy_le_succ c (n + 1)

/-- If range-indexed partial energies are unbounded, then the finite-prefix energies are
unbounded as well.  The only missing range index is `0`, whose partial energy is `0`; all
successor range indices are prefix energies by `cmPrefixEnergy_eq_cmPartialEnergy_succ`. -/
theorem not_bddAbove_cmPrefixEnergy_of_not_bddAbove_cmPartialEnergy (c : RealSeq)
    (hunbdd : ¬ BddAbove (Set.range (cmPartialEnergy c))) :
    ¬ BddAbove (Set.range (cmPrefixEnergy c)) := by
  intro hpre
  rcases hpre with ⟨B, hB⟩
  refine hunbdd ⟨max B 0, ?_⟩
  intro y hy
  rcases hy with ⟨n, rfl⟩
  cases n with
  | zero =>
      rw [cmPartialEnergy_zero]
      exact le_max_right B 0
  | succ n =>
      rw [← cmPrefixEnergy_eq_cmPartialEnergy_succ c n]
      exact le_trans (hB ⟨n, rfl⟩) (le_max_left B 0)

/-- The finite-prefix KL identity obtained by projecting the shifted iid sequence model
to the first `n + 1` coordinates.  This is the KL-facing version of the M2.4 prefix
marginal brick: after projection, the problem is exactly the already-proved
finite-dimensional Gaussian Cameron--Martin theorem `klDiv_stdGaussian_map_add`. -/
theorem klDiv_stdSeqGaussian_shift_prefix (c : RealSeq) (n : ℕ) :
    klDiv ((stdSeqGaussian.map (fun x : RealSeq => x + c)).map (prefixRestrict n))
        (stdSeqGaussian.map (prefixRestrict n))
      = ENNReal.ofReal (cmPrefixEnergy c n) := by
  rw [stdSeqGaussian_map_add_map_prefixRestrict, stdSeqGaussian_map_prefixRestrict]
  unfold cmPrefixEnergy
  simpa using (klDiv_stdGaussian_map_add (prefixRestrict n c))

/-- Real-valued form of `klDiv_stdSeqGaussian_shift_prefix`. -/
theorem klDiv_stdSeqGaussian_shift_prefix_toReal (c : RealSeq) (n : ℕ) :
    (klDiv ((stdSeqGaussian.map (fun x : RealSeq => x + c)).map (prefixRestrict n))
        (stdSeqGaussian.map (prefixRestrict n))).toReal
      = cmPrefixEnergy c n := by
  rw [klDiv_stdSeqGaussian_shift_prefix]
  exact ENNReal.toReal_ofReal (cmPrefixEnergy_nonneg c n)

/-- Data processing gives the finite-prefix Cameron--Martin lower bound on the full
sequence-space KL.  This is the KL `ℝ≥0∞` half of the eventual sequence-model theorem:
every finite prefix energy is bounded above by the full shifted-sequence divergence whenever the
shifted sequence law is absolutely continuous with respect to the reference sequence law. -/
theorem ofReal_cmPrefixEnergy_le_shift_kl (c : RealSeq) (n : ℕ)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian) :
    ENNReal.ofReal (cmPrefixEnergy c n)
      ≤ klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian := by
  have hshift : Measurable (fun x : RealSeq => x + c) := measurable_shift c
  haveI : IsProbabilityMeasure (stdSeqGaussian.map (fun x : RealSeq => x + c)) :=
    Measure.isProbabilityMeasure_map hshift.aemeasurable
  have hle := klDiv_map_le (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian
    hac (prefixRestrict n) (measurable_prefixRestrict n)
  rw [klDiv_stdSeqGaussian_shift_prefix] at hle
  exact hle

/-- Real-valued version of `ofReal_cmPrefixEnergy_le_shift_kl`.  This is the form consumed by
`le_toReal_klDiv_of_map_tendsto`-style arguments and is also useful for showing that finite full
KL forces uniformly bounded prefix energies. -/
theorem cmPrefixEnergy_le_shift_kl_toReal (c : RealSeq) (n : ℕ)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hfin : klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤) :
    cmPrefixEnergy c n
      ≤ (klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian).toReal := by
  have hshift : Measurable (fun x : RealSeq => x + c) := measurable_shift c
  haveI : IsProbabilityMeasure (stdSeqGaussian.map (fun x : RealSeq => x + c)) :=
    Measure.isProbabilityMeasure_map hshift.aemeasurable
  have hle := toReal_klDiv_map_le (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian
    hac (prefixRestrict n) (measurable_prefixRestrict n) hfin
  rw [klDiv_stdSeqGaussian_shift_prefix_toReal] at hle
  exact hle

/-- Prefix KL identity using Mathlib's `Preorder.frestrictLe` spelling of the same finite
restriction map.  This is a convenience bridge for the martingale-convergence theorem
`klDiv_map_tendsto`, whose product-filtration generator is stated for `frestrictLe`. -/
theorem klDiv_stdSeqGaussian_shift_frestrictLe (c : RealSeq) (n : ℕ) :
    klDiv ((stdSeqGaussian.map (fun x : RealSeq => x + c)).map
        (Preorder.frestrictLe n))
        (stdSeqGaussian.map (Preorder.frestrictLe n))
      = ENNReal.ofReal (cmPrefixEnergy c n) := by
  rw [preorder_frestrictLe_eq_prefixRestrict n]
  exact klDiv_stdSeqGaussian_shift_prefix c n

/-- Real-valued prefix KL identity using the `Preorder.frestrictLe` spelling. -/
theorem klDiv_stdSeqGaussian_shift_frestrictLe_toReal (c : RealSeq) (n : ℕ) :
    (klDiv ((stdSeqGaussian.map (fun x : RealSeq => x + c)).map
        (Preorder.frestrictLe n))
        (stdSeqGaussian.map (Preorder.frestrictLe n))).toReal
      = cmPrefixEnergy c n := by
  rw [preorder_frestrictLe_eq_prefixRestrict n]
  exact klDiv_stdSeqGaussian_shift_prefix_toReal c n

/-- The finite-prefix energies, embedded as `ℝ≥0∞`, converge to the full sequence-space KL
whenever the shifted sequence law is absolutely continuous with respect to the iid Gaussian
reference.  This is the martingale-convergence half that upgrades the prefix identities from
finite-dimensional checks to the countable product model. -/
theorem ofReal_cmPrefixEnergy_tendsto_shift_kl (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian) :
    Tendsto (fun n => ENNReal.ofReal (cmPrefixEnergy c n)) atTop
      (nhds (klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian)) := by
  have hshift : Measurable (fun x : RealSeq => x + c) := measurable_shift c
  haveI : IsProbabilityMeasure (stdSeqGaussian.map (fun x : RealSeq => x + c)) :=
    Measure.isProbabilityMeasure_map hshift.aemeasurable
  let ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace RealSeq) :=
    { seq := fun n => MeasurableSpace.comap
        (Preorder.frestrictLe n) inferInstance
      mono' := by
        intro n m hnm
        calc MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance
            = MeasurableSpace.comap (Preorder.frestrictLe m)
                (MeasurableSpace.comap (Preorder.frestrictLe₂ hnm)
                  inferInstance) := by
              rw [MeasurableSpace.comap_comp, Preorder.frestrictLe₂_comp_frestrictLe]
          _ ≤ MeasurableSpace.comap (Preorder.frestrictLe m) inferInstance :=
              MeasurableSpace.comap_mono (Preorder.measurable_frestrictLe₂ hnm).comap_le
      le' := fun n => (Preorder.measurable_frestrictLe n).comap_le }
  have htend := klDiv_map_tendsto
    (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian hac
    (fun n => Preorder.frestrictLe n)
    (fun n => Preorder.measurable_frestrictLe n) ℱ (fun _ => rfl)
    (iSup_comap_frestrictLe_eq_pi (ι := ℕ) (α := fun _ : ℕ => ℝ))
  simpa [klDiv_stdSeqGaussian_shift_frestrictLe] using htend

/-- Real-valued version of `ofReal_cmPrefixEnergy_tendsto_shift_kl` for the finite-KL case. -/
theorem cmPrefixEnergy_tendsto_shift_kl_toReal (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hfin : klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤) :
    Tendsto (fun n => cmPrefixEnergy c n) atTop
      (nhds (klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian).toReal) := by
  have hshift : Measurable (fun x : RealSeq => x + c) := measurable_shift c
  haveI : IsProbabilityMeasure (stdSeqGaussian.map (fun x : RealSeq => x + c)) :=
    Measure.isProbabilityMeasure_map hshift.aemeasurable
  let ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace RealSeq) :=
    { seq := fun n => MeasurableSpace.comap
        (Preorder.frestrictLe n) inferInstance
      mono' := by
        intro n m hnm
        calc MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance
            = MeasurableSpace.comap (Preorder.frestrictLe m)
                (MeasurableSpace.comap (Preorder.frestrictLe₂ hnm)
                  inferInstance) := by
              rw [MeasurableSpace.comap_comp, Preorder.frestrictLe₂_comp_frestrictLe]
          _ ≤ MeasurableSpace.comap (Preorder.frestrictLe m) inferInstance :=
              MeasurableSpace.comap_mono (Preorder.measurable_frestrictLe₂ hnm).comap_le
      le' := fun n => (Preorder.measurable_frestrictLe n).comap_le }
  have htend := klDiv_map_tendsto_toReal
    (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian hac hfin
    (fun n => Preorder.frestrictLe n)
    (fun n => Preorder.measurable_frestrictLe n) ℱ (fun _ => rfl)
    (iSup_comap_frestrictLe_eq_pi (ι := ℕ) (α := fun _ : ℕ => ℝ))
  simpa [klDiv_stdSeqGaussian_shift_frestrictLe_toReal] using htend

/-- Abstract uniqueness wrapper for the sequence-model Cameron--Martin identity in `ℝ≥0∞`.
If an independent argument identifies the limit of finite prefix energies, then the full
sequence-space KL has the same value.  Downstream, the independent argument is the pure
series/tail calculation `cmPrefixEnergy c n → ½ * ∑' k, c k ^ 2`. -/
theorem shift_kl_eq_of_ofReal_cmPrefixEnergy_tendsto (c : RealSeq) (L : ℝ)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hconv : Tendsto (fun n => ENNReal.ofReal (cmPrefixEnergy c n)) atTop
      (nhds (ENNReal.ofReal L))) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian = ENNReal.ofReal L := by
  exact (tendsto_nhds_unique hconv (ofReal_cmPrefixEnergy_tendsto_shift_kl c hac)).symm

/-- Real-valued abstract uniqueness wrapper for the sequence-model Cameron--Martin identity.
This is the same statement as `shift_kl_eq_of_ofReal_cmPrefixEnergy_tendsto`, phrased after
`toReal` under a finite-KL hypothesis. -/
theorem shift_kl_toReal_eq_of_cmPrefixEnergy_tendsto (c : RealSeq) (L : ℝ)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hfin : klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤)
    (hconv : Tendsto (fun n => cmPrefixEnergy c n) atTop (nhds L)) :
    (klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian).toReal = L := by
  exact (tendsto_nhds_unique hconv (cmPrefixEnergy_tendsto_shift_kl_toReal c hac hfin)).symm

/-- The full shifted-sequence KL is an upper bound for the supremum of all finite-prefix
Cameron--Martin energies, in `ℝ≥0∞`.  This packages the per-prefix data-processing
bounds into the exact shape needed by the eventual Kakutani/Cameron--Martin converse:
finite full KL forces uniformly bounded finite prefix energies. -/
theorem iSup_ofReal_cmPrefixEnergy_le_shift_kl (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian) :
    (⨆ n : ℕ, ENNReal.ofReal (cmPrefixEnergy c n))
      ≤ klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian := by
  exact iSup_le (fun n => ofReal_cmPrefixEnergy_le_shift_kl c n hac)

/-- If the full shifted-sequence KL is finite, then the real finite-prefix energies are
bounded above.  This is the real-valued boundedness form consumed by later pure-series
arguments that turn bounded nonnegative prefix energies into square-summability of the
shift vector. -/
theorem cmPrefixEnergy_bddAbove_of_shift_kl_finite (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hfin : klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤) :
    BddAbove (Set.range (cmPrefixEnergy c)) := by
  refine ⟨(klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian).toReal, ?_⟩
  intro y hy
  rcases hy with ⟨n, rfl⟩
  exact cmPrefixEnergy_le_shift_kl_toReal c n hac hfin


/-- Finite-prefix KLs are always finite.  This packages the finite-dimensional Gaussian
identity into a form that is convenient for later `toReal` rewrites and sanity checks. -/
theorem klDiv_stdSeqGaussian_shift_prefix_ne_top (c : RealSeq) (n : ℕ) :
    klDiv ((stdSeqGaussian.map (fun x : RealSeq => x + c)).map (prefixRestrict n))
        (stdSeqGaussian.map (prefixRestrict n)) ≠ ⊤ := by
  simp [klDiv_stdSeqGaussian_shift_prefix]

/-- Finite-prefix KLs are strictly below `⊤`. -/
theorem klDiv_stdSeqGaussian_shift_prefix_lt_top (c : RealSeq) (n : ℕ) :
    klDiv ((stdSeqGaussian.map (fun x : RealSeq => x + c)).map (prefixRestrict n))
        (stdSeqGaussian.map (prefixRestrict n)) < ⊤ := by
  simp [klDiv_stdSeqGaussian_shift_prefix]

/-- Contrapositive form of `cmPrefixEnergy_bddAbove_of_shift_kl_finite`: under absolute
continuity, unbounded finite-prefix energies rule out finite full sequence-space KL. -/
theorem not_shift_kl_finite_of_not_bddAbove_cmPrefixEnergy (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hunbdd : ¬ BddAbove (Set.range (cmPrefixEnergy c))) :
    ¬ klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤ := by
  intro hfin
  exact hunbdd (cmPrefixEnergy_bddAbove_of_shift_kl_finite c hac hfin)

/-- Under absolute continuity, unbounded finite-prefix energies force the full
shifted-sequence KL to be infinite.  This is the KL-facing converse scaffold that later
pure-series work will connect to non-square-summability of the deterministic shift. -/
theorem shift_kl_eq_top_of_not_bddAbove_cmPrefixEnergy (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hunbdd : ¬ BddAbove (Set.range (cmPrefixEnergy c))) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian = ⊤ := by
  by_contra hfin
  exact hunbdd (cmPrefixEnergy_bddAbove_of_shift_kl_finite c hac hfin)

/-- If ordinary range partial energies are unbounded, then finite full shifted-sequence KL is
impossible under absolute continuity.  This is the series-facing converse wrapper. -/
theorem not_shift_kl_finite_of_not_bddAbove_cmPartialEnergy (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hunbdd : ¬ BddAbove (Set.range (cmPartialEnergy c))) :
    ¬ klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤ := by
  exact not_shift_kl_finite_of_not_bddAbove_cmPrefixEnergy c hac
    (not_bddAbove_cmPrefixEnergy_of_not_bddAbove_cmPartialEnergy c hunbdd)

/-- Under absolute continuity, unbounded ordinary range partial energies force the full
shifted-sequence KL to be infinite. -/
theorem shift_kl_eq_top_of_not_bddAbove_cmPartialEnergy (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hunbdd : ¬ BddAbove (Set.range (cmPartialEnergy c))) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian = ⊤ := by
  exact shift_kl_eq_top_of_not_bddAbove_cmPrefixEnergy c hac
    (not_bddAbove_cmPrefixEnergy_of_not_bddAbove_cmPartialEnergy c hunbdd)

/-- Finite-prefix Cameron--Martin energies converge to the total square-series energy
for square-summable shifts.  This transfers the already-proved range-sum convergence along
the finite-set bridge `cmPrefixEnergy_eq_cmPartialEnergy_succ`. -/
theorem cmPrefixEnergy_tendsto_total_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    Tendsto (fun n : ℕ => cmPrefixEnergy c n) atTop
      (nhds (cmTotalEnergy c)) := by
  have hpart : Tendsto (cmPartialEnergy c) atTop (nhds (cmTotalEnergy c)) :=
    cmPartialEnergy_tendsto_total_of_summable c hsum
  have hshift : Tendsto (fun n : ℕ => cmPartialEnergy c (n + 1)) atTop
      (nhds (cmTotalEnergy c)) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      ((Filter.tendsto_add_atTop_iff_nat 1).mpr hpart)
  simpa [cmPrefixEnergy_eq_cmPartialEnergy_succ] using hshift

/-- `ℝ≥0∞` version of finite-prefix convergence to the total square-series energy. -/
theorem ofReal_cmPrefixEnergy_tendsto_total_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (cmPrefixEnergy c n)) atTop
      (nhds (ENNReal.ofReal (cmTotalEnergy c))) := by
  exact (ENNReal.continuous_ofReal.tendsto (cmTotalEnergy c)).comp
    (cmPrefixEnergy_tendsto_total_of_summable c hsum)

/-- Finite full shifted-sequence KL forces the ordinary range-indexed partial
Cameron--Martin energies to be bounded. -/
theorem cmPartialEnergy_bddAbove_of_shift_kl_finite (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hfin : klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤) :
    BddAbove (Set.range (cmPartialEnergy c)) := by
  by_contra hunbdd
  exact (not_shift_kl_finite_of_not_bddAbove_cmPartialEnergy c hac hunbdd) hfin

/-- Specialized `ℝ≥0∞` uniqueness wrapper for the sequence-model Cameron--Martin identity
with target value `cmTotalEnergy`.  The remaining input is the pure bridge showing that
`ENNReal.ofReal (cmPrefixEnergy c n)` converges to `ENNReal.ofReal (cmTotalEnergy c)`. -/
theorem shift_kl_eq_of_ofReal_cmPrefixEnergy_tendsto_cmTotalEnergy (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hconv : Tendsto (fun n => ENNReal.ofReal (cmPrefixEnergy c n)) atTop
      (nhds (ENNReal.ofReal (cmTotalEnergy c)))) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian
      = ENNReal.ofReal (cmTotalEnergy c) := by
  exact shift_kl_eq_of_ofReal_cmPrefixEnergy_tendsto c (cmTotalEnergy c) hac hconv

/-- Specialized real-valued uniqueness wrapper for the sequence-model Cameron--Martin identity
with target value `cmTotalEnergy`, under finite full KL. -/
theorem shift_kl_toReal_eq_of_cmPrefixEnergy_tendsto_cmTotalEnergy (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hfin : klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤)
    (hconv : Tendsto (fun n => cmPrefixEnergy c n) atTop (nhds (cmTotalEnergy c))) :
    (klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian).toReal
      = cmTotalEnergy c := by
  exact shift_kl_toReal_eq_of_cmPrefixEnergy_tendsto c (cmTotalEnergy c) hac hfin hconv

/-- Square-summable sequence-model Cameron--Martin KL identity.  Under absolute
continuity of the shifted sequence law, the full shifted-sequence divergence is exactly
the total Cameron--Martin square-series energy. -/
theorem shift_kl_eq_cmTotalEnergy_of_summable (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian
      = ENNReal.ofReal (cmTotalEnergy c) := by
  exact shift_kl_eq_of_ofReal_cmPrefixEnergy_tendsto_cmTotalEnergy c hac
    (ofReal_cmPrefixEnergy_tendsto_total_of_summable c hsum)

/-- The square-summable shifted-sequence KL is finite under absolute continuity. -/
theorem shift_kl_ne_top_of_summable (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤ := by
  rw [shift_kl_eq_cmTotalEnergy_of_summable c hac hsum]
  simp

/-- Real-valued square-summable sequence-model Cameron--Martin KL identity. -/
theorem shift_kl_toReal_eq_cmTotalEnergy_of_summable (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    (klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian).toReal
      = cmTotalEnergy c := by
  rw [shift_kl_eq_cmTotalEnergy_of_summable c hac hsum]
  exact ENNReal.toReal_ofReal (cmTotalEnergy_nonneg c)

/-- Real-valued square-summable sequence-model Cameron--Martin KL identity, packaged
for callers that already have a finite-KL hypothesis in scope. -/
theorem shift_kl_toReal_eq_cmTotalEnergy_of_summable_of_finite (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (_hfin : klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    (klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian).toReal
      = cmTotalEnergy c := by
  exact shift_kl_toReal_eq_cmTotalEnergy_of_summable c hac hsum

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

/-- The prefix filtration generated by the finite restrictions exhausts the ambient product
measurable space. -/
theorem iSup_prefixFiltration_eq :
    (⨆ n, prefixFiltration n) = (inferInstance : MeasurableSpace RealSeq) := by
  change (⨆ n, MeasurableSpace.comap (prefixRestrict n) inferInstance) =
    (inferInstance : MeasurableSpace RealSeq)
  simp_rw [← preorder_frestrictLe_eq_prefixRestrict]
  exact (iSup_comap_frestrictLe_eq_pi (ι := ℕ) (α := fun _ : ℕ => ℝ))

/-- The finite-prefix Cameron--Martin density process is adapted to the prefix filtration. -/
theorem stronglyAdapted_cmDensityProcess (c : RealSeq) :
    StronglyAdapted prefixFiltration (cmDensityProcess c) := by
  intro n
  change StronglyMeasurable[prefixFiltration n] (cmDensityProcess c n)
  change StronglyMeasurable[MeasurableSpace.comap (prefixRestrict n) inferInstance]
    (cmDensityProcess c n)
  have hprefix : @Measurable RealSeq (PrefixSpace n)
      (MeasurableSpace.comap (prefixRestrict n) inferInstance) inferInstance
      (prefixRestrict n) := by
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hmeas : @Measurable RealSeq ℝ
      (MeasurableSpace.comap (prefixRestrict n) inferInstance) inferInstance
      (cmDensityProcess c n) := by
    have hcomp : @Measurable RealSeq ℝ
        (MeasurableSpace.comap (prefixRestrict n) inferInstance) inferInstance
        (fun x : RealSeq => finiteCmDensity (prefixRestrict n c) (prefixRestrict n x)) :=
      (measurable_finiteCmDensity (prefixRestrict n c)).comp hprefix
    convert hcomp using 1
    ext x
    exact finiteCmDensity_prefixRestrict c n x
  exact hmeas.stronglyMeasurable

/-- Square-summable deterministic shifts are absolutely continuous with respect to the iid
standard Gaussian sequence law.  This is `PLAN_CONTINUUM_CLOSURE.md` M2.8. -/
theorem absolutelyContinuous_stdSeqGaussian_map_add_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian := by
  haveI : IsProbabilityMeasure (stdSeqGaussian.map (fun x : RealSeq => x + c)) :=
    Measure.isProbabilityMeasure_map (measurable_shift c).aemeasurable
  refine absolutelyContinuous_of_localDensity
    (μ := stdSeqGaussian.map (fun x : RealSeq => x + c))
    (ν := stdSeqGaussian)
    (ℱ := prefixFiltration)
    (hgen := iSup_prefixFiltration_eq)
    (Z := cmDensityProcess c)
    (hadapted := stronglyAdapted_cmDensityProcess c)
    (hnonneg := cmDensityProcess_nonneg c)
    (hdens := map_add_eq_lintegral_cmDensityProcess c)
    (hM := ENNReal.ofReal_ne_top)
    (hL2 := lintegral_sq_cmDensityProcess_le c hsum)

/-- Clean square-summable sequence-model Cameron--Martin KL identity, with absolute
continuity discharged by the local-density/L² route. -/
theorem klDiv_stdSeqGaussian_map_add_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian
      = ENNReal.ofReal (cmTotalEnergy c) := by
  exact shift_kl_eq_cmTotalEnergy_of_summable c
    (absolutelyContinuous_stdSeqGaussian_map_add_of_summable c hsum) hsum

/-- Finiteness of the clean square-summable sequence-model KL identity. -/
theorem klDiv_stdSeqGaussian_map_add_ne_top_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤ := by
  rw [klDiv_stdSeqGaussian_map_add_of_summable c hsum]
  exact ENNReal.ofReal_ne_top

/-- Real-valued clean square-summable sequence-model Cameron--Martin KL identity. -/
theorem toReal_klDiv_stdSeqGaussian_map_add_of_summable (c : RealSeq)
    (hsum : Summable (fun n : ℕ => c n ^ 2)) :
    (klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian).toReal
      = cmTotalEnergy c := by
  rw [klDiv_stdSeqGaussian_map_add_of_summable c hsum]
  exact ENNReal.toReal_ofReal (cmTotalEnergy_nonneg c)

end ForMathlib.MeasureTheory
