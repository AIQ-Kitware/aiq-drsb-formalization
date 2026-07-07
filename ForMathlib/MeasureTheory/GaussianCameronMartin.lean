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

end ForMathlib.MeasureTheory
