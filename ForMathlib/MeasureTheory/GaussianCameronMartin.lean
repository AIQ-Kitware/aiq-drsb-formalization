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
`iSup_comap_frestrictLe_eq_pi` and the `Preorder.frestrictLe`-based construction
used in `PathEmbedding.lean`; we keep this file on the exact `Finset.restrict`
shape expected by `Measure.infinitePi_map_restrict`.
-/
import ForMathlib.MeasureTheory.GaussianEntropy
import ForMathlib.MeasureTheory.KLDataProcessing
import ForMathlib.MeasureTheory.PiWithDensity
import ForMathlib.MeasureTheory.AbsoluteContinuityMartingale

open MeasureTheory Real InformationTheory ProbabilityTheory
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
