/-
# Sequence Gaussian Cameron--Martin: basic product and prefix laws

This module contains the carrier, iid Gaussian reference law, finite-prefix
restriction API, and shifted finite-prefix marginal identities.
-/

import ForMathlib.MeasureTheory.GaussianEntropy
import ForMathlib.MeasureTheory.KLDataProcessing
import ForMathlib.MeasureTheory.PiWithDensity
import ForMathlib.MeasureTheory.AbsoluteContinuityMartingale

set_option autoImplicit false

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

end ForMathlib.MeasureTheory
