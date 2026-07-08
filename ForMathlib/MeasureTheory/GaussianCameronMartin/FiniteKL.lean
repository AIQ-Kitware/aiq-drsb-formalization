/-
# Sequence Gaussian Cameron--Martin: finite-prefix KL identities

This module contains the projected finite-dimensional KL identities and
data-processing lower bounds for iid Gaussian sequence shifts.
-/

import ForMathlib.MeasureTheory.GaussianCameronMartin.Energy

set_option autoImplicit false

open MeasureTheory Real InformationTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace ForMathlib.MeasureTheory

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

end ForMathlib.MeasureTheory
