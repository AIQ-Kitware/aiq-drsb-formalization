/-
# Sequence Gaussian Cameron--Martin: infinite-product KL identities

This module contains the countable-product KL convergence, finite/infinite
dichotomy, and square-summable sequence Cameron--Martin identities that still
assume absolute continuity when needed.
-/

import ForMathlib.MeasureTheory.GaussianCameronMartin.FiniteKL

set_option autoImplicit false

open MeasureTheory Real InformationTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace ForMathlib.MeasureTheory

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

/-- If the range-indexed Cameron--Martin partial energies are bounded above, then the
underlying square series is summable.  This is the pure series/order-theory converse
bridge: bounded nonnegative partial sums converge by monotone convergence, and the
nonnegative-series `HasSum` criterion turns that limit into summability. -/
theorem summable_sq_of_bddAbove_cmPartialEnergy (c : RealSeq)
    (hbdd : BddAbove (Set.range (cmPartialEnergy c))) :
    Summable (fun n : ℕ => c n ^ 2) := by
  have hmono_sums : Monotone (fun n : ℕ => (Finset.range n).sum (fun i => c i ^ 2)) := by
    exact monotone_nat_of_le_succ (fun n => by
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (sq_nonneg (c n)))
  have hbdd_sums : BddAbove
      (Set.range (fun n : ℕ => (Finset.range n).sum (fun i => c i ^ 2))) := by
    rcases hbdd with ⟨B, hB⟩
    refine ⟨2 * B, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have henergy : cmPartialEnergy c n ≤ B := hB ⟨n, rfl⟩
    calc
      (Finset.range n).sum (fun i => c i ^ 2)
          = 2 * cmPartialEnergy c n := by
            unfold cmPartialEnergy
            ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left henergy (by norm_num)
  have hconv : Tendsto (fun n : ℕ => (Finset.range n).sum (fun i => c i ^ 2)) atTop
      (nhds (⨆ n : ℕ, (Finset.range n).sum (fun i => c i ^ 2))) :=
    tendsto_atTop_ciSup hmono_sums hbdd_sums
  have hhas : HasSum (fun n : ℕ => c n ^ 2)
      (⨆ n : ℕ, (Finset.range n).sum (fun i => c i ^ 2)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun n : ℕ => sq_nonneg (c n))
      (⨆ n : ℕ, (Finset.range n).sum (fun i => c i ^ 2))]
    exact hconv
  exact hhas.summable

/-- Non-square-summability forces the ordinary Cameron--Martin partial energies to be
unbounded.  This is the pure series bridge needed by the infinite-KL branch. -/
theorem not_bddAbove_cmPartialEnergy_of_not_summable (c : RealSeq)
    (hnsum : ¬ Summable (fun n : ℕ => c n ^ 2)) :
    ¬ BddAbove (Set.range (cmPartialEnergy c)) := by
  intro hbdd
  exact hnsum (summable_sq_of_bddAbove_cmPartialEnergy c hbdd)

/-- Under absolute continuity, non-square-summability rules out finite shifted-sequence KL. -/
theorem not_shift_kl_finite_of_not_summable_of_ac (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hnsum : ¬ Summable (fun n : ℕ => c n ^ 2)) :
    ¬ klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤ := by
  exact not_shift_kl_finite_of_not_bddAbove_cmPartialEnergy c hac
    (not_bddAbove_cmPartialEnergy_of_not_summable c hnsum)

/-- Under absolute continuity, a non-square-summable deterministic shift has infinite
shifted-sequence KL. -/
theorem shift_kl_eq_top_of_not_summable_of_ac (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hnsum : ¬ Summable (fun n : ℕ => c n ^ 2)) :
    klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian = ⊤ := by
  exact shift_kl_eq_top_of_not_bddAbove_cmPartialEnergy c hac
    (not_bddAbove_cmPartialEnergy_of_not_summable c hnsum)

/-- Finite shifted-sequence KL, together with absolute continuity, forces the shift to be
square-summable.  This is the finite-KL contrapositive package of the infinite branch. -/
theorem summable_of_shift_kl_finite_of_ac (c : RealSeq)
    (hac : stdSeqGaussian.map (fun x : RealSeq => x + c) ≪ stdSeqGaussian)
    (hfin : klDiv (stdSeqGaussian.map (fun x : RealSeq => x + c)) stdSeqGaussian ≠ ⊤) :
    Summable (fun n : ℕ => c n ^ 2) := by
  exact summable_sq_of_bddAbove_cmPartialEnergy c
    (cmPartialEnergy_bddAbove_of_shift_kl_finite c hac hfin)

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

end ForMathlib.MeasureTheory
