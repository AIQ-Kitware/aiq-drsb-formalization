/-
# Cameron–Martin relative entropy of a finite-dimensional Gaussian (Mathlib-staging)

The relative entropy (KL divergence) between a shifted standard Gaussian and the
standard Gaussian is exactly the Cameron–Martin cost of the shift:

  `KL((stdGaussian ι).map (· + h) ‖ stdGaussian ι) = ½‖h‖²`.

This is the finite-dimensional / Euler–Maruyama core of the DRSB control-energy
identity (`ChenGeorgiouPavon2021.energy_identity`, CGP (4.19)): in the
Euler–Maruyama discretization the increment law of each step is a shifted Gaussian,
so this identity gives per step `KL = ½‖drift·√Δt‖²` and summing over steps is the
discrete control energy — precisely the quantity the DRSB card actually measures
(AGENTS.md §3: "exact 𝔼_μ[V] → Euler–Maruyama SDE"). See the discrete energy
identity `klDiv_emShift_eq_emEnergy` at the bottom of this file.

--------------------------------------------------------------------------------
## PROVENANCE (vendored external proof — see SURVEY_LEADS.md vendoring policy)

The declarations `stdGaussian`, `klDiv_gaussianReal_shift`, `klDiv_map_measurableEquiv`,
`klDiv_prod`, `klDiv_pi`, `klDiv_pi_fintype`, and `klDiv_stdGaussian_map_add` are
**vendored verbatim** (namespace adapted `GibbsVariational → ForMathlib.MeasureTheory`)
from:

* Original author: **Michael R. Douglas** (`mrdouglasny`)
* Source repo:     https://github.com/mrdouglasny/gibbs-variational
* Source file:     `GibbsVariational/GaussianEntropy.lean`
* Source commit:   `75e08d8aaca83bb090fc43855898991fbfc9abf3`
  (permalink: https://github.com/mrdouglasny/gibbs-variational/blob/75e08d8aaca83bb090fc43855898991fbfc9abf3/GibbsVariational/GaussianEntropy.lean)
* License:         **Apache-2.0** (SPDX: Apache-2.0) — compatible with ours (Apache-2.0);
                   upstream copyright notice retained below.
* Retrieved:       2026-07-03
* Adapted by:      the DRSB formalization effort — only the enclosing namespace changed
                   (`GibbsVariational` → `ForMathlib.MeasureTheory`); the proofs are
                   Douglas's, unmodified.

The concluding section (`emShift`, `emEnergy`, `klDiv_emShift_eq_emEnergy`) — the
Euler–Maruyama discrete energy identity that consumes the vendored Cameron–Martin
lemma — is **original to this repo** (not from the upstream source).

Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
--------------------------------------------------------------------------------
-/
import Mathlib

open MeasureTheory Real InformationTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ForMathlib.MeasureTheory

/-- The standard Gaussian measure on `ι → ℝ` for a finite index type `ι`
(the product of one-dimensional `N(0,1)` factors). -/
noncomputable def stdGaussian (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (stdGaussian ι) := by
  unfold stdGaussian; infer_instance

/-- The 1D building block: `KL(N(c,1) ‖ N(0,1)) = ½ c²`.

Direct density computation. The Radon–Nikodym derivative `d N(c,1)/d N(0,1)` is the PDF ratio
`gaussianPDFReal c 1 / gaussianPDFReal 0 1`, whose `√(2π)` normalisations cancel, leaving
`exp(c·x − ½c²)`; so `llr = c·x − ½c²`, and `KL = ∫ llr d N(c,1) = c·c − ½c² = ½c²`
using `∫ x d N(c,1) = c` (`integral_id_gaussianReal`). -/
theorem klDiv_gaussianReal_shift (c : ℝ) :
    klDiv (gaussianReal c 1) (gaussianReal 0 1) = ENNReal.ofReal (2⁻¹ * c ^ 2) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hac : gaussianReal c 1 ≪ gaussianReal 0 1 :=
    (gaussianReal_absolutelyContinuous c h1).trans (gaussianReal_absolutelyContinuous' 0 h1)
  -- The Radon–Nikodym derivative is the PDF ratio (`volume`-a.e.).
  have hrn : (gaussianReal c 1).rnDeriv (gaussianReal 0 1) =ᵐ[volume]
      fun x => (gaussianPDF 0 1 x)⁻¹ * gaussianPDF c 1 x := by
    have h := Measure.rnDeriv_withDensity_right (gaussianReal c 1) volume
      (f := gaussianPDF 0 1) (measurable_gaussianPDF 0 1).aemeasurable
      (ae_of_all _ fun x => (gaussianPDF_pos 0 h1 x).ne')
      (ae_of_all _ fun _ => gaussianPDF_lt_top.ne)
    rw [← gaussianReal_of_var_ne_zero 0 h1] at h
    filter_upwards [h, rnDeriv_gaussianReal c 1] with x hx hxrn
    rw [hx, hxrn]
  -- Hence `llr` is the linear function `c·x − ½c²` (`N(c,1)`-a.e.).
  have hllr : llr (gaussianReal c 1) (gaussianReal 0 1) =ᵐ[gaussianReal c 1]
      fun x => c * x - 2⁻¹ * c ^ 2 := by
    have hs : Real.sqrt (2 * π) ≠ 0 := by positivity
    filter_upwards [(gaussianReal_absolutelyContinuous c h1).ae_le hrn] with x hx
    have hpdf : (gaussianPDFReal 0 1 x)⁻¹ * gaussianPDFReal c 1 x
        = Real.exp (c * x - 2⁻¹ * c ^ 2) := by
      simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one]
      rw [mul_inv, inv_inv, ← Real.exp_neg, mul_mul_mul_comm, mul_inv_cancel₀ hs, one_mul,
        ← Real.exp_add]
      congr 1
      ring
    unfold llr
    rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, toReal_gaussianPDF, toReal_gaussianPDF,
      hpdf, Real.log_exp]
  -- Integrability of the linear `llr`.
  have hid : Integrable (fun x => x) (gaussianReal c 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hint : Integrable (llr (gaussianReal c 1) (gaussianReal 0 1)) (gaussianReal c 1) := by
    rw [integrable_congr hllr]
    exact (hid.const_mul c).sub (integrable_const _)
  have hne : klDiv (gaussianReal c 1) (gaussianReal 0 1) ≠ ∞ :=
    klDiv_ne_top_iff.mpr ⟨hac, hint⟩
  -- The mean computation `∫ (c·x − ½c²) d N(c,1) = ½c²`.
  have hmean : ∫ x, (c * x - 2⁻¹ * c ^ 2) ∂(gaussianReal c 1) = 2⁻¹ * c ^ 2 := by
    have hs2 : ∫ x, (c * x - 2⁻¹ * c ^ 2) ∂(gaussianReal c 1)
        = (∫ x, c * x ∂(gaussianReal c 1)) - ∫ _x, (2⁻¹ * c ^ 2 : ℝ) ∂(gaussianReal c 1) :=
      integral_sub (hid.const_mul c) (integrable_const _)
    rw [hs2, integral_const_mul, integral_id_gaussianReal]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul]
    ring
  have hval : (klDiv (gaussianReal c 1) (gaussianReal 0 1)).toReal = 2⁻¹ * c ^ 2 := by
    rw [toReal_klDiv hac hint,
      show ∫ a, llr (gaussianReal c 1) (gaussianReal 0 1) a ∂(gaussianReal c 1) = 2⁻¹ * c ^ 2
        from (integral_congr_ae hllr).trans hmean]
    simp
  rw [← ENNReal.ofReal_toReal hne, hval]

lemma klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  by_cases h : μ ≪ ν
  · rw [klDiv_eq_lintegral_klFun_of_ac (μ := μ.map e) (ν := ν.map e)
      (e.measurableEmbedding.absolutelyContinuous_map h)]
    rw [klDiv_eq_lintegral_klFun_of_ac (μ := μ) (ν := ν) h]
    rw [MeasureTheory.lintegral_map_equiv (μ := ν)
      (f := fun y => ENNReal.ofReal (klFun (((μ.map e).rnDeriv (ν.map e) y).toReal))) e]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    simp [hx]
  · have hmap : ¬ μ.map e ≪ ν.map e := by
      intro hmap
      have hback := e.symm.measurableEmbedding.absolutelyContinuous_map hmap
      exact h (by simpa using hback)
    rw [klDiv_of_not_ac hmap, klDiv_of_not_ac h]

lemma klDiv_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  have hswap : klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) = klDiv (μ₂.prod μ₁) (ν₂.prod μ₁) := by
    have h := klDiv_map_measurableEquiv (e := MeasurableEquiv.prodComm) (μ := μ₁.prod μ₂)
      (ν := μ₁.prod ν₂)
    change klDiv (Measure.map Prod.swap (μ₁.prod μ₂)) (Measure.map Prod.swap (μ₁.prod ν₂)) = _
      at h
    symm
    simpa [MeasureTheory.Measure.prod_swap] using h
  have hright : klDiv (μ₂.prod μ₁) (ν₂.prod μ₁) = klDiv μ₂ ν₂ := by
    simpa [Measure.compProd_const] using
      (klDiv_compProd_left (μ := μ₂) (ν := ν₂) (κ := Kernel.const β μ₁))
  calc
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂)
        = klDiv μ₁ ν₁ + klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) := by
            simpa [Measure.compProd_const] using
              (klDiv_compProd_eq_add (μ := μ₁) (ν := ν₁)
                (κ := Kernel.const α μ₂) (η := Kernel.const α ν₂))
    _ = klDiv μ₁ ν₁ + klDiv (μ₂.prod μ₁) (ν₂.prod μ₁) := by rw [hswap]
    _ = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by rw [hright]

lemma klDiv_pi :
    ∀ {n : ℕ} {X : Fin n → Type*} [∀ i, MeasurableSpace (X i)]
      (μ ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
      [∀ i, IsProbabilityMeasure (ν i)],
      klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i)
  | 0, X, _, μ, ν, _, _ => by
      calc
        klDiv (Measure.pi μ) (Measure.pi ν)
            = klDiv ((Measure.pi μ).map (MeasurableEquiv.ofUniqueOfUnique ((i : Fin 0) → X i)
                Unit))
                ((Measure.pi ν).map (MeasurableEquiv.ofUniqueOfUnique ((i : Fin 0) → X i)
                Unit)) := by
                  symm
                  exact klDiv_map_measurableEquiv
                    (e := MeasurableEquiv.ofUniqueOfUnique ((i : Fin 0) → X i) Unit)
                    (μ := Measure.pi μ) (ν := Measure.pi ν)
        _ = 0 := by
            rw [(MeasureTheory.measurePreserving_pi_empty (μ := μ)).map_eq,
              (MeasureTheory.measurePreserving_pi_empty (μ := ν)).map_eq]
            simp
        _ = ∑ i, klDiv (μ i) (ν i) := by simp
  | n + 1, X, _, μ, ν, _, _ => by
      calc
        klDiv (Measure.pi μ) (Measure.pi ν)
            = klDiv ((Measure.pi μ).map (MeasurableEquiv.piFinSuccAbove X 0))
                ((Measure.pi ν).map (MeasurableEquiv.piFinSuccAbove X 0)) := by
                  symm
                  exact klDiv_map_measurableEquiv (e := MeasurableEquiv.piFinSuccAbove X 0)
                    (μ := Measure.pi μ) (ν := Measure.pi ν)
        _ = klDiv ((μ 0).prod (Measure.pi fun i => μ (Fin.succ i)))
              ((ν 0).prod (Measure.pi fun i => ν (Fin.succ i))) := by
                rw [(MeasureTheory.measurePreserving_piFinSuccAbove (μ := μ) 0).map_eq,
                  (MeasureTheory.measurePreserving_piFinSuccAbove (μ := ν) 0).map_eq]
                rfl
        _ = klDiv (μ 0) (ν 0) + klDiv (Measure.pi fun i => μ (Fin.succ i))
              (Measure.pi fun i => ν (Fin.succ i)) := by
                rw [klDiv_prod]
        _ = klDiv (μ 0) (ν 0) + ∑ i, klDiv (μ (Fin.succ i)) (ν (Fin.succ i)) := by
                rw [klDiv_pi (μ := fun i => μ (Fin.succ i)) (ν := fun i => ν (Fin.succ i))]
        _ = ∑ i, klDiv (μ i) (ν i) := by rw [Fin.sum_univ_succ]

/-- KL divergence tensorises over `Measure.pi` for an arbitrary finite index type `ι`
(constant-fibre form). Transported from the `Fin n` case `klDiv_pi` via `Fintype.equivFin`,
using `klDiv` invariance under the reindexing measurable equivalence. -/
lemma klDiv_pi_fintype {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
    (μ ν : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  let e := Fintype.equivFin ι
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => X) e
  haveI : ∀ j, IsProbabilityMeasure (μ (e.symm j)) := fun j => inferInstance
  haveI : ∀ j, IsProbabilityMeasure (ν (e.symm j)) := fun j => inferInstance
  haveI : ∀ j, SigmaFinite (μ (e.symm j)) := fun j => inferInstance
  haveI : ∀ j, SigmaFinite (ν (e.symm j)) := fun j => inferInstance
  have hstarμ : (Measure.pi μ).map E = Measure.pi (fun j => μ (e.symm j)) := by
    have h := Measure.pi_map_piCongrLeft (β := fun _ : Fin (Fintype.card ι) => X) e
      (μ := fun j => μ (e.symm j))
    rwa [show (fun i => μ (e.symm (e i))) = μ from
      funext fun i => by rw [e.symm_apply_apply]] at h
  have hstarν : (Measure.pi ν).map E = Measure.pi (fun j => ν (e.symm j)) := by
    have h := Measure.pi_map_piCongrLeft (β := fun _ : Fin (Fintype.card ι) => X) e
      (μ := fun j => ν (e.symm j))
    rwa [show (fun i => ν (e.symm (e i))) = ν from
      funext fun i => by rw [e.symm_apply_apply]] at h
  calc klDiv (Measure.pi μ) (Measure.pi ν)
      = klDiv ((Measure.pi μ).map E) ((Measure.pi ν).map E) :=
        (klDiv_map_measurableEquiv E (Measure.pi μ) (Measure.pi ν)).symm
    _ = klDiv (Measure.pi (fun j => μ (e.symm j))) (Measure.pi (fun j => ν (e.symm j))) := by
        rw [hstarμ, hstarν]
    _ = ∑ j, klDiv (μ (e.symm j)) (ν (e.symm j)) := klDiv_pi _ _
    _ = ∑ i, klDiv (μ i) (ν i) := Equiv.sum_comp e.symm (fun i => klDiv (μ i) (ν i))

/-- **Cameron–Martin relative entropy** for the standard finite-dimensional Gaussian.

Shifting the standard Gaussian by `h` costs relative entropy `½‖h‖²`:
`KL((stdGaussian n).map (· + h) ‖ stdGaussian n) = ½ ∑ᵢ (h i)²`.

**Proof strategy.** The Cameron–Martin density factorizes over coordinates:
`d((stdGaussian n).map (·+h)) / d(stdGaussian n) (x) = exp(∑ᵢ (h i · x i − ½ (h i)²))`
(product of the 1D Gaussian shift densities `exp(hᵢ xᵢ − ½ hᵢ²)`, each from `gaussianReal`).
Hence, `(shifted)`-a.e., `llr (shifted) (stdGaussian n) (x) = ∑ᵢ h i · x i − ½ ∑ᵢ (h i)²`, so
`KL = ∫ llr d(shifted) = ∑ᵢ h i · 𝔼_shifted[xᵢ] − ½ ∑ᵢ (h i)² = ∑ᵢ (h i)² − ½ ∑ᵢ (h i)²`
`= ½ ∑ᵢ (h i)²`, using `𝔼_shifted[xᵢ] = h i` (the shifted Gaussian has mean `h`).

Reduce to the 1D case `klDiv (gaussianReal (h i) 1) (gaussianReal 0 1) = ½ (h i)²` (a direct
density computation) and tensorize via `klDiv` of product measures over `Measure.pi`. -/
theorem klDiv_stdGaussian_map_add {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    klDiv ((stdGaussian ι).map (· + h)) (stdGaussian ι)
      = ENNReal.ofReal (2⁻¹ * ∑ i, (h i) ^ 2) := by
  have hmap : (stdGaussian ι).map (· + h) = Measure.pi (fun i => gaussianReal (h i) 1) := by
    unfold stdGaussian
    change (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x i => x i + h i) =
      Measure.pi (fun i => gaussianReal (h i) 1)
    rw [show (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x i => x i + h i) =
        Measure.pi (fun i => (gaussianReal 0 1).map (fun x : ℝ => x + h i)) by
          simpa using (Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
            (f := fun i (x : ℝ) => x + h i) (hf := fun i => by fun_prop))]
    exact congrArg Measure.pi <| funext fun i => by
      simpa using gaussianReal_map_add_const (μ := 0) (v := 1) (y := h i)
  rw [hmap, stdGaussian, klDiv_pi_fintype]
  simp_rw [klDiv_gaussianReal_shift]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Finset.mul_sum]
  · intro i hi
    positivity

--------------------------------------------------------------------------------
-- Euler–Maruyama discrete energy identity  (ORIGINAL to this repo — not vendored)
--
-- Consumes the vendored Cameron–Martin lemma to prove that the KL between the
-- Euler–Maruyama-discretized controlled path law and the reference path law equals
-- the discrete control energy — the quantity the DRSB card measures.  This is the
-- discrete/Gaussian layer of `ChenGeorgiouPavon2021.energy_identity` (CGP (4.19)).
--------------------------------------------------------------------------------

/-- **Euler–Maruyama noise shift.**  For an `N`-step discretization of `dX = u dt + √ε dW`
on `[0,1]` with step `Δt` and (with `ε = 1`) standard-Gaussian increments, the controlled
increment at step `k` has mean `u_k · Δt` and standard deviation `√Δt`, i.e. the *whitened*
increment `= √Δt · u_k + N(0,I)`.  So the controlled path law is the reference standard
Gaussian on the whole `Fin N × ι`-indexed increment space shifted by `emShift Δt u`. -/
noncomputable def emShift {ι : Type*} [Fintype ι] {N : ℕ} (Δt : ℝ) (u : Fin N → ι → ℝ) :
    (Fin N × ι) → ℝ :=
  fun p => Real.sqrt Δt * u p.1 p.2

/-- **Discrete (Euler–Maruyama) control energy.**  The Riemann sum
`∑ₖ Δt · (½‖u_k‖²)` approximating the continuous control energy `𝔼[∫₀¹ ½‖u_t‖² dt]`
of CGP (4.19)/(4.20). -/
noncomputable def emEnergy {ι : Type*} [Fintype ι] {N : ℕ} (Δt : ℝ) (u : Fin N → ι → ℝ) : ℝ :=
  ∑ k, Δt * (2⁻¹ * ∑ i, (u k i) ^ 2)

/-- **Discrete energy identity (Euler–Maruyama layer of CGP (4.19)).**

For the `N`-step Euler–Maruyama discretization (unit diffusion `ε = 1`, both the
controlled and reference chains started at the same point so the endpoint-entropy term
of (4.19) vanishes), the relative entropy between the controlled path law
`(stdGaussian).map (· + emShift Δt u)` and the reference path law `stdGaussian` equals
the discrete control energy `emEnergy Δt u`:

`KL(P^u ‖ P^0) = ∑ₖ Δt · ½‖u_k‖²`.

Proved sorry-free from the vendored Cameron–Martin identity `klDiv_stdGaussian_map_add`:
each per-step shift `√Δt·u_k` contributes `½‖√Δt·u_k‖² = Δt·½‖u_k‖²`, and KL tensorises
over the `Fin N × ι` increment coordinates. This is exactly the summed-shifted-Gaussian
construction described in AGENTS.md §3 (the card's Euler–Maruyama measurement of the SOC
energy). The remaining bridge to the *continuous* `energy_identity` is the
Euler–Maruyama → SDE limit (`Δt → 0`), a documented T4 edge — see `PROOF_PIPELINE.md`. -/
theorem klDiv_emShift_eq_emEnergy {ι : Type*} [Fintype ι] {N : ℕ} {Δt : ℝ} (hΔt : 0 ≤ Δt)
    (u : Fin N → ι → ℝ) :
    (klDiv ((stdGaussian (Fin N × ι)).map (· + emShift Δt u)) (stdGaussian (Fin N × ι))).toReal
      = emEnergy Δt u := by
  rw [klDiv_stdGaussian_map_add (emShift Δt u)]
  have hnonneg : (0 : ℝ) ≤ 2⁻¹ * ∑ p : Fin N × ι, (emShift Δt u p) ^ 2 := by positivity
  rw [ENNReal.toReal_ofReal hnonneg]
  -- expand `emShift`, use `(√Δt)² = Δt`, and reindex the `Fin N × ι` sum as a double sum
  unfold emShift emEnergy
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hstep : ∑ i, (Real.sqrt Δt * u k i) ^ 2 = Δt * ∑ i, (u k i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_pow, Real.sq_sqrt hΔt]
  rw [hstep]; ring

end ForMathlib.MeasureTheory
