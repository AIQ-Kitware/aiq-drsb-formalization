/-
# `Measure.pi` of `withDensity` factors (Mathlib-staging)

Finite products of measures-with-density: the product of `(μ i).withDensity (f i)` is the
product measure `Measure.pi μ` with the product density `x ↦ ∏ i, f i (x i)`, together with
the two work-horses around it —

* `map_withDensity_measurableEquiv` — `withDensity` commutes with pushforward along a
  measurable equivalence: `(μ.map e).withDensity g = (μ.withDensity (g ∘ e)).map e`.
  Verified absent from the pinned Mathlib (which has the `Measure.prod` versions
  `prod_withDensity*` but nothing for `map`/`pi`).
* `pi_withDensity` — the product-density identity, by induction on `Fin n` through
  `MeasurableEquiv.piFinSuccAbove` (pair step: Mathlib's `prod_withDensity`) and transport
  to an arbitrary `Fintype` index along `MeasurableEquiv.piCongrLeft`.
* `lintegral_pi_prod` — the finite-product Tonelli
  `∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i`, also verified absent from
  the pin (only the two-factor `lintegral_prod` exists). Proved by the same induction,
  independently of `pi_withDensity` (so it needs no σ-finiteness of the density factors).

STATUS: PROVED, dependency-clean (`propext / Classical.choice / Quot.sound`).

These are the `M2.2` bricks of `PLAN_CONTINUUM_CLOSURE.md`: they supply the
finite-dimensional Gaussian Cameron–Martin density (`stdGaussian ι` shifted = `stdGaussian ι`
with the product of the 1-D shift densities) and the moment computations of the
Cameron–Martin density martingale. All three are paper-agnostic and upstreamable; for
Mathlib, `pi_withDensity`/`lintegral_pi_prod` should additionally be generalized to
dependent fibres in the `Fintype` versions (the `Fin` cores below are already fully
dependent; the constant-fibre transport is all this repo needs).
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace ForMathlib.MeasureTheory

/-- **`withDensity` commutes with pushforward along a measurable equivalence**:
`(μ.map e).withDensity g = (μ.withDensity (g ∘ e)).map e`. Both sides evaluate a
measurable set `s` to `∫⁻ x in e ⁻¹' s, g (e x) ∂μ` (`setLIntegral_map` on the left,
`Measure.map_apply` + `withDensity_apply` on the right). -/
theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (μ.map e).withDensity g = (μ.withDensity fun x => g (e x)).map e := by
  ext s hs
  rw [withDensity_apply _ hs, setLIntegral_map hs hg e.measurable,
    Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs)]

/-- `Fin`-indexed core of `pi_withDensity`, with fully dependent fibres. Induction on `n`:
the pair step is Mathlib's `prod_withDensity`, and the product space is reassembled through
`MeasurableEquiv.piFinSuccAbove` using `map_withDensity_measurableEquiv`. -/
theorem pi_withDensity_fin :
    ∀ {n : ℕ} {X : Fin n → Type*} [∀ i, MeasurableSpace (X i)]
      (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
      (f : ∀ i, X i → ℝ≥0∞) (_hf : ∀ i, Measurable (f i))
      [∀ i, SigmaFinite ((μ i).withDensity (f i))],
      Measure.pi (fun i => (μ i).withDensity (f i))
        = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
  | 0, X, _, μ, _, f, _hf, _ => by
      have hμ : (fun i : Fin 0 => (μ i).withDensity (f i)) = μ := funext fun i => i.elim0
      have hone : (fun x : ∀ i : Fin 0, X i => ∏ i, f i (x i)) = 1 :=
        funext fun x => by simp
      rw [hμ, hone, withDensity_one]
  | n + 1, X, _, μ, _, f, hf, _ => by
      haveI : ∀ i : Fin n, SigmaFinite ((μ (Fin.succAbove 0 i)).withDensity
          (f (Fin.succAbove 0 i))) := fun i => inferInstance
      set E := MeasurableEquiv.piFinSuccAbove X 0
      have hmeas_tail : Measurable fun y : ∀ i : Fin n, X (Fin.succAbove 0 i) =>
          ∏ i, f (Fin.succAbove 0 i) (y i) :=
        Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
      refine MeasurableEquiv.map_measurableEquiv_injective E ?_
      calc (Measure.pi fun i => (μ i).withDensity (f i)).map E
          = ((μ 0).withDensity (f 0)).prod
              (Measure.pi fun i => (μ (Fin.succAbove 0 i)).withDensity
                (f (Fin.succAbove 0 i))) :=
            (measurePreserving_piFinSuccAbove (fun i => (μ i).withDensity (f i)) 0).map_eq
        _ = ((μ 0).withDensity (f 0)).prod
              ((Measure.pi fun i => μ (Fin.succAbove 0 i)).withDensity
                fun y => ∏ i, f (Fin.succAbove 0 i) (y i)) := by
            rw [pi_withDensity_fin (fun i => μ (Fin.succAbove 0 i))
              (fun i => f (Fin.succAbove 0 i)) fun i => hf _]
        _ = ((μ 0).prod (Measure.pi fun i => μ (Fin.succAbove 0 i))).withDensity
              (fun p => f 0 p.1 * ∏ i, f (Fin.succAbove 0 i) (p.2 i)) :=
            prod_withDensity (hf 0) hmeas_tail
        _ = ((Measure.pi μ).map E).withDensity
              (fun p => f 0 p.1 * ∏ i, f (Fin.succAbove 0 i) (p.2 i)) := by
            rw [(measurePreserving_piFinSuccAbove μ 0).map_eq]
        _ = ((Measure.pi μ).withDensity
              fun x => f 0 (E x).1 * ∏ i, f (Fin.succAbove 0 i) ((E x).2 i)).map E :=
            map_withDensity_measurableEquiv E _
              (((hf 0).comp measurable_fst).mul (hmeas_tail.comp measurable_snd))
        _ = ((Measure.pi μ).withDensity fun x => ∏ i, f i (x i)).map E := by
            have hfun : (fun x : ∀ i, X i =>
                  f 0 (E x).1 * ∏ i, f (Fin.succAbove 0 i) ((E x).2 i))
                = fun x => ∏ i, f i (x i) := by
              funext x
              rw [Fin.prod_univ_succAbove (fun i => f i (x i)) 0]
              rfl
            rw [hfun]

/-- **`Measure.pi` of `withDensity` factors** (constant-fibre `Fintype` form): the product
of `(μ i).withDensity (f i)` is the product measure with the product density
`x ↦ ∏ i, f i (x i)`. Transported from the `Fin` core `pi_withDensity_fin` along
`MeasurableEquiv.piCongrLeft` (in the cast-free `symm` orientation).

The `SigmaFinite` instance arguments on the density factors are discharged automatically in
the intended (probability-density) applications. Verified absent from the pinned Mathlib;
upstreamable. -/
theorem pi_withDensity {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, SigmaFinite (μ i)]
    (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  set e := Fintype.equivFin ι
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => X) e
  haveI : ∀ j, SigmaFinite (μ (e.symm j)) := fun j => inferInstance
  haveI : ∀ j, SigmaFinite ((μ (e.symm j)).withDensity (f (e.symm j))) :=
    fun j => inferInstance
  -- reindexing along `E.symm`: `Measure.pi ν = (Measure.pi (ν ∘ e.symm)).map E.symm`
  have hstar : ∀ ν : ι → Measure X, (∀ i, SigmaFinite (ν i)) →
      Measure.pi ν = (Measure.pi fun j => ν (e.symm j)).map E.symm := by
    intro ν hν
    haveI : ∀ j, SigmaFinite (ν (e.symm j)) := fun j => hν (e.symm j)
    have h := Measure.pi_map_piCongrLeft (β := fun _ : Fin (Fintype.card ι) => X) e
      (μ := fun j => ν (e.symm j))
    rw [show (fun i => ν (e.symm (e i))) = ν from
      funext fun i => by rw [e.symm_apply_apply]] at h
    exact (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq E).mp h
  -- the two densities agree through `E.symm` (cast-free: `E.symm y i = y (e i)`)
  have hEsymm : ∀ (y : Fin (Fintype.card ι) → X) (i : ι), E.symm y i = y (e i) := fun y i =>
    Equiv.piCongrLeft_symm_apply (fun _ => X) e y i
  have hdens : ∀ y : Fin (Fintype.card ι) → X,
      ∏ j, f (e.symm j) (y j) = ∏ i, f i (E.symm y i) := by
    intro y
    rw [← Equiv.prod_comp e fun j => f (e.symm j) (y j)]
    exact Finset.prod_congr rfl fun i _ => by rw [e.symm_apply_apply, hEsymm]
  calc Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi fun j => (μ (e.symm j)).withDensity (f (e.symm j))).map E.symm :=
        hstar _ fun i => inferInstance
    _ = ((Measure.pi fun j => μ (e.symm j)).withDensity
          fun y => ∏ j, f (e.symm j) (y j)).map E.symm := by
        rw [pi_withDensity_fin _ _ fun j => hf (e.symm j)]
    _ = ((Measure.pi fun j => μ (e.symm j)).withDensity
          fun y => ∏ i, f i (E.symm y i)).map E.symm := by
        simp_rw [hdens]
    _ = (((Measure.pi fun j => μ (e.symm j)).map E.symm).withDensity
          fun x => ∏ i, f i (x i)) :=
        (map_withDensity_measurableEquiv E.symm _
          (Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i))).symm
    _ = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
        rw [← hstar μ fun i => inferInstance]

/-- `Fin`-indexed core of `lintegral_pi_prod` (fully dependent fibres): Tonelli for a
finite product of nonnegative integrands over `Measure.pi`. Induction on `n`; the pair
step is Mathlib's two-factor `lintegral_prod`. -/
theorem lintegral_pi_prod_fin :
    ∀ {n : ℕ} {X : Fin n → Type*} [∀ i, MeasurableSpace (X i)]
      (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
      (f : ∀ i, X i → ℝ≥0∞) (_hf : ∀ i, Measurable (f i)),
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i
  | 0, X, _, μ, _, f, _hf => by
      simp
  | n + 1, X, _, μ, _, f, hf => by
      set E := MeasurableEquiv.piFinSuccAbove X 0
      have hmeas_tail : Measurable fun y : ∀ i : Fin n, X (Fin.succAbove 0 i) =>
          ∏ i, f (Fin.succAbove 0 i) (y i) :=
        Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
      have hmeas_pair : Measurable fun p : X 0 × ∀ i : Fin n, X (Fin.succAbove 0 i) =>
          f 0 p.1 * ∏ i, f (Fin.succAbove 0 i) (p.2 i) :=
        ((hf 0).comp measurable_fst).mul (hmeas_tail.comp measurable_snd)
      calc ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ
          = ∫⁻ x, f 0 (E x).1 * ∏ i, f (Fin.succAbove 0 i) ((E x).2 i) ∂Measure.pi μ := by
            refine lintegral_congr fun x => ?_
            rw [Fin.prod_univ_succAbove (fun i => f i (x i)) 0]
            rfl
        _ = ∫⁻ p, f 0 p.1 * ∏ i, f (Fin.succAbove 0 i) (p.2 i)
              ∂((μ 0).prod (Measure.pi fun i => μ (Fin.succAbove 0 i))) :=
            (measurePreserving_piFinSuccAbove μ 0).lintegral_comp hmeas_pair
        _ = ∫⁻ a, ∫⁻ b, f 0 a * ∏ i, f (Fin.succAbove 0 i) (b i)
              ∂(Measure.pi fun i => μ (Fin.succAbove 0 i)) ∂μ 0 :=
            lintegral_prod _ hmeas_pair.aemeasurable
        _ = ∫⁻ a, f 0 a * ∫⁻ b, ∏ i, f (Fin.succAbove 0 i) (b i)
              ∂(Measure.pi fun i => μ (Fin.succAbove 0 i)) ∂μ 0 := by
            refine lintegral_congr fun a => ?_
            rw [lintegral_const_mul _ hmeas_tail]
        _ = (∫⁻ y, f 0 y ∂μ 0) * ∫⁻ b, ∏ i, f (Fin.succAbove 0 i) (b i)
              ∂(Measure.pi fun i => μ (Fin.succAbove 0 i)) :=
            lintegral_mul_const _ (hf 0)
        _ = ∏ i, ∫⁻ y, f i y ∂μ i := by
            rw [lintegral_pi_prod_fin (fun i => μ (Fin.succAbove 0 i))
              (fun i => f (Fin.succAbove 0 i)) fun i => hf _,
              Fin.prod_univ_succAbove (fun i => ∫⁻ y, f i y ∂μ i) 0]

/-- **Tonelli for a finite product of integrands over `Measure.pi`** (constant-fibre
`Fintype` form): `∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i`. Verified
absent from the pinned Mathlib (only the two-factor `lintegral_prod` exists). This is the
moment-computation work-horse for the Cameron–Martin density martingale's `L²` bound
(`PLAN_CONTINUUM_CLOSURE.md` M2.7). Upstreamable. -/
theorem lintegral_pi_prod {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, SigmaFinite (μ i)]
    (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  set e := Fintype.equivFin ι
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => X) e
  haveI : ∀ j, SigmaFinite (μ (e.symm j)) := fun j => inferInstance
  have hstar : Measure.pi μ = (Measure.pi fun j => μ (e.symm j)).map E.symm := by
    have h := Measure.pi_map_piCongrLeft (β := fun _ : Fin (Fintype.card ι) => X) e
      (μ := fun j => μ (e.symm j))
    rw [show (fun i => μ (e.symm (e i))) = μ from
      funext fun i => by rw [e.symm_apply_apply]] at h
    exact (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq E).mp h
  have hEsymm : ∀ (y : Fin (Fintype.card ι) → X) (i : ι), E.symm y i = y (e i) := fun y i =>
    Equiv.piCongrLeft_symm_apply (fun _ => X) e y i
  have hdens : ∀ y : Fin (Fintype.card ι) → X,
      ∏ i, f i (E.symm y i) = ∏ j, f (e.symm j) (y j) := by
    intro y
    rw [← Equiv.prod_comp e fun j => f (e.symm j) (y j)]
    exact (Finset.prod_congr rfl fun i _ => by rw [e.symm_apply_apply, hEsymm]).symm
  calc ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ
      = ∫⁻ y, ∏ i, f i (E.symm y i) ∂Measure.pi (fun j => μ (e.symm j)) := by
        rw [hstar, lintegral_map_equiv]
    _ = ∫⁻ y, ∏ j, f (e.symm j) (y j) ∂Measure.pi (fun j => μ (e.symm j)) := by
        simp_rw [hdens]
    _ = ∏ j, ∫⁻ y, f (e.symm j) y ∂μ (e.symm j) :=
        lintegral_pi_prod_fin _ _ fun j => hf (e.symm j)
    _ = ∏ i, ∫⁻ y, f i y ∂μ i := Equiv.prod_comp e.symm fun i => ∫⁻ y, f i y ∂μ i

end ForMathlib.MeasureTheory
