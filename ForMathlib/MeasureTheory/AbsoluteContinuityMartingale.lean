/-
# Absolute continuity from a uniformly-integrable density martingale (Mathlib-staging)

The **`≪` direction of the Kakutani / Doob dichotomy.** Let `ν` be a reference probability measure and
`ℱ : Filtration ℕ` generating the whole σ-algebra (`⨆ n, ℱ n = m`). Suppose a candidate probability
measure `μ` is *locally* absolutely continuous — on each `ℱ n` it has a density `Z n` w.r.t. `ν` — and
the resulting density process `Z` is a **uniformly integrable** `ν`-martingale. Then `μ ≪ ν` globally,
with density the L¹-limit `ℱ.limitProcess Z ν`.

STATUS: PROVED, axiom-clean (`propext / Classical.choice / Quot.sound`).

This is a genuine Mathlib gap (the pin has the density-*process* martingale-convergence theorem
`MeasureTheory.Martingale.ae_eq_condExp_limitProcess`, but not this measure-level absolute-continuity
consequence) and it is the missing regularity input for the **continuum energy identity**
(`ChenGeorgiouPavon2021`): for a deterministic (open-loop) drift the controlled path law is a
Cameron–Martin shift of the Wiener reference, whose finite-dimensional Gaussian shift densities form an
L²-bounded (hence UI) martingale — so this theorem discharges the `P^u ≪ R` edge **Itô-free** (the
shift is deterministic; no stochastic integral).

Proof: with `Zlim := ℱ.limitProcess Z ν`, the L¹ martingale-convergence theorem gives
`Z n =ᵐ[ν] ν[Zlim | ℱ n]`, so on every `ℱ n`-set `s` the local density integrates to the same value as
`Zlim` (`setIntegral_condExp`), i.e. `μ s = ∫⁻ s, ofReal (Zlim) ∂ν = (ν.withDensity (ofReal ∘ Zlim)) s`.
The `ℱ n`-sets form a π-system generating `m`, so `μ` and `ν.withDensity (ofReal ∘ Zlim)` — both
probability measures — coincide (`ext_of_generateFrom_of_iUnion`), and `withDensity_absolutelyContinuous`
finishes.
-/
import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ForMathlib.MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The `ℱ n`-measurable sets, gathered across all `n`, form a **π-system generating** the ambient
σ-algebra when `⨆ n, ℱ n = m`: it is `⋃ n, {s | MeasurableSet[ℱ n] s}`. -/
theorem isPiSystem_iUnion_filtration (ℱ : Filtration ℕ m) :
    IsPiSystem (⋃ n, {s | MeasurableSet[ℱ n] s}) := by
  rintro s hs t ht _
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
  obtain ⟨n, hn⟩ := hs
  obtain ⟨k, hk⟩ := ht
  exact ⟨max n k, (ℱ.mono (le_max_left n k) _ hn).inter (ℱ.mono (le_max_right n k) _ hk)⟩

/-- **Absolute continuity from a uniformly-integrable density martingale** (the `≪` direction of the
Kakutani/Doob dichotomy). See the module docstring. `#print axioms`-clean. -/
theorem absolutelyContinuous_of_densityProcess
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m) (hgen : ⨆ n, ℱ n = m)
    (Z : ℕ → Ω → ℝ) (hmart : Martingale Z ℱ ν) (hUI : UniformIntegrable Z 1 ν)
    (hnonneg : ∀ n, 0 ≤ᵐ[ν] Z n)
    (hdens : ∀ n, ∀ s, MeasurableSet[ℱ n] s → μ s = ∫⁻ x in s, ENNReal.ofReal (Z n x) ∂ν) :
    μ ≪ ν := by
  classical
  -- the L¹ limit of the density martingale
  set Zlim := ℱ.limitProcess Z ν with hZlimdef
  obtain ⟨_R, hR⟩ := hUI.2.2
  have hZlimmem : MemLp Zlim 1 ν := Filtration.memLp_limitProcess_of_eLpNorm_bdd hUI.1 hR
  have hZlimint : Integrable Zlim ν := hZlimmem.integrable le_rfl
  -- `Z n =ᵐ[ν] ν[Zlim | ℱ n]`
  have hcond : ∀ n, Z n =ᵐ[ν] ν[Zlim | ℱ n] := fun n =>
    hmart.ae_eq_condExp_limitProcess hUI n
  -- `Zlim ≥ 0` a.e. (a.e. limit of nonnegative terms)
  have hZlimnonneg : 0 ≤ᵐ[ν] Zlim := by
    have htends : ∀ᵐ ω ∂ν, Tendsto (fun n => Z n ω) atTop (𝓝 (Zlim ω)) :=
      hmart.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hUI
    filter_upwards [htends, ae_all_iff.2 hnonneg] with ω hω hωn
    exact ge_of_tendsto' hω hωn
  -- the candidate density measure
  set ρ := ν.withDensity (fun x => ENNReal.ofReal (Zlim x)) with hρdef
  -- `μ` and `ρ` agree on every `ℱ n`-set
  have hagree : ∀ n, ∀ s, MeasurableSet[ℱ n] s → μ s = ρ s := by
    intro n s hs
    have hsm : MeasurableSet s := ℱ.le n s hs
    -- `Z n` integrates like `Zlim` over `s ∈ ℱ n`
    have hZnint : Integrable (Z n) ν := hmart.integrable n
    have hint_eq : ∫ x in s, Z n x ∂ν = ∫ x in s, Zlim x ∂ν := by
      calc ∫ x in s, Z n x ∂ν
          = ∫ x in s, (ν[Zlim | ℱ n]) x ∂ν :=
            setIntegral_congr_ae hsm ((hcond n).mono fun x hx _ => hx)
        _ = ∫ x in s, Zlim x ∂ν := setIntegral_condExp (ℱ.le n) hZlimint hs
    calc μ s = ∫⁻ x in s, ENNReal.ofReal (Z n x) ∂ν := hdens n s hs
      _ = ENNReal.ofReal (∫ x in s, Z n x ∂ν) :=
            (ofReal_integral_eq_lintegral_ofReal (hZnint.restrict)
              ((ae_restrict_of_ae (hnonneg n)))).symm
      _ = ENNReal.ofReal (∫ x in s, Zlim x ∂ν) := by rw [hint_eq]
      _ = ∫⁻ x in s, ENNReal.ofReal (Zlim x) ∂ν :=
            ofReal_integral_eq_lintegral_ofReal (hZlimint.restrict)
              (ae_restrict_of_ae hZlimnonneg)
      _ = ρ s := by
            rw [hρdef, withDensity_apply _ hsm]
  -- `μ = ρ` by π-system uniqueness
  have hμρ : μ = ρ := by
    have hgenC : m = MeasurableSpace.generateFrom (⋃ n, {s | MeasurableSet[ℱ n] s}) :=
      ((MeasurableSpace.generateFrom_iUnion_measurableSet
        fun n => (ℱ n : MeasurableSpace Ω)).trans hgen).symm
    refine Measure.ext_of_generateFrom_of_iUnion _ (fun _ => Set.univ)
      hgenC (isPiSystem_iUnion_filtration ℱ) (by rw [Set.iUnion_const])
      (fun _ => Set.mem_iUnion.2 ⟨0, MeasurableSet.univ⟩)
      (fun _ => measure_ne_top μ _) ?_
    rintro s hs
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hs
    exact hagree n s hn
  rw [hμρ, hρdef]
  exact withDensity_absolutelyContinuous _ _

end ForMathlib.MeasureTheory
