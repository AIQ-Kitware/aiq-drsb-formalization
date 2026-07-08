/-
# Absolute continuity from a uniformly-integrable density martingale (Mathlib-staging)

The **`≪` direction of the Kakutani / Doob dichotomy.** Let `ν` be a reference probability measure and
`ℱ : Filtration ℕ` generating the whole σ-algebra (`⨆ n, ℱ n = m`). Suppose a candidate probability
measure `μ` is *locally* absolutely continuous — on each `ℱ n` it has a density `Z n` w.r.t. `ν` — and
the resulting density process `Z` is a **uniformly integrable** `ν`-martingale. Then `μ ≪ ν` globally,
with density the L¹-limit `ℱ.limitProcess Z ν`.

STATUS: PROVED, dependency-clean (`propext / Classical.choice / Quot.sound`).

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

This file also supplies the two reductions that make the theorem *applicable* without any
martingale/UI verification at the call site (`PLAN_CONTINUUM_CLOSURE.md` M1 + M2.6):

* `martingale_of_setLIntegral_eq` — a locally-consistent density process **is automatically a
  martingale**: if each `Z n` is `ℱ n`-strongly measurable and integrates on every `ℱ n`-set to
  `μ` of that set, the tower property is forced (conditional-expectation uniqueness); no
  distributional computation is needed.
* `uniformIntegrable_one_of_lintegral_sq_bdd` — a uniform second-moment bound gives uniform
  integrability (elementary Chebyshev truncation; no maximal inequality).
* `absolutelyContinuous_of_localDensity` — their composition with the main theorem: local
  densities + a uniform `L²` bound ⇒ `μ ≪ ν`. This is the form the Gaussian Cameron–Martin
  application consumes (the `L²` bound being `exp` of the partial Cameron–Martin energy).
-/
import Mathlib

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

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
Kakutani/Doob dichotomy). See the module docstring. Lean dependency audit-clean. -/
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

/-- **A uniformly `L²`-bounded nonnegative family is uniformly integrable** (in the
probability sense, exponent `1`). Elementary Chebyshev truncation: on the tail set
`{C ≤ ‖Z n ·‖₊}` the pointwise bound `‖Z n x‖ₑ ≤ ‖Z n x‖ₑ ^ 2 / C` holds, so the truncated
`L¹` mass is at most `M / C`, which is `≤ ε` for `C := (M / ε).toNNReal + 1`. No maximal
inequality or interpolation is needed. -/
theorem uniformIntegrable_one_of_lintegral_sq_bdd
    {ν : Measure Ω} [IsFiniteMeasure ν] {Z : ℕ → Ω → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (Z n) ν) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hL2 : ∀ n, ∫⁻ x, ENNReal.ofReal (Z n x) ^ 2 ∂ν ≤ M)
    (hnonneg : ∀ n, 0 ≤ᵐ[ν] Z n) :
    UniformIntegrable Z 1 ν := by
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top hmeas fun ε hε => ?_
  have hε0 : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  set C : ℝ≥0 := (M / ENNReal.ofReal ε).toNNReal + 1 with hC
  have hCcoe : (C : ℝ≥0∞) = M / ENNReal.ofReal ε + 1 := by
    rw [hC, ENNReal.coe_add, ENNReal.coe_one,
      ENNReal.coe_toNNReal (ENNReal.div_ne_top hM hε0)]
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by
    rw [hCcoe]
    exact (lt_of_lt_of_le one_pos le_add_self).ne'
  refine ⟨C, fun n => ?_⟩
  -- pointwise Chebyshev truncation bound, valid at every `x`
  have hpt : ∀ x, ‖({x | C ≤ ‖Z n x‖₊}.indicator (Z n)) x‖ₑ ≤ ‖Z n x‖ₑ ^ 2 / C := by
    intro x
    by_cases hx : x ∈ {x | C ≤ ‖Z n x‖₊}
    · rw [Set.indicator_of_mem hx]
      have hCle : (C : ℝ≥0∞) ≤ ‖Z n x‖ₑ := by
        rw [enorm_eq_nnnorm]
        exact_mod_cast hx
      calc ‖Z n x‖ₑ = ‖Z n x‖ₑ * ((C : ℝ≥0∞) / C) := by
            rw [ENNReal.div_self hC0 ENNReal.coe_ne_top, mul_one]
        _ = ‖Z n x‖ₑ * C / C := by rw [mul_div_assoc]
        _ ≤ ‖Z n x‖ₑ * ‖Z n x‖ₑ / C := by gcongr
        _ = ‖Z n x‖ₑ ^ 2 / C := by rw [sq]
    · rw [Set.indicator_of_notMem hx]
      simp
  calc eLpNorm ({x | C ≤ ‖Z n x‖₊}.indicator (Z n)) 1 ν
      = ∫⁻ x, ‖({x | C ≤ ‖Z n x‖₊}.indicator (Z n)) x‖ₑ ∂ν :=
        eLpNorm_one_eq_lintegral_enorm
    _ ≤ ∫⁻ x, ‖Z n x‖ₑ ^ 2 / C ∂ν := lintegral_mono hpt
    _ = (∫⁻ x, ‖Z n x‖ₑ ^ 2 ∂ν) / C := by
        simp_rw [ENNReal.div_eq_inv_mul]
        exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hC0)
    _ = (∫⁻ x, ENNReal.ofReal (Z n x) ^ 2 ∂ν) / C := by
        congr 1
        refine lintegral_congr_ae ((hnonneg n).mono fun x hx => ?_)
        simp only [Pi.zero_apply] at hx
        simp only [Real.enorm_of_nonneg hx]
    _ ≤ M / C := by gcongr; exact hL2 n
    _ ≤ ENNReal.ofReal ε := by
        rw [ENNReal.div_le_iff hC0 ENNReal.coe_ne_top]
        calc M = M / ENNReal.ofReal ε * ENNReal.ofReal ε :=
              (ENNReal.div_mul_cancel hε0 ENNReal.ofReal_ne_top).symm
          _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal ε := by
              gcongr
              rw [hCcoe]
              exact le_self_add
          _ = ENNReal.ofReal ε * C := mul_comm _ _

/-- **A locally consistent density process is automatically a martingale.** If each `Z n` is
`ℱ n`-strongly measurable, a.e. nonnegative, and integrates on every `ℱ n`-set to the
`μ`-measure of that set, then `Z` is a `ν`-martingale: for `s ∈ ℱ i ⊆ ℱ j` both `∫_s Z i dν`
and `∫_s Z j dν` equal `(μ s).toReal`, so the tower property is forced by uniqueness of the
conditional expectation (`ae_eq_condExp_of_forall_setIntegral_eq`). No distributional
computation about `Z` is needed — the martingale property is *free* from the consistency of
the local-density identities across levels. -/
theorem martingale_of_setLIntegral_eq
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m) (Z : ℕ → Ω → ℝ)
    (hadapted : StronglyAdapted ℱ Z)
    (hnonneg : ∀ n, 0 ≤ᵐ[ν] Z n)
    (hdens : ∀ n, ∀ s, MeasurableSet[ℱ n] s → μ s = ∫⁻ x in s, ENNReal.ofReal (Z n x) ∂ν) :
    Martingale Z ℱ ν := by
  have hint : ∀ n, Integrable (Z n) ν := by
    intro n
    refine ⟨((hadapted n).mono (ℱ.le n)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_congr_ae ((hnonneg n).mono fun x hx => by rw [Real.enorm_of_nonneg hx]),
      ← setLIntegral_univ, ← hdens n Set.univ MeasurableSet.univ, measure_univ]
    exact ENNReal.one_lt_top
  -- on an `ℱ n`-set, `∫ Z k dν = (μ s).toReal` for every `k ≥ n`
  have hsetint : ∀ n k, n ≤ k → ∀ s, MeasurableSet[ℱ n] s →
      ENNReal.ofReal (∫ x in s, Z k x ∂ν) = μ s := fun n k hnk s hs => by
    rw [ofReal_integral_eq_lintegral_ofReal ((hint k).restrict)
      (ae_restrict_of_ae (hnonneg k)), ← hdens k s (ℱ.mono hnk s hs)]
  refine ⟨hadapted, fun i j hij => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) (hint j)
    (fun s _ _ => (hint i).integrableOn) (fun s hs _ => ?_)
    (hadapted i).aestronglyMeasurable).symm
  exact (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg_of_ae (ae_restrict_of_ae (hnonneg i)))
      (integral_nonneg_of_ae (ae_restrict_of_ae (hnonneg j)))).mp
    ((hsetint i i le_rfl s hs).trans (hsetint i j hij s hs).symm)

/-- **Absolute continuity from `L²`-bounded local densities** — the composition of
`absolutelyContinuous_of_densityProcess` with the two reductions above. A candidate
probability measure `μ` that is locally absolutely continuous along a generating filtration,
with density process `Z` uniformly bounded in `L²(ν)`, is globally `μ ≪ ν`. The martingale
property is automatic (`martingale_of_setLIntegral_eq`) and the `L²` bound gives uniform
integrability (`uniformIntegrable_one_of_lintegral_sq_bdd`), so the call site needs *only*
the local densities and one moment bound — the exact interface of the Gaussian
Cameron–Martin application (`PLAN_CONTINUUM_CLOSURE.md` M2.8). -/
theorem absolutelyContinuous_of_localDensity
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m) (hgen : ⨆ n, ℱ n = m)
    (Z : ℕ → Ω → ℝ) (hadapted : StronglyAdapted ℱ Z)
    (hnonneg : ∀ n, 0 ≤ᵐ[ν] Z n)
    (hdens : ∀ n, ∀ s, MeasurableSet[ℱ n] s → μ s = ∫⁻ x in s, ENNReal.ofReal (Z n x) ∂ν)
    {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hL2 : ∀ n, ∫⁻ x, ENNReal.ofReal (Z n x) ^ 2 ∂ν ≤ M) :
    μ ≪ ν :=
  absolutelyContinuous_of_densityProcess μ ν ℱ hgen Z
    (martingale_of_setLIntegral_eq μ ν ℱ Z hadapted hnonneg hdens)
    (uniformIntegrable_one_of_lintegral_sq_bdd
      (fun n => ((hadapted n).mono (ℱ.le n)).aestronglyMeasurable) hM hL2 hnonneg)
    hnonneg hdens

end ForMathlib.MeasureTheory
