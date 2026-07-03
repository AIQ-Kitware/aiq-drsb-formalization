/-
# Alquier2024 — core theorems of the PAC-Bayes "user-friendly introduction"

Statements-only scaffold (all bodies `sorry`) of the three published ingredients of
Pierre Alquier, *"User-friendly introduction to PAC-Bayes bounds"*
(Foundations and Trends in Machine Learning, 2024; arXiv:2110.11216) that underpin
the DRSB "TwoPager" **Theorem 4** (a PAC-Bayes bound for the clipped terminal-cost
network `g ∈ [−C, C]`).

Prose reference (all lemma/theorem numbers transcribed there from the PDF, not from
memory): `prose/pac-bayes-generalization.md`.

Abstract learning problem (prose §1.1, around p. 179):
* a measurable hypothesis/parameter space `Θ`;
* a fixed **prior** `π : ProbabilityMeasure Θ` and **posterior(s)** `ρ`;
* a bounded loss `ℓ : Θ → 𝒳 → ℝ`, an i.i.d. sample `S ∼ Dⁿ`;
* **population risk** `R θ = 𝔼_{x∼D}[ℓ θ x]` and **empirical risk**
  `r θ S = (1/n) Σᵢ ℓ θ (Sᵢ)`, with `𝔼_S[r θ] = R θ`.

Throughout `𝔼_ρ[·] = ∫ · ∂(ρ : Measure Θ)` and `KL(ρ‖π) = (klDiv ρ π).toReal`.

The Donsker–Varadhan facts are already proved in `ForMathlib.MeasureTheory`
(`integral_le_klDiv_add_log_integral_exp`, `log_integral_exp_eq_sSup`); Lemma 2.2
below is re-exported from there.
-/
import Mathlib
import ForMathlib.MeasureTheory.DonskerVaradhan

set_option autoImplicit false

open MeasureTheory InformationTheory
open scoped ENNReal

namespace Alquier2024

/-! ## Lemma 1.1 — Hoeffding's inequality (bounded-variable MGF bound) -/

/-- **Lemma 1.1 (Hoeffding's inequality)** — prose `pac-bayes-generalization.md`,
"Lemma 1.1", the bounded-variable MGF bound.

Let `U₁,…,Uₙ` be independent random variables taking values in `[a, b]`. Then for any
`t > 0`,
`𝔼[exp(t · Σᵢ (Uᵢ − 𝔼 Uᵢ))] ≤ exp(n t² (b−a)² / 8)`.

Here `𝔼 Uᵢ = ∫ Uᵢ dP` and the sum runs over the `n` coordinates. Applied at
`Uᵢ = 𝔼[ℓᵢ(θ)] − ℓᵢ(θ)` with loss in `[0, C]` (Alquier's Proposition 1.1, p. 179)
this yields the single-hypothesis bound `𝔼_S[e^{t n (R−r)}] ≤ e^{n t² C² / 8}`. -/
theorem hoeffding_mgf_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (U : Fin n → Ω → ℝ)
    -- `U₁,…,Uₙ` are independent random variables …
    (hindep : ProbabilityTheory.iIndepFun U P)
    (hmeas : ∀ i, Measurable (U i))
    -- … each taking values in the interval `[a, b]`
    {a b : ℝ} (hU : ∀ i ω, U i ω ∈ Set.Icc a b)
    -- for any `t > 0`
    {t : ℝ} (ht : 0 < t) :
    (∫ ω, Real.exp (t * ∑ i : Fin n, (U i ω - ∫ ω', U i ω' ∂P)) ∂P)
      ≤ Real.exp ((n : ℝ) * t ^ 2 * (b - a) ^ 2 / 8) := by
  sorry

/-! ## Lemma 2.2 — Donsker and Varadhan's variational formula

Re-exported from `ForMathlib.MeasureTheory` (the DV inequality
`integral_le_klDiv_add_log_integral_exp` and variational identity
`log_integral_exp_eq_sSup` are proved there). -/

variable {Θ : Type*} [MeasurableSpace Θ]

/-- **Lemma 2.2 (Donsker and Varadhan's variational formula)** — prose
`pac-bayes-generalization.md`, "Lemma 2.2".

For a fixed prior `π`, over posteriors `ρ ∈ 𝒫(Θ)`,
`log 𝔼_{θ∼π}[e^{h(θ)}] = sup_ρ (𝔼_{θ∼ρ}[h(θ)] − KL(ρ‖π))`,
the supremum being attained at the Gibbs measure `π.tilted h ∝ e^h dπ`
(Alquier Eq. (2.1)).

Re-exported from `ForMathlib.MeasureTheory.log_integral_exp_eq_sSup`; the
`ProbabilityMeasure`-typed side conditions (`ρ ≪ π`, integrability of `h` and of the
log-likelihood ratio) make the identity well-posed. -/
theorem donskerVaradhan_variational
    (π : ProbabilityMeasure Θ) {h : Θ → ℝ}
    (hexp : Integrable (fun θ => Real.exp (h θ)) (π : Measure Θ))
    (htilted : Integrable h ((π : Measure Θ).tilted h)) :
    Real.log (∫ θ, Real.exp (h θ) ∂(π : Measure Θ))
      = sSup { s : ℝ | ∃ ρ : ProbabilityMeasure Θ,
          (ρ : Measure Θ) ≪ (π : Measure Θ) ∧
          Integrable h (ρ : Measure Θ) ∧
          Integrable (llr (ρ : Measure Θ) (π : Measure Θ)) (ρ : Measure Θ) ∧
          s = ∫ θ, h θ ∂(ρ : Measure Θ)
                - (klDiv (ρ : Measure Θ) (π : Measure Θ)).toReal } := by
  sorry

/-- **Lemma 2.2, change-of-measure form** — prose `pac-bayes-generalization.md`,
"Lemma 2.2" specialized (the boxed inequality the DRSB chain actually uses).

Dropping the supremum and keeping a single posterior `ρ` gives
`𝔼_{θ∼ρ}[h(θ)] ≤ KL(ρ‖π) + log 𝔼_{θ∼π}[e^{h(θ)}]`,
with equality at the Gibbs measure `ρ = π.tilted h`.

Re-exported from `ForMathlib.MeasureTheory.integral_le_klDiv_add_log_integral_exp`. -/
theorem donskerVaradhan_change_of_measure
    (π ρ : ProbabilityMeasure Θ) {h : Θ → ℝ}
    (hρπ : (ρ : Measure Θ) ≪ (π : Measure Θ))
    (hh : Integrable h (ρ : Measure Θ))
    (hllr : Integrable (llr (ρ : Measure Θ) (π : Measure Θ)) (ρ : Measure Θ))
    (hexp : Integrable (fun θ => Real.exp (h θ)) (π : Measure Θ)) :
    ∫ θ, h θ ∂(ρ : Measure Θ)
      ≤ (klDiv (ρ : Measure Θ) (π : Measure Θ)).toReal
        + Real.log (∫ θ, Real.exp (h θ) ∂(π : Measure Θ)) := by
  sorry

/-! ## Theorem 2.1 — Catoni's PAC-Bayes bound -/

/-- **Theorem 2.1 (Catoni's bound, Catoni 2003)** — prose
`pac-bayes-generalization.md`, "Theorem 2.1".

The loss `ℓ` is bounded and takes values in `[0, C]`. For any `λ > 0`, any
`δ ∈ (0,1)`, with probability `≥ 1 − δ` over the i.i.d. sample `S ∼ Dⁿ`,
simultaneously for **all** posteriors `ρ ∈ 𝒫(Θ)`:
`𝔼_ρ[R] ≤ 𝔼_ρ[r] + λ C² / (8n) + (KL(ρ‖π) + log(1/δ)) / λ`.

Weakening (documented): the printed theorem quantifies over *all* `ρ` with the
convention `KL(ρ‖π) = +∞` when `ρ ⋠ π` (making the bound trivial there). Mathlib's
`(klDiv ρ π).toReal` collapses `⊤` to `0`, so we guard the inequality by the
absolute-continuity hypothesis `ρ ≪ π`, on which the two conventions agree; the
`⊤`-valued case is the vacuous one.

TwoPager correspondence (prose "Exact correspondence to the TwoPager constants"):
with `λ = ε`, prior `π = Q`, posterior `ρ = P` and the clipped cost `g ∈ [−C, C]`
(range `2C`), the Hoeffding term `λ (b−a)²/(8n) = λ (2C)²/(8n) = λ C²/(2n)` becomes
TwoPager's `ε C²/(2n)`, recovering TwoPager Eq. (126). (This only records the
constant match; the unpublished TwoPager theorem is not restated here.) -/
theorem catoni_pacBayes_bound
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (π : ProbabilityMeasure Θ) (D : ProbabilityMeasure 𝒳)
    {n : ℕ} (hn : n ≠ 0)
    (ℓ : Θ → 𝒳 → ℝ) (R : Θ → ℝ) (r : Θ → (Fin n → 𝒳) → ℝ)
    {C lam δ : ℝ}
    -- the loss is bounded and takes values in `[0, C]`
    (hℓmeas : Measurable (Function.uncurry ℓ))
    (hℓb : ∀ θ x, ℓ θ x ∈ Set.Icc (0 : ℝ) C) (hC : 0 ≤ C)
    -- population risk  `R θ = 𝔼_{x∼D}[ℓ θ x]`
    (hR : ∀ θ, R θ = ∫ x, ℓ θ x ∂(D : Measure 𝒳))
    -- empirical risk   `r θ S = (1/n) Σᵢ ℓ θ (Sᵢ)`  over the i.i.d. sample `S ∼ Dⁿ`
    (hr : ∀ θ S, r θ S = (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i))
    -- `λ > 0` (written `lam`, since `λ` is reserved) and `δ ∈ (0,1)`
    (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi (fun _ : Fin n => (D : Measure 𝒳)))
        { S | ∀ ρ : ProbabilityMeasure Θ,
            (ρ : Measure Θ) ≪ (π : Measure Θ) →
              ∫ θ, R θ ∂(ρ : Measure Θ)
                ≤ (∫ θ, r θ S ∂(ρ : Measure Θ))
                  + lam * C ^ 2 / (8 * (n : ℝ))
                  + ((klDiv (ρ : Measure Θ) (π : Measure Θ)).toReal
                      + Real.log (1 / δ)) / lam }
      ≥ ENNReal.ofReal (1 - δ) := by
  sorry

end Alquier2024
