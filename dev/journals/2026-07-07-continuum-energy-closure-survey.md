# Survey — closing the DRSB continuum energy identity (2026-07-07)

**Author:** Claude Opus 4.8 (continuing the survey started by Claude Fable 5).
**Scope:** finish the feasibility survey of what it takes to close
`ChenGeorgiouPavon2021.energy_identity`'s **continuum** Cameron–Martin edge (`hCM`)
*edge-free*, verified against the currently pinned Mathlib
(`leanprover/lean4:v4.32.0-rc1`, Mathlib `inputRev = master`). This report grades each
remaining "brick" from Session 5's plan (`JOURNAL.md`) by the infrastructure the pin
actually provides. **No proofs were written this pass — this is a survey.**

Companion docs: [`ROADMAP_ENERGY_IDENTITY.md`](../../ROADMAP_ENERGY_IDENTITY.md) (the
Phase decomposition), [`JOURNAL.md`](../../JOURNAL.md) Sessions 3–5 (the bricks), and
[`AGENTS.md`](../../AGENTS.md) §9 (status).

---

## 0. TL;DR

- **The repo is proved and dependency-clean today** (0 placeholder outside `reference/`;
  `energy_identity` is proved modulo the explicit, non-vacuous `hCM` edge). Nothing here
  is regressed or blocked at the *repo* level — this survey is about the further,
  optional goal of discharging the last continuum edge without any hypothesis.
- **Two disjoint continuum problems, very different verdicts:**
  - **Deterministic (open-loop) drift** — reachable, *not* blocked by any impossibility.
    Blocked only on **Brick 2** (a finite-dimensional Gaussian **density/RN-derivative**
    layer that the pin does not have). Multi-session, but buildable with in-pin tools.
  - **Feedback (closed-loop) drift** — genuinely blocked. Needs the **Itô/Girsanov
    stack**, which is *entirely absent* from the pin (confirmed below). Not a session, not
    a month — a Mathlib-scale upstream program.
- **The two "hard" gaps around Brick 2 are already discharged** in-repo: gap #1
  (Kolmogorov extension → `wienerMeasure`) via the vendored extension, and gap #3's
  needed `≪`-direction (Kakutani) via `absolutelyContinuous_of_densityProcess`. So the
  deterministic closure is a *single* remaining construction (Brick 2), fed by two proved
  reductions (Bricks 1.5 and 3) — see §4.

---

## 1. Method

For each brick I grepped the pinned Mathlib (`.lake/packages/mathlib/Mathlib`) for the
theorem/def it rests on, and recorded present/absent with the exact declaration name and
file. "Present" = the lemma is in the pin and usable; "absent" = grep-confirmed missing
(cross-checked against the file docstrings, which flag their own gaps). The bricks are
Session 5's decomposition (`JOURNAL.md` "Route to full deterministic closure").

---

## 2. What the pin PROVIDES (verified present)

| Capability | Declaration (pin, unless noted) | Consumed by / enables |
|---|---|---|
| 1-D Gaussian shift **density (RN-derivative)** | `ProbabilityTheory.rnDeriv_gaussianReal`, `gaussianReal_absolutelyContinuous(')`, `gaussianPDF` (`Probability/Distributions/Gaussian/Real.lean`) | the 1-D atom of Brick 2; already used by `GaussianEntropy.klDiv_gaussianReal_shift` |
| 1-D Gaussian **mgf** (for L² moment bounds) | `mgf_gaussianReal`, `mgf_id_gaussianReal` (`…/Gaussian/Real.lean:494`) | the `exp(energy)` L²-bound of the density process |
| Kolmogorov **extension existence** | `projectiveLimit`, `isProjectiveLimit_projectiveLimit`, `isProbabilityMeasure_projectiveLimit` (**vendored**, `ForMathlib/KolmogorovExtension/`) | **`ForMathlib.MeasureTheory.wienerMeasure`** = the continuum reference `R` (gap #1, discharged) |
| Brownian **projective family** (grid marginals) | `BrownianReal.projectiveFamily`, `isProjectiveMeasureFamily_projectiveFamily`, `measurePreserving_eval_sub_eval_projectiveFamily` (increment law) (`Probability/BrownianMotion/GaussianProjectiveFamily.lean`) | the grid marginals of `wienerMeasure`; independent-increment structure |
| **L¹ martingale convergence** (Lévy) | `Martingale.ae_eq_condExp_limitProcess`, `Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable`, `Integrable.tendsto_ae_condExp` (`Probability/Martingale/Convergence.lean`) | `absolutelyContinuous_of_densityProcess` (gap #3 `≪`), and `klDiv_map_tendsto` (projection-exhaustion) |
| **Chebyshev/Markov + L^p tails** | `pow_mul_meas_ge_le_eLpNorm`, `meas_ge_le_mul_pow_eLpNorm_enorm` (`…/LpSpace/Basic.lean`), `MemLp.eLpNorm_indicator_le`, `uniformIntegrable_of` (`…/UniformIntegrable.lean`) | **Brick 1.5** (L²-bounded ⇒ UI) |
| KL machinery (chain rule, DPI, per-coord tensorization) | `klDiv_compProd_eq_add`, repo's `toReal_klDiv_map_le`, `klDiv_map_tendsto(_toReal)`, `klDiv_stdGaussian_map_add` | the whole projection/embedding argument (already proved, §4) |

**Already-proved reductions that surround Brick 2** (all dependency-clean, in-repo):
`iSup_comap_frestrictLe_eq_pi` (grid filtration generates the product σ-algebra),
`PathEmbedding.*` (continuous-path embedding edge discharged),
`klDiv_emShift_eq_emEnergy` (discrete grid KL = discrete energy),
`tendsto_emEnergy_sampled` + `tendsto_equispaced_riemannSum` (Δt→0 Riemann limit),
`absolutelyContinuous_of_densityProcess` (Kakutani `≪`).

---

## 3. What the pin LACKS (grep-confirmed absent)

| Missing capability | Evidence | Which brick/case it blocks |
|---|---|---|
| **Finite-dim / multivariate Gaussian density (RN-derivative)** | `Probability/Distributions/Gaussian/Multivariate.lean` has **no** `rnDeriv`/`withDensity`/`pdf`/`absolutelyContinuous` (only the 1-D `Real.lean` does) | **Brick 2** (the correlated-coordinate density) |
| **Brownian bridge / Gaussian conditional-expectation structure** | no `BrownianBridge`, no `condExp`-of-Gaussian, no `condDistrib`-Gaussian in `Probability/` | **Brick 2** martingale property under *non-nested* grid refinement |
| **Itô/stochastic integral, Girsanov, stochastic exponential, Doléans** | grep of the whole pin for `stochasticIntegral`/`Girsanov`/`stochasticExponential`/`Doleans` → **nothing**; `BrownianMotion/` holds only `Basic.lean` + `GaussianProjectiveFamily.lean` | **feedback-drift** continuum `hCM` (gap #2) — hard block |
| **Kolmogorov extension in-pin** | `MeasureTheory/Constructions/ProjectiveFamilyContent.lean:28` still says *"not yet in Mathlib"* | gap #1 — worked around by the **vendor** (so not a live blocker) |
| **Kakutani / infinite-product absolute continuity** | only `RieszMarkovKakutani` (unrelated) + `Prokhorov` (tightness) present | gap #3 — worked around by the **martingale** route (`absolutelyContinuous_of_densityProcess`), so not a live blocker for the `≪` we need |

---

## 4. Brick-by-brick verdict (deterministic closure)

Session 5 factored the deterministic continuum identity into Bricks 1.5 / 2 / 3. Updated
grades against the pin:

- **Brick 1.5 — L²-bounded ⇒ UI density martingale. Verdict: FEASIBLE, moderate (~T2).**
  All ingredients present: Chebyshev (`meas_ge_le_mul_pow_eLpNorm_enorm`) bounds the tail
  measure `ν{|Zₙ| ≥ C} ≤ C⁻²·eLpNorm(Zₙ,2)²`, Hölder/`MemLp.eLpNorm_indicator_le` turns a
  uniform L² bound into a uniform L¹ tail, and `uniformIntegrable_of` packages it. No
  missing theory — this is a self-contained lemma feeding `absolutelyContinuous_of_densityProcess`'s
  `hUI` hypothesis. This is the cheap brick.

- **Brick 2 — construct the Cameron–Martin density process on `wienerMeasure` and prove it
  is an L²-bounded martingale. Verdict: REACHABLE but the real cost centre; multi-session.**
  This is where the pin's gap bites. Two honest routes, each with a concrete obstruction:
  - **(2a) Correlated-coordinate route.** Work directly with the position-grid marginals
    `BrownianReal.projectiveFamily I` (centered Gaussian, covariance `min s t`). Needs the
    **multivariate Gaussian RN-derivative** — *absent* (§3). Would require building
    finite-dim Gaussian densities (a genuine, upstreamable Mathlib sub-gap) plus their
    conditional (Brownian-bridge) structure to get the martingale property. Largest lift.
  - **(2b) Increment-coordinate route (recommended).** In *increment* coordinates the
    Wiener grid marginal is a **product of independent** centered Gaussians
    (`measurePreserving_eval_sub_eval_projectiveFamily` gives the increment law), so the
    deterministic CM shift density **factorizes** into 1-D `rnDeriv_gaussianReal` factors —
    exactly the product structure `klDiv_stdGaussian_map_add` already exploits. The density
    process along a **nested (dyadic)** increment filtration is then a *product martingale*
    (each refinement multiplies by an independent, mean-one factor; `E[Zₙ₊₁|ℱₙ]=Zₙ` from
    independence — provable with in-pin tools), and its L² bound is `exp(partial CM energy)`
    via `mgf_gaussianReal`. **Remaining friction, both real but bounded:** (i) tie the
    nested-increment filtration to the position/`frestrictLe`-over-`denseSeq` filtration
    that `iSup_comap_frestrictLe_eq_pi` / `PathEmbedding` consume (a linear
    change-of-coordinates + a generation argument for the nested grid); (ii) handle grid
    *refinement* — a fresh dense time splits one increment into two dependent pieces
    (Brownian-bridge conditioning), which is why the *nested* dyadic grid is used to keep
    factors independent. Neither needs the Itô integral. This route avoids the missing
    multivariate density entirely by staying in the product world, at the price of the
    nesting bookkeeping.

- **Brick 3 — assemble the deterministic identity. Verdict: FEASIBLE once Brick 2 lands.**
  `P^u := R.withDensity Zlim` makes `P^u ≪ R` free (Brick 1 / `withDensity_absolutelyContinuous`);
  the grid marginals are the shifted Gaussians by the tower property
  (`ae_eq_condExp_limitProcess`); grid KL = CM energy is the proved discrete layer; Riemann
  → `∫₀¹½‖u‖²` is `tendsto_emEnergy_sampled`; and the projection/embedding identity
  (`eq_toReal_klDiv_continuousMap_of_tendsto`) closes it. Pure plumbing of proved pieces —
  no new theory, contingent only on Brick 2 exhibiting the density martingale.

**Feedback-drift continuum identity — Verdict: BLOCKED (unchanged).** The RN-derivative
between the controlled and reference path measures *is* a stochastic (Doléans) exponential
`exp(∫u dW − ½∫‖u‖²)`; with no stochastic integral in the pin (§3) there is no non-faked
route. This is a fact about the mathematics, not a matter of effort. It stays the honest
`hCM` edge whose **discrete** instance (`energy_identity_euler_maruyama`) is already proved.

---

> **Follow-up (same day):** this survey's recommendations have been expanded into a
> ticket-level implementation plan — see [`PLAN_CONTINUUM_CLOSURE.md`](../../PLAN_CONTINUUM_CLOSURE.md)
> (Theorem A = the infinite-dimensional Cameron–Martin KL identity on the iid Gaussian
> sequence model, milestones M1–M5 with exact statements, pin lemmas, and pitfalls).

## 5. Recommendation

1. **Land Brick 1.5 now** as a standalone `ForMathlib` lemma (`eLpNorm`-bounded family ⇒
   `UniformIntegrable … 1`). It is cheap, self-contained, immediately upstreamable, and
   unblocks the `hUI` hypothesis of the already-proved `absolutelyContinuous_of_densityProcess`.
2. **Scope Brick 2 as route (2b)** (increment/product + nested dyadic filtration). Break it
   into: (a) the 1-D shifted-Gaussian factor as a mean-one L²-bounded `gaussianReal`
   density (present tools); (b) the finite product martingale along the nested grid; (c) the
   filtration-identification lemma to `frestrictLe`. Each is a separate landable target;
   (c) is the subtle one and deserves its own scratch file.
3. **Do not spend cycles on the feedback/Itô case** against this pin — record it as the
   standing gap #2 and revisit only if/when a stochastic-integral stack is ported or the pin
   gains one. (`SURVEY_LEADS.md`: `raphaelrrcoelho/formal-mathfin` is the 1-D Itô/Girsanov
   candidate, but it is finance-flavoured and KL-free — a foundation, not a drop-in.)
4. **Optional upstream win independent of DRSB:** the missing **multivariate Gaussian
   RN-derivative** (§3) is a clean, self-contained Mathlib gap. Filling it would make route
   (2a) viable *and* is valuable to Mathlib on its own — a good "ForMathlib → PR" candidate
   regardless of whether the continuum closure is pursued.

## 6. Honesty check

Nothing above is faked or hand-waved. The deterministic closure is graded *reachable*
because every step except Brick 2's density factor uses a verified-present pin lemma, and
Brick 2 route (2b) reduces to independent 1-D Gaussian densities that the pin *does* have.
The feedback closure is graded *blocked* because the stochastic integral it requires is
grep-confirmed absent. The current repo remains proved and dependency-clean; these bricks are
about removing the last *hypothesis* (`hCM`), not any placeholder.
