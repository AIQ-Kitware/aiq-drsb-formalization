# DRSB formalization — challenge manifest

This repository formalizes the DRSB (Distributionally-Robust Schrödinger Bridge)
evaluation-card claims (the **end states**) and, in the course of proving them, produced
a number of reusable, Mathlib-quality results (the **hard upstream proofs**). The
challenges are organized into two families that separate *role* and *upstream readiness*:

```
Challenge/
  MathlibCandidate/  — drop-ready upstream PRs, one folder per PR
  MathlibPending/    — proven, but not yet PR-shaped (needs generality / destination / sharpening)
```

The DRSB source-paper libraries (`BlanchetMurthy2019`, `GaoKleywegt2023`,
`MohajerinEsfahaniKuhn2018`, `WangGaoXie2023`, `ChenGeorgiouPavon2021`) and the `Drsb`
capstone — the repo's actual **end states** — are documented below and in `STATUS.md`, but
they are deliberately **not** comparator challenges: their statements are inherently in
each paper's own vocabulary (`couplings`, `couplingCost`, `sinkhornBall`, `droValue`, …),
and the comparator can compare a named proof and its reported dependencies, but it cannot certify that
those definitions faithfully model the paper. That faithfulness is a human reading task, so
a comparator artifact there would add no trust. The comparators stay purely
Mathlib-candidate-focused.

Principles:

- **Public entry points only.** Each challenge lists the theorems a reviewer would actually
  import, not the supporting lemmas. `#print axioms` on a listed theorem transitively
  certifies its entire proof tree. Where one listed theorem is a corollary of another
  (both are public API of the same proposed PR), the axiom gate is transitive either way.
- **Dependency gate.** For each project-backed `Leaderboard` leaf, record the literal
  `#print axioms` output after rebuilding the relevant module. The 2026-07-10 maintainer report
  lists only `propext, Classical.choice, Quot.sound` for the audited project proofs. This statement
  does not apply to `Conformance.lean`, whose admitted specifications are intentional.
- **Mathlib-only conformance.** `Conformance.lean` imports *only* Mathlib and states the
  theorems as `sorry`. A result whose statement names a project definition therefore cannot
  have one; those carry an axiom-audit `Leaderboard` only, and no comparator config.
- **No false dependency arrows.** The Mathlib contributions are *independent*, reusable
  results. They were *motivated* by the DRSB work but are not owned by any paper, so this
  manifest does not link candidates to papers as dependencies.

Gap claims below were checked against this repo's Mathlib checkout (`.lake/packages/mathlib`,
tracking master) on 2026-07-10.

---

## Family 1 — `MathlibCandidate/` (the focused upstream push)

**Strategy: a small, strong opening hand.** Three canonical results, each a verified gap in
Mathlib, are enough to establish credibility and earn maintainer engagement for the rest.

| # | Challenge | Leaf theorem(s) | Destination | Why it clears the bar |
|---|---|---|---|---|
| 01 | DonskerVaradhan | `isGreatest_donskerVaradhan`, `log_integral_exp_eq_sSup` | `InformationTheory/KullbackLeibler/DonskerVaradhan.lean` | The **Gibbs variational formula**. Mathlib has `Measure.tilted` and all its `llr` infrastructure but **no Donsker–Varadhan statement** (`grep -ril donsker Mathlib` → nothing). Canonical, textbook |
| 02 | KLConvexity | `klDiv_mix_le`, `klDiv_mix_ne_top`, `toReal_klDiv_mix_le` | `InformationTheory/KullbackLeibler/Convex.lean` | **Convexity of relative entropy in its first argument**, `ℝ≥0∞`-valued and hypothesis-free. Mathlib has `klDiv_smul_same` / `klDiv_smul_right_eq_smul_left` but **no convexity**, in either `ℝ` or `ℝ≥0∞`. Canonical |
| 03 | Supergradient | `exists_supergradient_of_concaveOn(')`, `exists_nonneg_multiplier(')` | `Analysis/Convex/Supergradient.lean` | Mathlib has `ConcaveOn` and the slope lemmas but **no sub/supergradient existence at all** (`grep -rn 'supergradient\|subgradient' Mathlib` → nothing). Canonical convex analysis |

---

## Family 2 — `MathlibPending/` (proven, but held back)

The project-backed `Leaderboard` proofs were reported with the same scoped dependency output as
the candidate leaves, but these results are **not** part of the opening push — each either needs
work to clear the maintainer bar, or is held until the headline three land. Each may graduate.

| Challenge | Leaf theorem(s) | Why pending |
|---|---|---|
| KLChainRule | `klDiv_compProd_eq_lintegral`, `toReal_klDiv_compProd_eq_integral` | Mathlib **has** the *additive* chain rule (`klDiv_compProd_eq_add`, `klDiv_compProd_left`) but not the **disintegration** form `klDiv (μ⊗ₘκ) (μ⊗ₘη) = ∫⁻ x, klDiv (κ x) (η x) ∂μ`. Natural companion; confirm framing and destination against the existing `ChainRule.lean` |
| GibbsTilt | `klDiv_tilted_ne_top`, `entropic_gibbs_attained_tilted` | `klDiv_tilted_ne_top` is small and clearly wanted; `entropic_gibbs_attained_tilted` is stated in a DRO-shaped form (a `λ`, `κ`-parametrised Lagrangian) that a maintainer would likely want re-cut |
| MeasurableArgmax | `exists_measurable_eps_argmax`, `sSup_image_dense_eq`, `exists_measurable_eps_argmax_of_separable` | A **measurable ε-argmax selector** — the Kuratowski–Ryll-Nardzewski-free substitute (countable index / separable domain). Mathlib has no measurable-selection theory; confirm this is the shape it would want, not a special case of one |
| KLLowerSemicontinuous | `toReal_klDiv_le_of_tendsto_integral` | **Setwise lsc of `klDiv`**, via the DV *dual* variational formula. Proven, but the surrounding `dvDualSet` API is project-local, so the statement is currently a bespoke `Tendsto`-hypothesis form rather than a `LowerSemicontinuous` instance. Needs re-shaping |
| IntegrableIntegralCompProd | `integrable_integral_compProd` | The **measure-level** `Integrable.integral_compProd`; Mathlib has only the kernel-level one (`ProbabilityTheory`, `(κ ⊗ₖ η) a`). Genuinely absent, but **too small** to stand alone — should ride along with another PR |
| TiltedKernel | `tiltedKernel_apply`, `isMarkovKernel_tiltedKernel`, `measurable_tiltedKernel_normalizer` | The parametrized/kernel form of `Measure.tilted` (Mathlib has it only for a single potential). Statements name the project definition `tiltedKernel`, so they are **not cleanly Mathlib-only expressible**: **axiom-audit `Leaderboard` only, no `Conformance`/comparator config** |
| BirkhoffHopf | `positive_kernel_birkhoff_hopf_contraction_of_apply_hilbert_log_diameter_bound` | **Birkhoff–Hopf contraction** in the Hilbert projective metric. Mathlib's `Analysis/Convex/Birkhoff.lean` is Birkhoff–**von Neumann** (doubly stochastic matrices); the contraction theorem and the projective metric are absent. Statement names project definitions (`IsBirkhoffHopfContractionCoefficient`, `positiveKernelBirkhoffCoefficient`), so **`Leaderboard` only** until the metric is given a Mathlib-shaped definition |

---

## DRSB libraries — the repo's end states (documented, not comparator challenges)

These are the source-paper layers and capstone results that motivated much of the reusable work.
They are **not** comparator challenges (see the rationale in the intro). Dependency reports should
be attached to named declarations, not summarized as a property of an entire library. The two card
theorems were reported with `#print axioms = {propext, Classical.choice, Quot.sound}` at the
snapshot documented in `STATUS.md`.

| Library | Main theorem(s) | Recorded status |
|---|---|---|
| Drsb (capstone) | `wdrsb_cost_bound`, `sdrsb_cost_bound` (the two MAGNET card claims; neither takes an explicit duality-gap hypothesis), `wdrsb_strong_duality_of_regularity`, `sdrsb_strong_duality`, `sdrsb_strong_duality_of_radius_gt_independent_cost` | see named reports / rebuild before use |
| WangGaoXie2023 | `strong_duality` (Sinkhorn/entropic DRO; no `hge` parameter, uses a checkable Slater hypothesis), `sinkhornDual_le_droValue`, `sinkhorn_cost_bound` | see named reports / rebuild before use |
| GaoKleywegt2023 | `strong_duality_thm1_of_regularity`, `weak_duality_prop1` | see named reports / rebuild before use |
| BlanchetMurthy2019 | `strong_duality_thm1` | see named reports / rebuild before use |
| MohajerinEsfahaniKuhn2018 | `strong_duality` | see named reports / rebuild before use |
| ChenGeorgiouPavon2021 | Schrödinger-bridge / SOC value function, Sinkhorn convergence, energy identity | see named reports / rebuild before use |

---

## Running the checks

```bash
# cheap pre-flight: universe signature + full type, Conformance vs Leaderboard
python3 scripts/check_comparator_signatures.py

# the real thing (needs the comparator toolchain; see scripts/install_comparator_tools.sh)
bash scripts/run_challenge_comparator.sh
```

`lake build Challenge` does **not** work (there is no `Challenge.lean` root module, by design —
the same shape as `aiq-dkps-formalization`); build individual modules instead, e.g.
`lake build Challenge.MathlibCandidate.DonskerVaradhan.Leaderboard`.
