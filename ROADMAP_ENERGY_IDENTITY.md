# Roadmap — closing `ChenGeorgiouPavon2021.energy_identity` (the last sorry)

The repo's sole remaining `sorry` is the continuous energy identity (CGP eq. 4.19):

```
D(P^{u,ρ₀} ‖ R) = D(ρ₀ ‖ ρ₀^W) + 𝔼_{P^{u,ρ₀}}[∫₀¹ ½‖u_t‖² dt]
```

It is **not an open problem** — it is a known Girsanov consequence. It is only a `sorry`
because Mathlib lacks a *packaged* multi-dim Girsanov / KL-between-path-measures. This document
breaks it into small, individually-landable pieces and identifies exactly which Mathlib results
each rests on. The goal: convert one monolithic `sorry` into proved reductions + one atomic,
honestly-labelled Girsanov edge, then close that edge.

## The decomposition

Disintegrate both path laws over the initial coordinate `X₀`. For a *feedback* control
`u(t,x)` the conditional law given `X₀ = x` is the SDE-from-`x`, a Markov kernel independent of
the initial marginal:

```
P^{u,ρ₀} = ρ₀   ⊗ₘ Kᵘ        (Kᵘ_x = law of dX=u dt+√ε dW from x)
R        = ρ₀^W ⊗ₘ Kᵂ        (Kᵂ_x = reference/Wiener law from x)
```

Then the identity splits into three independent facts:

| # | Fact | Status / Mathlib basis |
|---|------|------------------------|
| **(★)** | `D(P‖R) = D(ρ₀‖ρ₀^W) + D(ρ₀⊗ₘKᵘ ‖ ρ₀⊗ₘKᵂ)` (marginal / chain-rule split) | **Provable now.** `InformationTheory.klDiv_compProd_eq_add` — *"holds without any assumption on the measurable spaces"*, so `Path X = ℝ→X` is fine. Real-valued version = that + `ENNReal.toReal_add`. |
| **(cond)** | `D(ρ₀⊗ₘKᵘ ‖ ρ₀⊗ₘKᵂ) = ∫ D(Kᵘ_x ‖ Kᵂ_x) dρ₀(x)` (conditional KL = averaged pointwise KL) | **Provable now** from the same file's `μ[fun x ↦ klDiv (κ x)(η x)]` form + kernel-integral API. |
| **(CM)** | `∫ D(Kᵘ_x ‖ Kᵂ_x) dρ₀(x) = 𝔼_P[∫₀¹ ½‖u_t‖² dt]` (per-trajectory Cameron–Martin / Girsanov) | **The one hard edge.** Discrete Euler–Maruyama layer already proved: `ForMathlib…klDiv_emShift_eq_emEnergy`. Remaining: the `Δt→0` limit. |

So the *entire* Girsanov content is (CM), and (CM) itself already has its discrete half proved.

## Phases

### Phase 0 — real-valued chain-rule backbone (LAND FIRST, no SDE)
- `ForMathlib/MeasureTheory/KLChainRule.lean`: `toReal_klDiv_compProd_eq_add` (real-valued (★))
  and `toReal_klDiv_condKernel` (real-valued (cond), the averaged-pointwise form).
- Pure Mathlib re-export + `toReal` bookkeeping; axiom-clean; reusable. **Deliverable this pass.**

### Phase 1 — wire the split into `energy_identity` (house pattern)
- Enrich `SBData` (or add hypotheses) with the disintegration data: Markov kernels `Kᵘ`, `Kᵂ`
  and structural edges `P = ρ₀ ⊗ₘ Kᵘ`, `R = ρ₀^W ⊗ₘ Kᵂ` (true by construction for diffusions),
  plus the finiteness edges `D(ρ₀‖ρ₀^W) ≠ ⊤`, `D(cond) ≠ ⊤` (finite-energy regime, cf. `hfin` in
  `dynamic_eq_static_SB`).
- Prove `energy_identity` **sorry-free** = (★)∘Phase 0 + one explicit edge
  `hCM : ∫ D(Kᵘ_x‖Kᵂ_x) dρ₀ = energy`. **Sorry count 1 → 0**; the Girsanov content is now the
  single named, non-vacuous hypothesis `hCM`, exactly the repo's isolate-content-to-an-edge pattern.

### Phase 1.5 — (cond): conditional KL = averaged pointwise KL (Mathlib's own TODO)
`InformationTheory/KullbackLeibler/ChainRule.lean` explicitly lists as a **TODO**: the integral
form `klDiv (μ⊗ₘκ) (μ⊗ₘη) = μ[fun x ↦ klDiv (κ x) (η x)]`. Proving it (real-valued) reduces `hCM`
from the compProd form to the **per-trajectory Cameron–Martin atom**
`∫ D(Kᵘ_x ‖ Kᵂ_x) dρ₀ = 𝔼[∫½‖u‖²]`, which is *exactly* the object whose discrete instance
`klDiv_emShift_eq_emEnergy` proves. Achievable now (pieces: `rnDeriv_compProd`,
`Kernel.rnDeriv`, `integral_compProd`) but PR-sized (that is why Mathlib left it a TODO); a good
standalone Mathlib contribution. **Does not by itself close (CM)** — it tightens the edge.

### Phase 2 — discharge (CM): the `Δt→0` limit (BLOCKED on Mathlib infrastructure)
**Status (verified 2026-07):** genuinely blocked — Mathlib ships **no stochastic integral, no
Girsanov, no stochastic exponential, and no KL lower-semicontinuity** (all four grep-confirmed
absent). So both candidate routes require building substantial infrastructure; neither is a
session's work. This is a mathematical fact about what the continuum identity's proof requires
(its Radon–Nikodym derivative between path measures *is* a stochastic exponential), not a matter
of effort. The gap is reduced to the single per-trajectory Cameron–Martin atom (above), whose
**discrete Euler–Maruyama instance is already a proved theorem**.

Two routes, each a real project:
- **2a (discrete-limit).** Take `klDiv_emShift_eq_emEnergy` to the limit: Euler–Maruyama law ⇒
  SDE law (weak convergence — *absent from Mathlib*) + KL joint lsc (*absent from Mathlib*) for
  `≤`, matching `≥` from the energy Riemann sum. Avoids the Itô integral but needs SDE-convergence
  theory + KL lsc.
- **2b (Girsanov-density).** Refound `Kᵂ` on Mathlib Brownian motion; `Kᵘ = Kᵂ.withDensity Z`,
  `Z = exp(∫u dW − ½∫‖u‖²)`; `D(Kᵘ‖Kᵂ) = 𝔼_{Kᵘ}[log Z]`. Needs the stochastic integral `∫u dW`
  (*absent from Mathlib*). Port path: `raphaelrrcoelho/formal-mathfin` (Apache-2.0, 1-D
  Itô/Girsanov) → generalize to multi-D + add KL. This is the recommended long-term project.

**Bottom line:** the continuum `hCM` is a known Girsanov identity that cannot be discharged in Lean
until the Itô-integral / stochastic-analysis stack exists in (or is ported into) Mathlib. Until
then it stays an explicit, non-vacuous edge whose discrete instance is proved — the honest state.

## External-survey status (SURVEY_LEADS.md)
- `raphaelrrcoelho/formal-mathfin` (Apache-2.0): full continuous Itô/SDE-existence/Girsanov, but
  **1-D / finance-flavoured, no KL** → the foundation for route 2b, not drop-in.
- `RemyDegenne/brownian-motion` (Apache-2.0): Brownian construction complete, **no Girsanov**.
- `mrdouglasny/gibbs-variational` (VENDORED): finite Cameron–Martin `klDiv_stdGaussian_map_add`
  → already powers the proved discrete layer `klDiv_emShift_eq_emEnergy`.
- Mathlib now ships: `InformationTheory/KullbackLeibler/ChainRule.lean` (the (★)/(cond) engine),
  `Probability/Kernel/Disintegration/*`, `Probability/BrownianMotion/*`, Gaussian processes.

## Why this is honest
Phases 0–1 do not *fake* the Girsanov content — they prove the genuinely-Mathlib-backed
chain-rule reductions and isolate the one remaining fact (CM) as an explicit, non-vacuous edge
whose discrete instance is already a theorem. Phase 2 then attacks a single, precisely-scoped
identity rather than a monolithic path-measure statement.
