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
| **(cond)** | `D(ρ₀⊗ₘKᵘ ‖ ρ₀⊗ₘKᵂ) = ∫ D(Kᵘ_x ‖ Kᵂ_x) dρ₀(x)` (conditional KL = averaged pointwise KL) | **PROVED** (`ForMathlib…klDiv_compProd_eq_lintegral`, ℝ≥0∞ form; `…toReal_klDiv_compProd_eq_integral`, real form). Closes Mathlib's own `ChainRule.lean` TODO. Needs only `μ⊗ₘKᵘ ≪ μ⊗ₘKᵂ` + the standard `CountableOrCountablyGenerated` typeclass (standard-Borel spaces). |
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

### Phase 1.5 — (cond): conditional KL = averaged pointwise KL (Mathlib's own TODO) — ✅ DONE
`InformationTheory/KullbackLeibler/ChainRule.lean` explicitly lists as a **TODO**: the integral
form `klDiv (μ⊗ₘκ) (μ⊗ₘη) = μ[fun x ↦ klDiv (κ x) (η x)]`. **Now PROVED**, both forms, axiom-clean
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`):
- `ForMathlib…klDiv_compProd_eq_lintegral` — `klDiv (μ⊗ₘκ)(μ⊗ₘη) = ∫⁻ x, klDiv (κ x)(η x) ∂μ`
  (ℝ≥0∞), hypotheses: `μ⊗ₘκ ≪ μ⊗ₘη` only;
- `ForMathlib…toReal_klDiv_compProd_eq_integral` — `(klDiv (μ⊗ₘκ)(μ⊗ₘη)).toReal
  = ∫ x, (klDiv (κ x)(η x)).toReal ∂μ` (real Bochner integral), adds `klDiv (μ⊗ₘκ)(μ⊗ₘη) ≠ ⊤`.

**Method (how it dodges the measurability wall Mathlib flagged).** We never integrate
`x ↦ klDiv (κ x)(η x)` as a black box. Instead `μ⊗ₘκ = (μ⊗ₘη).withDensity (fun p ↦ Kernel.rnDeriv κ η
p.1 p.2)` (from `κ x = η.withDensity (κ.rnDeriv η) x` a.e. + `compProd_withDensity`), so the compProd
RN-derivative *is* the jointly measurable kernel derivative; `lintegral_compProd` peels the outer
integral and each inner slice is recognised as `klDiv (κ x)(η x)`. The real form gets
`AEMeasurable`-ity of the slice map for free (it is a.e. equal to the measurable slice lintegral).

**The one structural cost: `CountableOrCountablyGenerated 𝓧 𝓨`** — the standard typeclass under
which `Kernel.rnDeriv` is jointly measurable (used throughout `Probability/Kernel/RadonNikodym`).
It holds for any standard-Borel / Polish state and value space. **Caveat for wiring into
`energy_identity`:** the *placeholder* path model `Path X = ℝ→X` (uncountable-index `Pi` σ-algebra)
is **not** countably generated, and `X` is not countable, so this typeclass is not satisfiable there
— (cond) therefore does **not** plug into the current placeholder `energy_identity` (doing so would
require a false instance = a vacuous edge, forbidden). Wiring it in requires first upgrading `Path`
to a standard-Borel continuous-path model (`C([0,1], X)` / Polish), a *modeling* step, not new
mathematics. Until then (cond) stands as a proved, reusable reduction closing Mathlib's TODO.
**Does not by itself close (CM)** — it tightens the edge to the per-trajectory atom.

**Wired, abstractly:** `ChenGeorgiouPavon2021.energy_identity_conditional` (axiom-clean) is the
`energy_identity` disintegration with (cond) applied internally, so its Girsanov edge is already the
**per-trajectory atom** `hCM : (∫⁻ x, D(Kᵘ_x ‖ Kᵂ_x) dρ₀).toReal = energyVal`. It is stated over an
*abstract* path-space factor `𝓨` carrying `CountableOrCountablyGenerated 𝒳 𝓨` as a **satisfiable
hypothesis** (a free type variable — true for standard-Borel `𝓨`), so it is a genuine conditional
theorem, *not* the vacuous edge that instantiating at `Path X = ℝ→X` would be. This is the exact
shape Phase 2 discharges: instantiate `𝓨` = standard-Borel continuous paths, build the SDE kernels,
and prove `hCM`'s continuum (Girsanov) — its discrete instance is already `energy_identity_euler_maruyama`.

### Phase 2 — the `≥` half is now Itô-FREE; only the `≤` half needs the stochastic integral
**Split of the Girsanov edge (2026-07).** The continuum identity is two inequalities; they are *not*
equally hard:
- **`≥` half — `𝔼[∫½‖u‖²] ≤ D(P^{u}‖R)` — PROVED (modulo an Itô-free convergence edge).**
  `ForMathlib…le_toReal_klDiv_of_map_tendsto` + `ChenGeorgiouPavon2021.energy_le_klReal_of_projections`
  (both axiom-clean): the KL data-processing inequality gives `D(π_# P ‖ π_# R) ≤ D(P‖R)` for every
  time-grid projection `π`; as the projected divergences → the control energy (their limit is the
  proved discrete `emEnergy` = a Riemann sum, `energy_identity_euler_maruyama`), the bound passes to
  the limit. **No stochastic integral** — only the DPI. The single remaining input, `hconv` (grid
  KLs → energy), is itself Itô-free (finite-dimensional Gaussian Cameron–Martin + Riemann sums).
- **`≤` half — `D(P^{u}‖R) ≤ 𝔼[∫½‖u‖²]` — still blocked.** This is the direction requiring the
  finite-dimensional projections to *exhaust* the σ-algebra (a martingale/RN-derivative convergence
  that recovers the full density), i.e. the genuine stochastic-exponential / Itô content. That is the
  irreducible Phase-2 core below.

### Phase 2 core (`≤` half) — discharge (CM): the `Δt→0` limit (BLOCKED on Mathlib infrastructure)
**Status (re-verified 2026-07-04 against latest-master Mathlib `d3716e6d`, Lean `v4.32.0-rc1` — pin
upgraded this day from `476fb97b62`):** genuinely blocked — Mathlib ships **no stochastic integral,
no Girsanov, no stochastic exponential, no Cameron–Martin, and no quadratic variation** (all
grep-confirmed absent even at latest master; only basic martingales + predictable processes are
present). So the `≤` half requires building
substantial infrastructure; neither route is a session's work. This is a mathematical fact about what the continuum identity's proof requires
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

#### `≤`-half sub-plan — the projection-EXHAUSTION theorem (Itô-FREE, ✅ DONE 2026-07-04)
**PROVED, axiom-clean** — `ForMathlib…klDiv_map_tendsto_toReal`:
`(klDiv (μ.map gₙ) (ν.map gₙ)).toReal → (klDiv μ ν).toReal` when `comap gₙ` forms a filtration
generating `m𝓧`. Steps, each landed: 1 `toReal_klDiv_map_eq_integral_condExp`, 2a
`klDiv_map_eq_lintegral_ofReal_klFun_condExp`, 2b `klDiv_map_le` (ℝ≥0∞ DPI), 2c the Lévy
(`Integrable.tendsto_ae_condExp`) + Fatou (`lintegral_liminf_le`) sandwich. Wired into
`ChenGeorgiouPavon2021.energy_eq_klReal_of_projections`: the FULL `=` identity
`𝔼[∫½‖u‖²] = D(P^{u}‖R)`, both directions from this martingale convergence + limit uniqueness,
**leaving the entire Itô requirement in the single edge `hconv`** (exact-SDE grid-KL → energy).
Below is the original plan, now realised.

#### `≤`-half sub-plan — the projection-EXHAUSTION theorem (Itô-FREE, ✅ realised 2026-07-04)
The `≤` half's *structural* core — "the finite-dimensional projections capture all of the KL" — is
**not** Itô-blocked: it is the L¹ martingale-convergence identity
`KL(μ‖ν) = limₙ KL(πₙ_#μ ‖ πₙ_#ν)` when `comap πₙ ↑ m𝓧`. Combined with the `≥`-half DPI bound this
gives BOTH inequalities, i.e. it upgrades `energy_le_klReal_of_projections` from `≥` to a full `=`,
**modulo only the convergence edge `hconv`** (grid KLs → energy). It relies on Lévy's upward theorem,
which Mathlib **has** (`MeasureTheory.Integrable.tendsto_ae_condExp`). Proof skeleton (all ingredients
present):
1. **Representation** (DONE — `ForMathlib…toReal_klDiv_map_eq_integral_condExp`):
   `(klDiv (μ.map g)(ν.map g)).toReal = ∫ x, klFun ((ν[dμ/dν | comap g]) x) ∂ν` — the projected KL is
   the `klFun`-integral of the conditional expectation of the density (extracted from the DPI proof).
2. **Limit** (next): with `ℱₙ = comap πₙ`, `Mₙ = ν[dμ/dν|ℱₙ] → dμ/dν` a.e. (Lévy); `klFun ≥ 0`
   continuous, so Fatou gives `KL ≤ liminf ∫klFun(Mₙ)`, while the DPI gives each `∫klFun(Mₙ) ≤ KL`;
   the sandwich forces `∫klFun(Mₙ) → KL`, i.e. `KL(πₙ_#μ‖πₙ_#ν) → KL(μ‖ν)`.
3. **Package** (after): a projection-form corollary + the CGP `=` identity modulo `hconv`.

**What remains genuinely Itô after this:** only `hconv` itself — the statement that the *exact* SDE
finite-dimensional marginal KLs converge to the energy. For the Euler–Maruyama/Gaussian marginals
(the card's object) that is Itô-free (discrete Cameron–Martin + Riemann sums); for the *exact*
feedback-diffusion marginals it is the finite-dimensional Girsanov density, the true stochastic-
exponential content. So this sub-plan localises the entire Itô requirement to `hconv`.

#### `hconv`'s "+ Riemann sums" half — PROVED (Itô-free, Kolmogorov-free, 2026-07-04)
The `Δt → 0` analytic core is now a theorem (axiom-clean, `ForMathlib/MeasureTheory/GaussianEntropy.lean`):
- `tendsto_equispaced_riemannSum` — equispaced left-Riemann sums of a continuous `g` on `[0,1]`
  converge to `∫₀¹ g` (uniform-continuity proof; `sum_integral_adjacent_intervals` +
  `norm_integral_le_of_norm_le_const`).
- `tendsto_emEnergy_sampled` — `emEnergy (1/n) (v(·/n)) → ∫₀¹ ½ Σᵢ (vₜ i)² dt` for continuous `v`:
  the card's discrete energy is a consistent quadrature of CGP (4.20).

So the EM-model `hconv` now factors into two **proved** Itô-free pieces — grid KL = discrete energy
(`energy_identity_euler_maruyama`) and discrete energy → continuum integral (`tendsto_emEnergy_sampled`)
— plus ONE remaining gap: *grid KL of the continuum path measure = discrete energy*, i.e. the
existence + finite-dim projection of the continuum reference measure itself.

**The continuum wall is now two sharply-named, disjoint Mathlib gaps** (re-verified 2026-07-04):
1. **Kolmogorov extension for dependent projective families** → the continuum reference measure.
   The pin's `MeasureTheory.Constructions.Projective` has only the `IsProjectiveLimit` predicate +
   uniqueness; existence is present only for **product** measures (`infinitePi`) and Ionescu–Tulcea
   Markov trajectories. The Brownian projective family is built and proved consistent
   (`Probability.BrownianMotion.GaussianProjectiveFamily`, with `IsPreBrownianReal`/`IsBrownianReal`
   in `…BrownianMotion.Basic`) but its own docstring notes the extension theorem is "not in Mathlib yet".
2. **The Itô/Girsanov stack** → the feedback-drift path-measure density (route 2b above).

Neither is faked; both are multi-file Mathlib-scale ports. Everything around them — the discrete
Cameron–Martin layer, the projection-exhaustion martingale theorem, the DPI `≥`-half, and now the
Riemann-quadrature limit — is proved and axiom-clean.

**Plan A(i) — the embedding edge — DONE (2026-07-04, `ForMathlib/MeasureTheory/PathEmbedding.lean`).**
The abstract measurable-embedding edge `e : Path X ↪ (ℕ→ℝ)` of `energy_eq_klReal_via_embedding` is now
a **theorem** for the continuous-path model, not a hypothesis. `exists_measurableEmbedding_nat_of_separating`
(engine: standard-Borel + countable separating measurable family ⇒ measurable embedding into `ℕ→ℝ`
with measurable left inverse, via Lusin–Souslin `Measurable.measurableEmbedding` +
`MeasurableEmbedding.invFun`); `exists_measurableEmbedding_nat_continuousMap` (the concrete `C(T,ℝ)`
instance, `φ n = eval at denseSeq T n`); `toReal_klDiv_map_frestrictLe_tendsto_of_separating` /
`eq_toReal_klDiv_of_separating_tendsto` (absorb the edge into the KL-limit); and
`eq_toReal_klDiv_continuousMap_of_tendsto` (the continuum identity for `C(T,ℝ)` laws, embedding edge
gone, only `hconv` + regularity left). **No vendor needed** — Mathlib's `ContinuousMap` instances
already make `C(T,ℝ)` Polish; only a `BorelSpace C(T,ℝ)` is taken as a satisfiable hypothesis. All
axiom-clean. Remaining for a *fully closed* continuum identity: `hconv` (gap #2 below) and re-typing
`SBData.Path` to `C([0,1],X)` so these feed `Drsb` directly.

**Bottom line:** the continuum `hCM` is a known Girsanov identity that cannot be discharged in Lean
until the Itô-integral / stochastic-analysis stack exists in (or is ported into) Mathlib. Until
then it stays an explicit, non-vacuous edge whose discrete instance is proved — the honest state.

> **Refinement (2026-07-07 survey):** the bottom line above applies to the **feedback**-drift
> case only. The **deterministic** (open-loop) case is *not* Itô-blocked: it reduces to the
> infinite-dimensional Cameron–Martin KL identity on the iid Gaussian sequence model, and every
> ingredient except one finite-dimensional Gaussian density layer is pin-present. See
> `dev/journals/2026-07-07-continuum-energy-closure-survey.md` (feasibility grades) and
> **[`PLAN_CONTINUUM_CLOSURE.md`](PLAN_CONTINUUM_CLOSURE.md)** (the ticket-level implementation
> plan: Bricks 1.5 / 2 / 3 → Theorem A → CGP wiring).

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
