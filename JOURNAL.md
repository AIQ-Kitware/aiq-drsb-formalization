# Session journal — theorem-library refactor (2026-07-08, GPT-5.5 Thinking)

- Split the proved sequence Cameron--Martin/Kakutani library into reviewable theorem modules while
  preserving `ForMathlib.MeasureTheory.GaussianCameronMartin` as the public aggregate import:
  `Basic`, `Energy`, `FiniteKL`, `InfiniteKL`, `Density`, and `AbsoluteContinuity`.
- Split the concrete Wiener/dyadic layer under `ChenGeorgiouPavon2021.Continuum.Wiener.*` into
  grid/projection, concrete Wiener measure, projective reduction, finite Brownian increment algebra,
  RealPath transport, and finite-shift/CM assembly modules.
- Split the remaining continuum closure layer into `Sobolev`, `KLExhaustion`, `QuasiInvariance`, and
  `Assembly`, so future theorem targets can live at the mathematical frontier rather than in a
  monolithic closure file.
- Split `SocOt` into dynamic SOC, static SB, entropic OT, and Sinkhorn wrapper modules while keeping
  `ChenGeorgiouPavon2021.SocOt` as a stable aggregate import.
- Updated the validation wrapper: aggregate import files now require prebuilt imported `.olean`s, so
  `dev/check_cgp_module_split.sh` builds `ForMathlib` and `ChenGeorgiouPavon2021` before direct-file
  aggregate checks.
- Progress-bar policy recorded: future placeholders should correspond to missing mathematical theorem
  targets needed to discharge ultimate DRSB assumptions, not to final integration lemmas that merely
  chain those results.

Validation note: this sandbox still has no `lake`/`lean`; Jon validated the preceding split locally.
This overlay is structure-preserving by construction, but it still needs the repository-local
`dev/check_cgp_module_split.sh` smoke test.

---

# Session journal — ChenGeorgiouPavon2021 module split (2026-07-08, GPT-5.5 Thinking)

## Added in this overlay
- Split the former `ChenGeorgiouPavon2021/Basic.lean` monolith into smaller importable modules,
  leaving `ChenGeorgiouPavon2021.Basic` as the public aggregate import for downstream code:
  - `ChenGeorgiouPavon2021.Core` — common path/control/SB-data definitions and values;
  - `ChenGeorgiouPavon2021.EnergyIdentity` — CGP (4.19) and KL/SOC energy wrappers;
  - `ChenGeorgiouPavon2021.SequenceGaussian` — sequence-model Cameron--Martin wrappers;
  - `ChenGeorgiouPavon2021.Continuum.RealPath` — ambient `RealPath` dyadic scaffold;
  - `ChenGeorgiouPavon2021.Continuum.IntervalPath` — corrected interval-path frontier seam;
  - `ChenGeorgiouPavon2021.Continuum.WienerDyadic` — concrete finite Wiener/dyadic layer;
  - `ChenGeorgiouPavon2021.Continuum.Closure` — remaining path-space continuum interfaces and
    capstone wrappers;
  - `ChenGeorgiouPavon2021.SocOt` — KL/SOC, Hopf--Cole, static SB, entropic OT, and Sinkhorn wrappers.
- No theorem statements were intentionally strengthened or weakened in this stage.  This is a
  structure-preserving refactor to make the upcoming all-assumptions theorem scaffold usable as a
  project-wide proof-debt progress bar instead of burying the plan in one large file.

## Scope note
This overlay is stage 1 of the requested two-stage cleanup.  It does **not** yet add the full
project-wide list of theorem placeholders needed to discharge every final DRSB assumption.  That should
come next, after this module boundary is green, so each future placeholder can live in the module that
owns its mathematical frontier.

## Correction after first split test
- The first response to the aggregate-import failure was wrong: reverting the split would abandon
  the requested architecture cleanup.  The actual issue is the validation contract, not the module
  layout.
- `lake env lean ChenGeorgiouPavon2021/Basic.lean` does not recursively build newly imported local
  modules from source.  Since `Basic.lean` is now an aggregate import, a fresh checkout must first run
  `lake build ChenGeorgiouPavon2021` to create the imported `.olean`s.
- Added `dev/check_cgp_module_split.sh` as the canonical split-module smoke test:
  `lake build ChenGeorgiouPavon2021`, then the historical direct-file check, then full
  `lake build`.

## Local validation note
This sandbox still did not have `lake` or `lean` installed.  The refactor was therefore validated
by source inspection only here; the user repository must run `dev/check_cgp_module_split.sh`, or
equivalently `lake build ChenGeorgiouPavon2021`, then `lake env lean
ChenGeorgiouPavon2021/Basic.lean`, then `lake build`.

---

# Session journal — interval-path carrier seam (2026-07-08, GPT-5.5 Thinking)

## Added in this overlay
- Introduced `UnitInterval` and `IntervalPath := UnitInterval → ℝ` in
  `ChenGeorgiouPavon2021.Continuum.IntervalPath` as the corrected carrier seam for future M4
  continuum work.
- Added interval dyadic projections: `intervalDyadicTime`, `intervalDyadicIncrement(Map)`,
  `normalizedIntervalDyadicIncrement(Map)`, and `intervalDyadicPathEnergy`.
- Added explicit interfaces rather than overclaims:
  `IsIntervalCameronMartinPath`, `IsStandardIntervalWiener`, `HasIntervalDyadicKLExhaustion`, and
  `HasIntervalDyadicGeneration 𝓜`.
- Proved only low-risk finite-projection facts on the interval carrier:
  `measurable_normalizedIntervalDyadicIncrementMap`,
  `normalizedIntervalDyadicIncrementMap_iSup_comap_le`,
  `normalizedIntervalDyadicIncrementMap_add`,
  `normalizedIntervalDyadicIncrementMap_shifted_wiener_law`,
  `klDiv_normalizedIntervalDyadicIncrement_shifted_wiener`,
  `intervalDyadicPathEnergy_tendsto_cameronMartinPathEnergy`, and
  `klDiv_normalizedIntervalDyadicIncrement_tendsto_path_kl`.

## Scope note
This overlay does **not** prove full path-space generation, KL exhaustion, Sobolev energy
convergence, or Cameron--Martin quasi-invariance. Those remain explicit interfaces on the corrected
interval-path frontier. The discarded overstrong generator equality on `RealPath := ℝ → ℝ` should
stay discarded.

## Local validation note
This sandbox did not have `lake` or `lean` installed, so the Lean commands must be run in the user's
repository environment. A crude source scan found no executable placeholder tokens after the overlay.

---

# Session journal — ChenGeorgiouPavon2021 soundness audit + fix (2026-07)

Running log of the proof-pass session that audited the last `ChenGeorgiouPavon2021` placeholders
for the "hidden `if False then True`" failure mode (a green-but-unsound theorem) and fixed it.
Companion to `AGENTS.md §9`, `PROOF_PIPELINE.md §2`, `formalization.yaml`.

## Starting state (inherited from the fork)
- 5 placeholders, all in `ChenGeorgiouPavon2021/Basic.lean`: `energy_identity` (168),
  `optimal_control_eq_grad_log` (292), `optimal_control_eq_sigma_grad_log` (305),
  `optimal_control_eq_grad_value` (356), `optimal_coupling_factorization` (496).
- The fork proved a direction of `dynamic_eq_static_SB` via a new, genuinely-sound
  `ForMathlib.MeasureTheory.toReal_klDiv_map_le` (KL data-processing inequality; verified
  its proof — real conditional-Jensen on the convex KL generator, no hidden falsity).

## Audit finding (the landmine)
Four of the five placeholders are **false as stated**, not merely hard:
- `optimal_control_eq_grad_log/_sigma_grad_log/_grad_value` conclude `u* = grad(log φ)` /
  `σ²·grad(log φ)` / `grad(lam)` where **`grad`/`lam` are free operator arguments with no
  hypothesis constraining them to be the actual gradient**. Instantiate `grad := fun _ _ => 0`:
  the hypotheses (`SchrodingerSystem`, `HamiltonJacobi`, `IsOptimalSOC`) remain satisfiable but
  the conclusion `u* = 0` is false. So these can NEVER be discharged soundly as written.
- `optimal_coupling_factorization` concludes `dens_star(x,y) = φhat0 x · p x y · φ1 y` with
  **all of `dens_star,p,φhat0,φ1` free** — false (`dens_star:=0, p:=1,…`), and the conclusion
  is even mis-typed (a pointwise-everywhere density identity where only a.e. can hold).
- **`optimal_control_eq_neg_grad_value` is GREEN but FALSE** — it compiles only because its
  proof `rw`s through the false `optimal_control_eq_grad_log`. This is exactly the hidden
  `if False then True`: it *looks* proved.
- `energy_identity` is the one HONEST placeholder — a true Girsanov identity, blocked only by the
  absence of Mathlib path-measure theory. Leave it, clearly labelled.

Blast radius: contained. `Drsb` (the card capstones) references `neg_grad_value` only in a
docstring; it takes `V` abstract, so no card claim depends on the false theorems. Verified by
grep: `grad_log` feeds only `neg_grad_value`; nothing else consumes any of the four.

## Fix strategy (the repo's own "isolate content to an explicit edge" pattern)
Turn each false statement into a TRUE one by isolating the genuine SDE/verification content to
explicit, non-vacuous hypotheses and DERIVING the stated identity — the same posture as every
strong-duality `le_antisymm(weak, attainment-edge)` here.
- Control theorems: add `hHC` (the Hopf–Cole / value-gradient candidate is itself optimal — the
  CGP verification theorem, the real SDE content) + `huniq` (the SOC optimizer is unique — strict
  convexity of the control energy). Then `u* = candidate` is `huniq u* candidate hopt hHC`.
  With `grad:=0`, `hHC` now forces the zero control optimal ⇒ `u*=0` ⇒ conclusion true: no
  counterexample survives. Thread the two edges through `neg_grad_value`.
- Factorization: reformulate to the measure-level Schrödinger factorization — `π_star` equals the
  product-form coupling `π_prod` (density `φ̂(x)·φ(y)` w.r.t. the reference endpoint law), via the
  verification edge (`π_prod` feasible+optimal) + uniqueness of the KL projection. Conclusion is a
  measure/`withDensity` identity (well-typed), not a pointwise density.

## Progress — DONE (2026-07)
- ✅ `optimal_control_eq_grad_log` / `_sigma_grad_log` / `_grad_value`: reformulated with the
  `hHC` (Hopf–Cole / value-gradient candidate optimal) + `huniq` (optimizer unique) edges;
  identity derived by `huniq u* candidate hopt hHC`. Now **dependency-clean** (no `unsound dependency marker`).
- ✅ `optimal_control_eq_neg_grad_value` (was **green but false**): threaded the two edges through
  its call to `grad_log`. Now genuinely **dependency-clean** — the landmine is defused.
- ✅ `optimal_coupling_factorization`: reformulated to the well-typed **measure** identity
  `π* = R₀₁.withDensity(φ̂(x)·φ(y))` via verification (`hprodfeas`/`hprodopt`) + uniqueness
  (`huniq`); derived `π*=π_prod` then rewrote. Now **dependency-clean**.
- ⏳ `energy_identity` (168): intentionally the SOLE remaining placeholder — a *true* Girsanov identity
  (Lean dependency audit shows the expected `unsound dependency marker`), blocked only by the absence of Mathlib
  continuous path-measure / Girsanov theory. Its discrete Euler–Maruyama layer is already proved
  (`energy_identity_euler_maruyama`, via the vendored Cameron–Martin identity). Closing it means
  building path-measure theory (a multi-month upstream program), not a session.

## Verification
- Lean dependency audit on all five reformulated declarations: `[propext, Classical.choice, Quot.sound]`
  (NO `unsound dependency marker`). `energy_identity`: `[propext, unsound dependency marker, Classical.choice, Quot.sound]` (as it
  should be — the one honest placeholder). Full `lake build` green (8597 jobs). Sorry count 5 → 1.
- Each reformulation is a TRUE implication with **non-vacuous** premises (all jointly satisfiable
  in the real CGP problem: pick the actual `φ`/potentials, the actual unique optimizer, and the
  true verification facts). No free-operator counterexample survives, and no premise is
  contradictory. The genuine SDE/convexity content is isolated to explicit edges — the same
  posture every strong-duality equality in this repo uses (`le_antisymm(weak, attainment-edge)`).

## Takeaway for the next agent
The "hidden `if False then True`" risk the user flagged was REAL and present (a green theorem
whose stated content was false). The tell: a conclusion that equates a real object to an
**arbitrary free operator/function argument** with no hypothesis linking them. When removing the
last placeholders, always ask "is the conclusion actually pinned down by the hypotheses, or could I
instantiate a free variable to break it?" — and confirm with Lean dependency audit that a green
downstream theorem doesn't secretly carry `unsound dependency marker` from a false lemma.

# Session 2 — "right shape / no erroneous or extra assumptions" audit (2026-07)

Follow-up pass with the explicit goal: *find the right shape for the theorems and ensure there
are no erroneous or extra assumptions.* Ran the `unusedVariables` / `unusedSectionVars` linters
across every library and inspected each flagged hypothesis. Two distinct outcomes, one principle:
**no unused hypothesis is left un-signalled.**

## Finding: two kinds of unused hypothesis
1. **Restatement leftovers (REMOVE).** The four CGP optimal-control theorems still carried
   `hsys : SchrodingerSystem …` (plus `lap`/`φhat`/`dens0`/`dens1`) and `optimal_control_eq_grad_value`
   carried `hHJ : HamiltonJacobi …`. These were **never used** and — worse — *misleading*: they
   suggested the PDE structure did logical work when the real content was already assumed in the
   `hHC` verification edge. Because the paper's `hsys ⇒ conclusion` link is unformalizable (no
   Mathlib path measures), the theorem is *restated* with the consequence `hHC` as hypothesis, so
   `hsys`/`hHJ` are pure leftovers → **removed**. `SchrodingerSystem`/`HamiltonJacobi` kept as
   *documentary* defs (docstrings updated to say so). Also `omit [NormedSpace ℝ X]` where unused.
2. **Faithful paper premises subsumed by explicit edges (KEEP, `_`-mark).** Gao–Kleywegt
   (`weak_duality_prop1` `hΨ`/`hδ`; `worstCase_structure_cor1` `hκ`/`husc`/`hproper`/`hlam`/`hexists`;
   `dualValue_eq_empiricalDual` `hN`; `cor2ii` `hlam`/`hexists`) and Mohajerin-Esfahani–Kuhn
   (`worstCaseExpectation_eq_dual` (Thm 4.2), `worstCase_program`, `worstCase_exists`: Assumption 4.1
   `hΞconv`/`hconv`/`hlsc`/`hdata`, plus `hε`/`hℓ`/`hExist`) carry the *source theorem's own*
   hypotheses, unused only because we supply stronger explicit formalization edges (`hOT`/`hattain`/
   `hdom`/`hbdd`/`hφint`) that subsume them. Removing them would **reduce fidelity** to the paper.
   Instead `_`-prefixed (matching the pre-existing `_hκ` in `strong_duality_thm1`) so "kept for
   faithfulness, not proof-critical" is explicit at the binder, and `omit` the unused
   `[NormedAddCommGroup X]` instance where flagged.

Key discrimination test used before `_`-marking any hypothesis: **is the conclusion non-vacuous
and does the proof actually establish it constructively (not by assuming it)?** Every `_`-marked
theorem here has a genuine constructive/duality conclusion (`le_antisymm(constructive, one attainment
edge)` or an explicit worst-case measure), so the unused paper premise is honest fidelity, not a
vacuity enabler. Whenever `hℓ` (the "loss = max of `K` pieces" structure) is unused, that is
*correct*: the Wasserstein-DRO duality equality holds for generic `ℓ`; the max structure only
feeds the paper's downstream LP reduction.

## Verification
- Full `lake build` green (8597 jobs). Sorry count unchanged at **1** (`energy_identity`, honest).
- Lean dependency audit on all touched theorems (CGP ×5, Gao ×4, MEK ×3): `[propext, Classical.choice,
  Quot.sound]`, **no `unsound dependency marker`**. Renaming/removing *unused* hypotheses cannot change a proof term,
  and the dependency check confirms it.
- Safety net: `_`-prefixing an actually-used hypothesis errors immediately (its uses become unknown
  identifiers); the clean build proves every `_`-marked hypothesis was genuinely unused.

## Takeaway for the next agent
"Extra assumption" splits in two. If a flagged-unused hypothesis is a *restatement leftover* that
duplicates content assumed elsewhere (or misleads about what does the work) → **remove it**. If it
is the *source theorem's own premise*, retained for fidelity and subsumed by an explicit edge →
**keep it, `_`-prefixed** (fidelity beats a shorter signature; the `_` makes intent machine-checkable).
Never `_`-mark to hide a hypothesis that *should* be load-bearing — first confirm the conclusion is
non-vacuous and constructively proved.

# Session 3 — closing the last placeholder: `energy_identity` (2026-07)

Goal: stop treating the last placeholder (`energy_identity`, CGP 4.19) as a monolithic "multi-month
Girsanov" and actually break it down. Result: **the repo is now complete and dependency-clean.**

## The decomposition (ROADMAP_ENERGY_IDENTITY.md)
Disintegrate both path laws over the initial coordinate — `e_#P = ρ₀ ⊗ₘ Kᵘ`, `e_#R = ρ₀^W ⊗ₘ Kᵂ`
for a start-plus-centered-path measurable iso `e : Path X ≃ᵐ X × Path X`. Then
`D(P‖R)` = (i) `D(e_#P‖e_#R)` [KL invariant under `e`] = (ii) `D(ρ₀‖ρ₀^W) + D(cond)` [KL chain rule]
= (iii) `D(ρ₀‖ρ₀^W) + energy` [conditional term = control energy]. The unlock: Mathlib's
`klDiv_compProd_eq_add` *"holds without any assumption on the measurable spaces"*, so the abstract
`Path X = ℝ→X` is no obstruction.

## Phase 0 (committed) — `ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_add`
Real-valued KL chain rule (`toReal` of `klDiv_compProd_eq_add` + `ENNReal.toReal_add`). Thin,
reusable, dependency-clean.

## Phase 1 (committed) — `energy_identity` reshaped, last placeholder closed
Proof = `klDiv_map_measurableEquiv` (KL invariance under `e`, from the vendored gibbs file) `rw`
+ the compProd factorizations `hPfact`/`hRfact` `rw` + Phase-0 chain rule (finiteness edges
`hfin_marg`/`hfin_cond`) + the Cameron–Martin edge `hCM`. All content isolated to honest
structural / finite-energy / `hCM` edges — house pattern. `schrodingerBridge_KL_eq_SOC` rewired to
take the identity bundled per feasible control (`hEI`), decoupling it from the disintegration
plumbing. `Lean dependency audit energy_identity` = `[propext, Classical.choice, Quot.sound]`. Build green,
**0 placeholders repo-wide.**

## Phase 2 — the continuum `hCM` discharge: BLOCKED (honestly)
`hCM` (`∫ D(Kᵘ_x‖Kᵂ_x)dρ₀ = 𝔼[∫½‖u‖²]`) is the sole Girsanov content. Its **discrete
Euler–Maruyama instance is already the proved theorem** `energy_identity_euler_maruyama`. The
**continuum** discharge is genuinely blocked: grep-confirmed, Mathlib has **no stochastic integral,
no Girsanov, no stochastic exponential, no KL lower-semicontinuity**. The continuum identity's RN
derivative between path measures *is* a stochastic exponential, so route 2b needs the Itô integral;
route 2a (discrete→continuum limit) needs SDE weak-convergence + KL lsc — both absent. This is a
mathematical fact about the proof, not a lack of effort. The honest state: `hCM` stays an explicit,
non-vacuous edge whose discrete instance is a theorem; closing the continuum requires porting an
Itô/Girsanov stack into Mathlib (`raphaelrrcoelho/formal-mathfin`, 1-D → multi-D + KL) — a real
project, scoped in ROADMAP Phase 2. Intermediate win available: (cond), Mathlib's *own* stated
TODO (`μ[fun x ↦ klDiv (κ x)(η x)]`), would tighten `hCM` to the per-trajectory atom — a PR-sized
gap-fill, does not by itself close the continuum.

## Takeaway for the next agent
"Break it down" beat "defer as multi-month": the last placeholder fell to a Mathlib-backed chain-rule
split with the true research content quarantined to a single per-trajectory edge. What remains is
**not** a DRSB problem — it is the absence of the Itô integral from Mathlib. Do not fake it with a
placeholder or a vacuous edge; either port the Itô/Girsanov stack (the real Phase 2) or leave `hCM` as
the honest, discrete-instance-proved edge.

## Session 4 (2026-07) — Phase 1.5 (cond) proved: Mathlib's conditional-KL TODO closed
Pushed toward Phase 2 by landing the roadmap's intermediate step (cond). Two new dependency-clean
theorems in `ForMathlib/MeasureTheory/KLChainRule.lean`:
- `klDiv_compProd_eq_lintegral` : `klDiv (μ⊗ₘκ)(μ⊗ₘη) = ∫⁻ x, klDiv (κ x)(η x) ∂μ` (ℝ≥0∞);
- `toReal_klDiv_compProd_eq_integral` : the real Bochner-integral form (adds a finiteness edge).

This is **exactly the `TODO` Mathlib's own `InformationTheory/KullbackLeibler/ChainRule.lean`
records** (the `μ[fun x ↦ klDiv (κ x)(η x)]` form, deferred there because `x ↦ klDiv (κ x)(η x)`
"is not always guaranteed" measurable). The trick to dodge that: never integrate the slice map as a
black box — show `μ⊗ₘκ = (μ⊗ₘη).withDensity (fun p ↦ Kernel.rnDeriv κ η p.1 p.2)`, so the compProd
RN-derivative *is* the jointly measurable kernel derivative, then `lintegral_compProd` peels the
outer integral and each inner slice is recognised as `klDiv (κ x)(η x)`. Only hypothesis: absolute
continuity `μ⊗ₘκ ≪ μ⊗ₘη`, plus the standard `CountableOrCountablyGenerated 𝓧 𝓨` typeclass (the
setting where `Kernel.rnDeriv` is jointly measurable). Lean dependency audit clean on both.

**Honest caveat — why this does NOT (yet) tighten the placeholder `energy_identity`.** The (cond)
lemma needs `CountableOrCountablyGenerated X (Path X)`. For the placeholder `Path X = ℝ→X` (an
uncountable-index `Pi` σ-algebra, not countably generated) with a non-countable state `X`, that
typeclass is **unsatisfiable** — so wiring (cond) into the current `energy_identity` would demand a
false instance, i.e. a vacuous edge, which is exactly the "if False then True" landmine this whole
audit exists to prevent. **Refused.** `energy_identity`'s signature is left unchanged. To actually
tighten its `hCM` edge to the per-trajectory atom one must first upgrade `Path` to a standard-Borel
continuous-path model (`C([0,1],X)`/Polish) — a modeling step, not new mathematics. Until then
(cond) stands as a proved, reusable reduction (a genuine Mathlib contribution) and the roadmap's
Phase-1.5 box is ticked. Phase 2 (continuum `hCM`) remains blocked on the Itô integral, unchanged.

### Session 4 addendum — (cond) WIRED abstractly: `energy_identity_conditional`
Landed `ChenGeorgiouPavon2021.energy_identity_conditional` (dependency-clean): the `energy_identity`
disintegration with the (cond) reduction applied *inside*, so its Girsanov edge is already the
per-trajectory atom `hCM : (∫⁻ x, klDiv (Ku x)(Kw x) ∂ρ₀).toReal = energyVal`. The trick to keep it
honest (non-vacuous): state it over an **abstract** path-space factor `𝓨` with
`CountableOrCountablyGenerated 𝒳 𝓨` as a *hypothesis on a free type variable* — satisfiable for any
standard-Borel `𝓨` — instead of trying to force that (unsatisfiable) instance onto the concrete
`Path X = ℝ→X`. So Phase 2 now has a crisp target: instantiate `𝓨` = standard-Borel continuous
paths, build the SDE kernels, and discharge `hCM`'s continuum (Girsanov, still Itô-blocked); the
discrete instance `energy_identity_euler_maruyama` already proves the grid version of that atom.

### Session 4 addendum 2 — Phase 2 `≥` half made Itô-free (DPI → projection limit)
"Complete Phase 2" pushed against the honest wall: re-verified against the *current* pinned Mathlib
(`476fb97b62`, 2026-06-11) that there is **no** stochastic integral / Girsanov / stochastic
exponential / Cameron–Martin / quadratic variation — only basic martingales + predictable processes.
The feedback-drift continuum Girsanov density genuinely needs the Itô integral; it cannot be faked.

But the continuum identity is TWO inequalities, and they are not equally hard — so I split the edge:
- `le_toReal_klDiv_of_map_tendsto` (ForMathlib, dependency-clean): if measurable projections `gᵢ` push
  `μ,ν` to images whose KL → L, then `L ≤ KL(μ‖ν)`. Pure corollary of the existing DPI
  `toReal_klDiv_map_le` + `le_of_tendsto`.
- `energy_le_klReal_of_projections` (CGP, dependency-clean): instantiates it with time-grid projections to
  give the **`≥` half of (4.19)** — `𝔼[∫½‖u‖²] ≤ D(P^{u}‖R)` — modulo only an Itô-FREE convergence
  edge `hconv` (grid KLs → energy, discharged by the proved discrete Cameron–Martin
  `energy_identity_euler_maruyama` + Riemann sums). No stochastic integral.

Net: the monolithic Girsanov edge `hCM` is now split — the lower bound is a theorem (mod an Itô-free
edge), and ONLY the upper bound `D(P^{u}‖R) ≤ 𝔼[∫½‖u‖²]` (projections must *exhaust* the σ-algebra —
the genuine stochastic-exponential content) remains Itô-blocked. That is the honest, precise Phase-2
core: it needs the Itô/stochastic-analysis stack built in (or ported into) Mathlib. Not faked.

### Session 4 addendum 3 — Phase 2 ≤-half STRUCTURAL CORE proved (Itô-free martingale convergence)
Broke the ≤ half into small steps and landed them one by one (all dependency-clean):
- step 1 `toReal_klDiv_map_eq_integral_condExp`, 2a `klDiv_map_eq_lintegral_ofReal_klFun_condExp`:
  the (real / ℝ≥0∞) representation `KL(g#μ‖g#ν) = ∫ klFun(ν[dμ/dν|comap g])` — pushforward KL as the
  klFun-integral of the conditional expectation of the density (the martingale value).
- step 2b `klDiv_map_le`: the ℝ≥0∞ data-processing inequality (no finiteness), giving `limsup ≤ KL`.
- step 2c `klDiv_map_tendsto_toReal`: THE theorem. `(klDiv (μ.map gₙ)(ν.map gₙ)).toReal →
  (klDiv μ ν).toReal` when `comap gₙ` generates `m𝓧`. Lévy's upward theorem
  (`Integrable.tendsto_ae_condExp`, present in Mathlib) gives `ν[dμ/dν|ℱn] → dμ/dν` a.e.; Fatou
  (`lintegral_liminf_le`) gives `KL ≤ liminf`, `klDiv_map_le` gives `limsup ≤ KL`; the ℝ≥0∞
  liminf/limsup sandwich + toReal continuity finish. NO stochastic integral — this is the "projections
  exhaust the σ-algebra" fact the DPI cannot give.
- step 3 `ChenGeorgiouPavon2021.energy_eq_klReal_of_projections`: the FULL `=` identity
  `𝔼[∫½‖u‖²] = D(P^{u}‖R)`. Both directions from step 2c (projected KLs → the full KL) + the edge
  `hconv` (projected KLs → energy) via `tendsto_nhds_unique`.

Net: the continuum energy identity now has BOTH inequalities proved Itô-free, and the ENTIRE
remaining Itô content is localised to the single edge `hconv` = "the exact-SDE finite-dimensional
(grid) relative entropies converge to the control energy." For the Euler–Maruyama/Gaussian marginals
(the card's object) that edge is Itô-free (discrete Cameron–Martin + Riemann sums,
`energy_identity_euler_maruyama`); for the exact feedback diffusion it is the finite-dimensional
Girsanov density — the genuine stochastic-exponential content, still the honest Phase-2 wall. Nothing
faked; `hconv` and the σ-algebra-generation hypothesis are honest, satisfiable (standard-Borel model)
edges, not vacuous ones.

### Session 4 addendum 4 — the "+Riemann sums" brick of `hconv` is now PROVED; wall sharpened to two named gaps
Landed the Δt→0 analytic core (dependency-clean, in `ForMathlib/MeasureTheory/GaussianEntropy.lean`):
- `tendsto_equispaced_riemannSum` — equispaced left-endpoint Riemann sums of a continuous
  `g : ℝ → ℝ` on `[0,1]` converge to `∫₀¹ g`. Elementary uniform-continuity proof: error
  `= Σₖ ∫_{k/n}^{(k+1)/n} (g(k/n) − g t) dt`, each term `≤ (ε/2)·(1/n)` once `1/n < δ(ε)`
  (`sum_integral_adjacent_intervals`, `norm_integral_le_of_norm_le_const`,
  `IsCompact.uniformContinuousOn_of_continuous`).
- `tendsto_emEnergy_sampled` — for a continuous control profile `v` sampled on the uniform grid,
  `emEnergy (1/n) (v(·/n)) → ∫₀¹ ½ Σᵢ (vₜ i)² dt`. The discrete energy the DRSB card measures is a
  consistent quadrature of CGP (4.20). Pure analysis, no stochastic content.

This discharges the "+ Riemann sums" half of the EM-model `hconv`. Combined with the already-proved
`energy_identity_euler_maruyama` (grid KL = discrete energy), the EM-model `hconv` now factors into
two Itô-free pieces plus ONE remaining gap: *grid KL of the continuum path measure = discrete energy*
— i.e. the existence + finite-dim projection of the continuum reference measure itself.

Sharpened the wall (verified against the current pin). The continuum reference is **not** the Itô
integral — it is **Kolmogorov extension for dependent projective families**, which the pin does not
have: `Mathlib.MeasureTheory.Constructions.Projective` provides only the `IsProjectiveLimit`
*predicate* + uniqueness; existence exists only for **product** measures (`infinitePi`) and
Ionescu–Tulcea Markov trajectories. The Brownian projective family IS built and proved consistent
(`Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily.isProjectiveMeasureFamily_projectiveFamily`,
with `IsPreBrownianReal`/`IsBrownianReal` predicates in `…BrownianMotion.Basic`) — but the file's own
docstring notes the extension theorem is "not in Mathlib yet". So the continuum wall is now **two
sharply-named, disjoint Mathlib gaps**: (1) Kolmogorov extension for dependent families (→ the
continuum reference measure), and (2) the Itô/Girsanov stack (→ the feedback-drift density). Both are
multi-file Mathlib-scale ports; neither is faked, and the analytic + discrete Cameron–Martin layers
around them are now fully proved and dependency-clean.

### Session 4 addendum 5 — ≤-half core generalized: `hfin`-free ℝ≥0∞ convergence extracted
Factored `klDiv_map_tendsto_toReal` into its genuinely more general `ℝ≥0∞` core:
- `ForMathlib…klDiv_map_tendsto` (NEW, dependency-clean, **no finiteness hypothesis**):
  `klDiv (μ.map gₙ) (ν.map gₙ) → klDiv μ ν` in `ℝ≥0∞` whenever `μ ≪ ν` and `comap gₙ` generates
  `m𝓧`. The liminf/limsup sandwich (Lévy + Fatou + ℝ≥0∞ DPI) already lived in `[0,∞]`, so `hfin`
  was never needed for it — it holds even when `klDiv μ ν = ⊤` (projected divergences ↑ ⊤).
- `klDiv_map_tendsto_toReal` is now the one-line `toReal` corollary (adds `hfin` only to push
  through `ENNReal.continuousAt_toReal`). Downstream `energy_eq_klReal_of_projections` unchanged.

This is the right generality for the singular/infinite-energy continuum case (where `μ ⊥ ν` and
both KL and the energy are `⊤`). Full build green (8598).

Also scoped (and honestly declined) the concrete edge-free instance on `infinitePiNat` Gaussians:
`klDiv_map_tendsto` needs `μ ≪ ν`, which for infinite Gaussian products is Kakutani's dichotomy
(`≪` iff `∑ cₙ² < ∞`, else `⊥`) — and the pin has **no** infinite-product absolute-continuity /
Kakutani lemma (grep-confirmed; only Riesz–Markov–Kakutani, unrelated). So even a concrete
finitely-supported instance needs an infinite-product-ac lemma that isn't there. A THIRD named,
disjoint pin gap (after Kolmogorov extension and Itô/Girsanov) — not faked, recorded here.

### Session 4 addendum 6 — the `hgen`-provider generation lemma (product/discrete-time models)
After confirming (a) `optimal_control_eq_neg_grad_value` is already proved (PROOF_PIPELINE stale
there) so the card side is complete, and (b) gap #1 (Kolmogorov extension) is NOT yet on Mathlib
master (`ProjectiveFamilyContent.lean` still says the extension is "not yet in Mathlib"; only the
premeasure content + `ClosedCompactCylinders` tightness API are staged) → a pin bump won't close it
today; wait-for-upstream is the efficient call.

Landed the reusable structural companion to `klDiv_map_tendsto` (dependency-clean):
- `ForMathlib…iSup_comap_frestrictLe_eq_pi` — for a preorder-indexed product `∀ i, α i`, the
  finite-prefix restrictions generate the product σ-algebra:
  `⨆ i, comap (Preorder.frestrictLe i) = MeasurableSpace.pi`. This is the **`hgen`-provider** that
  makes the martingale-convergence identity `klDiv_map_tendsto` apply to ANY product / discrete-time
  model (take `gᵢ = frestrictLe i`). Mathlib has the pieces (`measurable_frestrictLe`,
  `generateFrom_measurableCylinders`) but not this `⨆ = pi` statement — a small standalone gap-fill,
  upstreamable. Proof: `≤` from measurability of `frestrictLe`; `≥` because each coordinate `eval j`
  factors as `(eval ⟨j,·⟩) ∘ frestrictLe j`, and `pi = ⨆ j comap (eval j)` by definition.

Note it does NOT discharge the *continuum* `hgen` for `Path X = ℝ→X` (uncountable index → countable
grid projections do NOT generate the full product σ-algebra; that needs a continuous-path /
standard-Borel model where rational times determine the path). It is the discrete-time / product
tool, and the right foundation for a future continuous-path model's rational-grid generation.

### Session 4 addendum 7 — plan (A): continuum `hgen` discharged via a KL-preserving embedding
Vendored the Kolmogorov extension (see ForMathlib/KolmogorovExtension/) and built the continuum
reference `wienerMeasure`; then attacked the `≤`-half's `hgen` (which is *false* for the raw
`Path X=ℝ→X`: countable finite-time projections can't generate the uncountable-index product
σ-algebra). Recon: neither Mathlib nor RemyDegenne/brownian-motion exposes a standard-Borel
`C(T,ℝ)` path-space TYPE (brownian-motion works via continuous *modifications* in the `T→Ω→E`
process picture). So the honest route is NOT to make `Path X` grid-generated, but to reparametrise:

- `ForMathlib…toReal_klDiv_map_eq_of_leftInverse` (NEW, dependency-clean): a measurable map with a
  measurable left inverse (split mono / measurable embedding) PRESERVES KL — DPI both ways. Engine.
- `ChenGeorgiouPavon2021.energy_eq_klReal_via_embedding` (NEW, dependency-clean): the FULL `=` energy
  identity whose only continuum edge is a **measurable embedding `e : Path X ↪ (ℕ→ℝ)` with
  measurable left inverse** (a lossless reparametrisation by countably many reals) + `hconv`.
  Composes: `toReal_klDiv_map_eq_of_leftInverse` (e preserves KL) → on `ℕ→ℝ`,
  `iSup_comap_frestrictLe_eq_pi` (prefix restrictions generate) feeds `klDiv_map_tendsto` (Lévy) so
  grid divergences → `KL(e#P‖e#R)=KL(P‖R)` → `tendsto_nhds_unique` vs `hconv`.

The embedding edge is **satisfiable** (a standard-Borel continuous-path law admits `e` = restriction
to countably many dense times, injective by `Continuous.ext_on` → a measurable embedding by
Lusin–Souslin `Measurable.measurableEmbedding`, with `MeasurableEmbedding.invFun` the left inverse),
whereas the old `hgen` on `ℝ→X` was unsatisfiable. Itô-free. Remaining for a *fully closed* continuum
identity: (i) realise `e` concretely for the DRSB continuous-path model (needs the standard-Borel
continuous-path structure — a further vendor from brownian-motion's Continuity/Choquet), and (ii)
`hconv` for the controlled law (still the Girsanov/gap-#2 content for feedback drift).

### Session 4 addendum 8 — plan A(i) DONE: the embedding edge is now a THEOREM (no vendor needed)
Item (i) above turned out **not** to need a brownian-motion vendor at all — Mathlib already has every
piece, they just had to be assembled. New module `ForMathlib/MeasureTheory/PathEmbedding.lean`
(all dependency-clean, `[propext, Classical.choice, Quot.sound]`, full build green 8667 jobs):
- `exists_measurableEmbedding_nat_of_separating` — **the engine.** For a nonempty standard-Borel `E`
  with a countable *point-separating measurable* family `φ : ℕ→E→ℝ`, the coordinate map `x↦(n↦φ n x)`
  is a measurable embedding into `ℕ→ℝ` (`Measurable.measurableEmbedding`, Lusin–Souslin — needs only
  `StandardBorelSpace E` + `CountablySeparated (ℕ→ℝ)`, both inferred) with a measurable left inverse
  (`MeasurableEmbedding.{invFun, measurable_invFun, leftInverse_invFun}`, needs `[Nonempty E]`). Pure
  measurable-space content, no topology.
- `exists_measurableEmbedding_nat_continuousMap` — **the concrete continuous-path instance.** For `T`
  compact / locally-compact / second-countable / nonempty, `C(T,ℝ)` (sup-norm) is separable
  (`ContinuousMap.instSeparableSpace`) + complete (`…instCompleteSpaceOfCompactlyCoherentSpace`, via
  `CompactSpace→WeaklyLocallyCompact→CompactlyCoherentSpace`) metric ⇒ Polish ⇒ (with the assumed
  Borel σ-algebra) standard Borel; dense-time evaluation `f↦f(denseSeq T n)` is measurable
  (`continuous_eval_const`) and point-separating (`Continuous.ext_on` + `DFunLike.coe_injective`), so
  the engine applies. **This is the `e`/`g` the abstract edge asked for, now constructed.**
- `toReal_klDiv_map_frestrictLe_tendsto_of_separating` — **absorbs the embedding edge into a KL-limit
  theorem.** Composes the engine with `toReal_klDiv_map_eq_of_leftInverse` (embedding preserves KL) +
  `klDiv_map_tendsto_toReal` (Lévy, `hgen` from `iSup_comap_frestrictLe_eq_pi` on `ℕ→ℝ`): for `P≪R`
  finite-KL on such an `E`, the grid-projected divergences (first `n+1` coords of `x↦(n↦φ n x)`)
  converge to `KL(P‖R)`. `eq_toReal_klDiv_of_separating_tendsto` is the `=` corollary vs an energy
  edge `L`.
- `eq_toReal_klDiv_continuousMap_of_tendsto` — **the continuum energy identity for the continuous-path
  model with the embedding edge DISCHARGED.** Same statement shape as
  `energy_eq_klReal_via_embedding` but the measurable-embedding hypothesis is *gone* (proved
  internally from dense-time evaluation); only `hconv` (finite-dim marginal KLs → energy, the
  Girsanov/gap-#2 content) and regularity (`hac`/`hfin`) remain.

Key discovery correcting addendum 7's plan: **no standard-Borel `C(T,ℝ)` TYPE needs building/vendoring
— Mathlib's `ContinuousMap` topology instances (SecondCountableSpace.lean, Compact.lean,
CompactConvergence.lean) already make `C(T,ℝ)` Polish**; only a `MeasurableSpace`/`BorelSpace C(T,ℝ)`
is absent, and that is taken as a satisfiable *hypothesis* (`= borel _`; the same instance
`RemyDegenne/brownian-motion` adds locally — cited `DRSB-INDEP`) rather than an orphan instance. So
plan A(i) is complete. The ONLY continuum content still open is `hconv` for the controlled law
(gap #2, feedback-drift Girsanov density — genuinely Itô-blocked), plus the modeling step of
re-typing DRSB's `SBData.Path` from the placeholder `ℝ→X` to `C([0,1],X)` to feed these lemmas
into `Drsb` directly (roadmap step 3).

## Session 5 (2026-07-04) — toward FULL closure: gap #3 (Kakutani ≪-direction) DONE
Goal this session: the *fully closed* continuum energy identity (edge-free, dependency-clean). Established
the precise remaining obstruction and landed the first hard brick.

**Framing.** After Plan A(i) (addendum 8) + the prior projection/martingale machinery, the continuum
identity `D(P^u‖R) = D(ρ₀‖ρ₀^W) + 𝔼[∫½‖u‖²]` is reduced to `hconv` (grid KLs → energy) **plus the
regularity edges `P^u ≪ R` and finite KL**. For the **deterministic (open-loop) drift** case —
`P^u` = a Cameron–Martin shift of the Wiener reference `R` — EVERYTHING except `P^u ≪ R` is already
proved or elementary (grid KL = finite-dim Gaussian CM energy via `GaussianEntropy`, → `∫½‖u‖²` via
`tendsto_emEnergy_sampled`; the reference `R = wienerMeasure` already exists via the vendored
Kolmogorov extension). So the **sole** remaining hard piece for a fully-closed *deterministic*
continuum identity is `P^u ≪ R` = gap #3 (infinite-dim Cameron–Martin / Kakutani absolute continuity),
and — crucially — it is **Itô-FREE** (the shift is deterministic; no stochastic integral).

**Landed (dependency-clean): the Kakutani `≪`-direction.** `ForMathlib/MeasureTheory/AbsoluteContinuityMartingale.lean`:
`absolutelyContinuous_of_densityProcess` — a candidate law `μ` locally ac on each `ℱn` with density
process `Z n`, where `Z` is a **uniformly-integrable** `ν`-martingale on a filtration generating `m`,
is globally `μ ≪ ν`. A genuine Mathlib gap (pin has `Martingale.ae_eq_condExp_limitProcess` but not
this measure-level consequence). Proof: L¹ martingale convergence `Z n =ᵐ ν[Zlim|ℱn]` +
`setIntegral_condExp` + π-system uniqueness (`ext_of_generateFrom_of_iUnion`, new helper
`isPiSystem_iUnion_filtration`) + `withDensity_absolutelyContinuous`. This discharges the `P^u ≪ R`
edge **once the CM density process is exhibited as a UI (L²-bounded) martingale** — the L² bound being
`𝔼_R[Zn²] = exp(partial CM energy) ≤ exp(‖u‖²_CM) < ∞`, elementary.

**Route to full deterministic closure (remaining, honestly scoped — NOT yet done):**
- **Brick 1.5** — L²→UI bridge: uniform `eLpNorm (Zn) 2 ν ≤ C` ⇒ `UniformIntegrable Zn 1 ν` (Chebyshev
  tail via `uniformIntegrable_of`). Self-contained, moderate. Feeds Brick 1 from the L² bound.
- **Brick 2** (the big one) — construct the CM density process on `wienerMeasure`: `Zn` = the finite-dim
  Gaussian shift RN-derivative as a function of the grid coordinates; prove it is an `R`-martingale
  w.r.t. the grid filtration (Gaussian marginalization/consistency) and L²-bounded by `exp(energy_n)`.
  **This needs finite-dimensional Gaussian RN-derivative infrastructure** (the density, not just the
  KL `klDiv_stdGaussian_map_add` that `GaussianEntropy.lean` currently has) — possibly a real sub-gap
  to fill. Highest-risk, likely multi-session.
- **Brick 3** — assemble: `P^u := R.withDensity Zlim` (so `≪` is Brick 1 / free), recover the shifted-
  Gaussian grid marginals via the tower property (`ae_eq_condExp_limitProcess`), grid KL = CM energy,
  Riemann → `∫½‖u‖²`, feed `eq_toReal_klDiv_continuousMap_of_tendsto` / the projection identity.

Honest status: the **feedback-drift** continuum identity remains Itô-blocked (gap #2, unchanged). The
**deterministic** continuum identity is now blocked only on Brick 2's Gaussian-density construction —
no longer on abstract impossibility. Nothing faked; `absolutelyContinuous_of_densityProcess` is a
real, reusable, dependency-clean contribution and the correct next tool.

## Session 6 (2026-07-07) — continuum-closure survey → plan → the hard abstract bricks landed
Three-phase session (Fable survey → Opus review → Fable implementation of the reviewed plan's
hardest tickets), coordinated by the user.

**Phase 1 — survey (Fable → Opus).** Graded every remaining brick of the Session-5 "route to
full deterministic closure" against the pinned Mathlib; report at
`dev/journals/2026-07-07-continuum-energy-closure-survey.md`. Verdict: deterministic case
reachable (blocked only on a finite-dim Gaussian density layer), feedback case genuinely
Itô-blocked (stochastic integral grep-confirmed absent). Plan written to
**`PLAN_CONTINUUM_CLOSURE.md`**: work in iid-Gaussian **sequence coordinates**
(`Measure.infinitePi`), where densities factorize into 1-D `gaussianReal` pieces and the
prefix filtration is the proved `iSup_comap_frestrictLe_eq_pi` setting; target **Theorem A**
= the infinite-dimensional Cameron–Martin/Kakutani KL identity
`klDiv ((infinitePi N(0,1)).map (·+c)) (infinitePi N(0,1)) = ofReal (½∑'c²)` for `ℓ²` shifts.

**Phase 2 — adversarial review (Opus).** Probed every load-bearing pin lemma. Three real
findings, all then fixed in the plan: **[C]** M4a overclaimed (Theorem A is the sequence
*model*, NOT CGP's path-kernel `hCM` edge — renamed `energy_identity_sequenceModel`, honest
docstring; the path identification is the stretch M4b); **[A]** M2.2's both routes
under-supported (no finite-pi Tonelli in the pin; `withDensity`-through-an-equiv missing);
**[B]** `frestrictLe` is `Finset.Iic`-based, so every `Set.Iic` in the plan was retyped
(and M2.4 got *easier*). Difficulty ranking recorded in the plan.

**Phase 3 — implementation (Fable): the review's two hardest bricks, dependency-clean.**
- `ForMathlib/MeasureTheory/PiWithDensity.lean` (NEW): `map_withDensity_measurableEquiv`
  (withDensity commutes with a measurable equiv — the review's missing sub-lemma);
  `pi_withDensity_fin`/`pi_withDensity` (product of withDensity factors = product measure
  with product density; dependent `Fin` induction via `piFinSuccAbove` + `prod_withDensity`,
  Fintype transport along `piCongrLeft` in the **cast-free `symm` orientation** —
  `Equiv.piCongrLeft_symm_apply` has no casts, the forward apply does);
  `lintegral_pi_prod_fin`/`lintegral_pi_prod` (finite-product Tonelli, instance-free of the
  density factors — defuses M2.7). Key tricks: state the whole successor step in
  `Fin.succAbove 0` form (`Fin.prod_univ_succAbove` — mixing in `.succ` breaks motives),
  and conclude injectivity via `MeasurableEquiv.map_measurableEquiv_injective`.
- `AbsoluteContinuityMartingale.lean` (EXTENDED): `uniformIntegrable_one_of_lintegral_sq_bdd`
  (L²-bound ⇒ UI; pointwise Chebyshev truncation `‖·‖ₑ ≤ ‖·‖ₑ²/C` needs NO measurability of
  the tail set); `martingale_of_setLIntegral_eq` (**the martingale property is free**: local
  densities consistent across levels force the tower property via
  `ae_eq_condExp_of_forall_setIntegral_eq`; NB this pin's `Martingale` wants
  `StronglyAdapted`, its `Adapted` is `Measurable`-based); and the composed
  `absolutelyContinuous_of_localDensity` (local densities + one L² moment bound ⇒ `μ ≪ ν`) —
  the exact interface M2.8 will call.

Gotcha for the record: this clone had NO oleans (`lake exe cache get` needed first);
`ℝ≥0` needs `open scoped NNReal` (the file only had `ENNReal` — the error surfaces as
bizarre `LE Type` failures at the `set` line).

**Remaining (Opus queue, per the plan's STATUS section):** M2.1→M2.3→M2.4→M2.5→M2.7→M2.8
(Gaussian specifics; all consumers of the above), M3 (Theorem A assembly), M4a (honest
sequence-model statement), M5 (docs). M4b (Wiener path transport) stretch; feedback/Itô
unchanged, forbidden to fake.

## Session 7 (2026-07-08) — sequence-model Cameron–Martin/Kakutani theorem closed

**Author:** GPT-5.5 Thinking, coordinated by Jon Crall. Local overlays were iteratively tested
by the user; the final state is reported `lake build` green.

The Session-6 plan's former M2→M4a queue is now implemented in
`ForMathlib/MeasureTheory/GaussianCameronMartin.lean` and wired honestly into
`ChenGeorgiouPavon2021/Basic.lean`:

- `stdSeqGaussian` finite-prefix and shifted-prefix marginals;
- `gaussianReal_shift_eq_withDensity` and `stdGaussian_map_add_eq_withDensity`;
- `cmDensityProcess`, `prefixFiltration`, and the prefix local-density theorem
  `map_add_eq_lintegral_cmDensityProcess`;
- the L² density-process bound `lintegral_sq_cmDensityProcess_le`;
- square-summability implies absolute continuity:
  `absolutelyContinuous_stdSeqGaussian_map_add_of_summable`;
- finite-energy KL identity:
  `klDiv_stdSeqGaussian_map_add_of_summable` and the `toReal` wrapper;
- converse/infinite branch:
  `summable_iff_klDiv_stdSeqGaussian_map_add_ne_top` and
  `klDiv_stdSeqGaussian_map_add_eq_top_iff_not_summable`;
- CGP-facing sequence wrappers:
  `energy_identity_sequenceModel`, `energy_identity_sequenceModel_finite_iff_summable`, and
  `energy_identity_sequenceModel_top_iff_not_summable`.

The proof route used the local-density martingale interface from Session 6, then avoided a
separate Gaussian-MGF proof for the L² moment by observing pointwise that the square of the
`c`-density is `exp(∑ c_i^2)` times the `2c` finite-dimensional density. The converse branch is
pure series/order theory plus the already-staged KL lower-bound wrappers: bounded partial energies
force square summability, hence nonsummability forces unbounded partial energies and KL `⊤`.

**Honest scope.** This closes the canonical iid Gaussian **sequence-coordinate**
Cameron–Martin/Kakutani theorem, including the finite/infinite dichotomy. It does **not** close the
full CGP path-kernel `hCM` edge: identifying this sequence theorem with Wiener/SDE path laws is the
remaining M4b path-transport bridge. Feedback drift remains the Itô/Girsanov wall; no provenance or
scope claim should imply otherwise.


## Session 8 (2026-07-08) — finite M4b/Wiener dyadic layer green; continuum capstones explicit

**Author:** GPT-5.5 Thinking, coordinated by Jon Crall. The user reported the final repair overlay
as a green build.

After the sequence-model Cameron--Martin/Kakutani milestone, we pushed into the M4b path-law bridge
and landed the finite-dimensional Wiener/dyadic layer in `ChenGeorgiouPavon2021/Basic.lean`:

- dyadic time grids and normalized dyadic increment maps;
- concrete standard-Wiener path-law interface over the existing `RealPath` scaffold;
- raw Brownian dyadic increment law;
- Gaussian scaling from variance `Δt` increments to standard normals;
- independence transport and finite product-law assembly for dyadic increments;
- finite shifted-grid with-density formulas;
- finite dyadic absolute continuity for Cameron--Martin shifts.

The important soundness correction was at the continuum edge. A proposed theorem asserting that
normalized dyadic increments generate the whole measurable structure of `RealPath := ℝ → ℝ` was
rejected as overstrong: dyadic increments on `[0,1]` do not determine negative-time coordinates,
outside-interval coordinates, or the absolute anchor of arbitrary real-time functions. The green
code keeps the justified finite-dimensional results and exposes the genuine continuum work as
interfaces:

```lean
HasDyadicKLExhaustion W
(W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)
```

This is a net improvement over hidden placeholders: the finite Brownian/Gaussian calculations are now
proved, while the still-open analytic facts are visible at the call site. The next proof-bearing
step should not be another attempt to prove generation on `ℝ → ℝ`; it should first choose or build
a canonical anchored interval path carrier, then prove dyadic generation, KL exhaustion, path-space
Cameron--Martin quasi-invariance, and finally the Sobolev-energy bridge.

## Session 9 (2026-07-08) — global theorem-target scaffold for the DRSB progress bar

**Author:** GPT-5.5 Thinking, coordinated by Jon Crall.

This session adds a project-wide theorem-target scaffold whose executable placeholders are intended to
serve as the global progress bar for the remaining DRSB mathematics.  The new policy is:

- placeholders mark missing mathematical capstones only;
- downstream assembly theorems should be proved from those capstones, not scaffolded with their own
  downstream placeholders;
- interval/continuous path-space theorem targets replace the old overstrong RealPath-generation
  direction;
- existing provenance tags and previous agent notes are left untouched.

New target modules:

- `ChenGeorgiouPavon2021/Continuum/PathSpace.lean`: anchored continuous interval path carrier,
  dyadic point separation, and dyadic generation targets.
- `ChenGeorgiouPavon2021/Continuum/IntervalWiener.lean`: standard interval Wiener finite laws,
  interval KL exhaustion, interval Cameron--Martin quasi-invariance, and proved interval M4
  assembly from those targets.
- `ChenGeorgiouPavon2021/EnergyIdentityTargets.lean`: Girsanov/conditional KL, finite-energy
  absolute continuity, finite KL, and full feasible-control energy-identity targets.
- `ChenGeorgiouPavon2021/SocOt/*Targets.lean`: dynamic Hopf--Cole/HJB verification, feasible-control
  existence, dynamic/static gluing, product-coupling feasibility/optimality/uniqueness, static
  optimizer existence, and finite Sinkhorn uniqueness/convergence targets.
- `ChenGeorgiouPavon2021/ProjectTheoremTargets.lean`: aggregate import for the progress-bar scaffold.

Source scan after this overlay finds 27 executable theorem-target placeholders, all in the new scaffold
or in the newly promoted continuum target statements.  The existing proved finite sequence Gaussian
and finite Wiener dyadic layers remain theorem-bearing and should not be downgraded to assumptions.

## Session 10 (2026-07-10) — repo re-orientation: Mathlib bump, doc de-staling, projective-metric survey

**Author:** Claude Opus 4.8, coordinated by Jon Crall. **No proofs attempted this session** — the goal
was to hand a fresh agent a clean, accurate repo. Nothing in the open-goal set was touched.

### What we found: the docs had drifted badly from the tree
`AGENTS.md` described a repo with **one** open goal (`energy_identity`, the continuum Girsanov edge)
on toolchain `v4.31.0-rc2` / Mathlib `476fb97`. Reality: **16** open goals, none of them
`energy_identity` (closed in Session 3), on `v4.32.0-rc1` / Mathlib `69b866d8`. The Session-9
theorem-target scaffold had also been converted from executable placeholders into
hypothesis/structure interfaces, so its "27 placeholders" no longer existed either.

The actual frontier — invisible in every doc — is **Sinkhorn convergence via the Birkhoff–Hopf
contraction**: `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf{,/PaperRoute/*}`,
`ForMathlib/Analysis/ExpLogBounds.lean`, and `…/Sinkhorn/Convergence/Compactness/FranklinLorenz.lean`.

### Changes landed
- **Mathlib bumped to latest master** `e3b73828` (2026-07-09), same toolchain `v4.32.0-rc1`, so no
  toolchain migration. Recorded a standing policy: *track latest master; older toolchains are not
  kept on disk.*
- **Grep hygiene enforced.** Per the repo rule, Lean comments must never contain the words `sorry` or
  `axiom` (they destroy the proof-debt inventory). Found and fixed the **single** violation, a
  docstring in `BirkhoffHopf.lean`. The rule — and the now-exact grep recipe it buys — is written
  into `AGENTS.md` §5, where it had never been recorded.
- **Docs restructured.** `AGENTS.md` is now **evergreen** (purpose, conventions, traps) and carries
  no counts or revisions; all dated state moved to a new **`STATUS.md`**. `AGENTS.md` §9 is a pointer.
  Both files open with the two commands that re-derive the pin and the open-goal count, so no future
  agent has to trust a doc. Also promoted two long-buried house rules into the evergreen conventions:
  *isolate content to an explicit satisfiable edge* and the *`if False then True` landmine check*.
- **`FOUNDATIONS.md` Chain 3 corrected.** It still framed the chain as "Perron–Frobenius ⇒ Sinkhorn".
  Both halves were wrong: Sinkhorn **existence** is done and used *no* PF (log-domain convex
  minimization), and the live need is Sinkhorn **convergence**, which wants Birkhoff–Hopf instead.

### Survey: is any of this vendorable? (the question that prompted the session)
Two independent sweeps — pinned/master Mathlib, and external Lean repos. Recorded in
`SURVEY_LEADS.md` § *Projective-metric frontier*.

- **Hilbert projective metric: does not exist in Lean. Anywhere.** Not Mathlib, not any repo.
- **Birkhoff–Hopf contraction (`tanh(Δ/4)`): does not exist in Lean. Anywhere.** Strongest negative.
- **Perron–Frobenius: exists, sorry-free, permissive** — `mkaratarakis/HopfieldNet` (MIT, most
  complete; and it *is* the source behind Mathlib PRs #39919/#39920, correcting an earlier note that
  called it independent) and `mrdouglasny/spectral-positivity` (Apache-2.0, cleanest headers).
  **But PF is off our critical path** — nothing downstream consumes an eigenvector.
- **Mathlib PF PR cluster #39917/#39918/#39919/#39920: all still OPEN**, none merged; #39919 has a
  merge conflict and #39920 is blocked on it. A pin bump does not deliver PF. Docs-site 404 confirms.
- **`gpeyre/flow-sinkhorn` re-examined:** zero hits for `hilbert|birkhoff|tanh|projective`. Its
  Sinkhorn convergence goes by KL-descent + Pinsker, *not* the Hilbert metric; no Franklin–Lorenz.
- ⚠️ **Name-collision traps recorded**: Mathlib's `Analysis/Convex/Birkhoff` is Birkhoff–**von
  Neumann**, `Order/Birkhoff` is Birkhoff **representation**, `Dynamics/BirkhoffSum` is **ergodic**;
  every `Hilbert` hit is Hilbert **space**/**projection**; `Analysis/Oscillation` is modulus of
  continuity; `Gauge` is **Minkowski**. None is our target.
- Method caveat: no GitHub token in the survey env, so authenticated **code**-search never ran. Repo
  search + web + clone inspection agreed, but a keyed code-search is the one stone left unturned.

**Conclusion: the two theorems we need must be authored in-house.** That is what `BirkhoffHopf.lean`
is already doing, so the direction was right — it just wasn't written down.

### Audit of the frontier (statements checked, not proved)
- `IsBirkhoffHopfContractionCoefficient` is **non-vacuous and correct**: `∀ x y > 0,
  logSpread(Gx,Gy) ≤ γ · logSpread(x,y)`, and the diagonal `i=i'` term forces `spread ≥ 0`.
- Its coefficient `γ = (B−1)/B`, `B = 1 + Σ cross-ratios`, is **deliberately coarser** than the sharp
  Birkhoff constant `tanh(Δ/4) = (√B−1)/(√B+1)`; since `B ≥ 1+M ≥ √B+1`, the coarse statement is a
  true, weaker corollary. ⚠️ But coarseness does **not** buy an easier proof — the analytic core is
  the same. Prefer proving Carroll's sharp constant and weakening.
- **Two parallel unfinished routes to the same theorem** were discovered: `BirkhoffHopf.lean` is
  Carroll (2004) (3 open goals); `BirkhoffHopf/PaperRoute/*` is Eveson–Nussbaum (1995) (10 open),
  and its own header calls itself "the intended replacement spine for the currently parked
  weighted-average route". **Someone must pick one.** Carroll is far closer to done.
- Verified by dependency audit that `positive_kernel_birkhoff_hopf_contraction` — which *reads* as
  proved — is placeholder-backed through
  `finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound`.
- `PaperRoute/Assemble.lean`'s "public" theorem is `exact` of an open goal: **zero content**.
- `FranklinLorenz.lean` is correctly decoupled: its hard cores take the contraction coefficient as an
  explicit hypothesis, so the two efforts can proceed independently.

### The distilled TeX is the right tool and maps 1:1 onto the open goals
`prose/distilled_literature/` (with original PDFs in `prose/papers/`) already contains
`Carroll2004_birkhoff_contraction.tex`, `EvesonNussbaum1995_birkhoff_hopf.tex`,
`FranklinLorenz1989_matrix_scaling.tex`, `LemmensNussbaum2013_hilbert_metric_survey.tex`,
`Birkhoff1957_extensions_jentzsch.tex`. The goal→source map is now in `STATUS.md`. Highlights:
- Carroll **Step 4** (the two-coordinate inequality) is elementary — AM-GM `1+rsy² ≥ 2y√(rs)` then two
  mean-value comparisons. Its analogue `symmetricTwoByTwoPhi_le` is **already proved** in `TwoByTwo.lean`.
- Carroll **Step 3** (reduce *n* coordinates to 2, by linear programming) and Eveson–Nussbaum **Lemma
  3.11** (two-dimensional subspace reduction) are the two genuinely hard goals.
- Eveson–Nussbaum **Lemma 5.1**'s doubly-stochastic + IVT normalization is **unnecessary** for the
  Lean statement as written: `α = √(cross-ratio)` and the row/column scalings have explicit closed
  forms (the `hdet ≠` hypothesis is exactly "cross-ratio ≠ 1", and a row swap fixes `α > 1`).

### Takeaway for the next agent
Read `STATUS.md`, not this file, for where things are. Then, before writing a single tactic: **decide
between the Carroll and Eveson–Nussbaum routes and delete or explicitly park the loser.** Two
half-built proofs of one theorem is the largest avoidable cost in the current tree.

### Session 10 addendum — route decision + handoff

**Decision (Jon, 2026-07-10): finish the Eveson–Nussbaum `PaperRoute`; *sequester, don't delete,* the
Carroll weighted-average route in `BirkhoffHopf.lean`.** Getting Carroll too would be nice, but the
paper route is the more correct and (per the sources) easier one, and it is what `PaperRoute`'s own
header already declares itself to be.

The dependency analysis that makes this cheap (grep-verified, recorded so nobody redoes it):

- `ForMathlib.Matrix.positive_kernel_strict_birkhoff_contraction_coefficient` is **the public seam** —
  the *only* Birkhoff–Hopf theorem `FranklinLorenz.lean` consumes (lines 507, 529). Both routes exist
  purely to discharge its one open goal, so swapping routes touches nothing downstream.
- **Every weighted-average theorem has zero external consumers.** Sequestration is therefore a pure
  move of eight declarations into `BirkhoffHopf/WeightedAverageRoute.lean`; the shared definitions and
  the proved core lemmas stay in `BirkhoffHopf.lean`.
- ⚠️ The seam has **no** `[Nonempty ι]`/`[Nonempty κ]` but `…_paper_route` does, so wiring them needs an
  empty-type case split (both sides degenerate to `0 ≤ γ·0`).

Two findings worth not rediscovering:

- `positive_kernel_apply_hilbert_log_diameter_bound_paper_route` (open, in `PositiveMatrixDiameter.lean`)
  is *the same statement* as the already-proved, non-placeholder-backed
  `positive_kernel_apply_hilbert_log_diameter_bound_of_apply_crossratio_bound` in the core. It is free.
- `positive_twoByTwo_reduces_to_symmetric_normal_form`: **do not follow Eveson–Nussbaum Lemma 5.1's
  doubly-stochastic + IVT argument.** The Lean statement admits explicit closed-form witnesses. With
  `ρ = A₀₀A₁₁/(A₀₁A₁₀)` — and `hdet` is *exactly* `ρ ≠ 1` — take `α = √ρ`, `c₁ = 1`,
  `c₀ = √(A₀₁A₁₁/(A₀₀A₁₀))`, `r₀ = 1/(A₀₁c₁)`, `r₁ = 1/(A₁₀c₀)`; if `ρ < 1`, swap rows first
  (`ρ ↦ 1/ρ > 1`). Verified algebraically, not yet in Lean.

The ordered first-moves list (cheapest → hardest) lives in `STATUS.md`. No proofs were attempted this
session; the only Lean edits were the two lint fixes recorded above.
