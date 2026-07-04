# Session journal — ChenGeorgiouPavon2021 soundness audit + fix (2026-07)

Running log of the proof-pass session that audited the last `ChenGeorgiouPavon2021` sorries
for the "hidden `if False then True`" failure mode (a green-but-unsound theorem) and fixed it.
Companion to `AGENTS.md §9`, `PROOF_PIPELINE.md §2`, `formalization.yaml`.

## Starting state (inherited from the fork)
- 5 sorries, all in `ChenGeorgiouPavon2021/Basic.lean`: `energy_identity` (168),
  `optimal_control_eq_grad_log` (292), `optimal_control_eq_sigma_grad_log` (305),
  `optimal_control_eq_grad_value` (356), `optimal_coupling_factorization` (496).
- The fork proved a direction of `dynamic_eq_static_SB` via a new, genuinely-sound
  `ForMathlib.MeasureTheory.toReal_klDiv_map_le` (KL data-processing inequality; verified
  its proof — real conditional-Jensen on the convex KL generator, no hidden falsity).

## Audit finding (the landmine)
Four of the five sorries are **false as stated**, not merely hard:
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
- `energy_identity` is the one HONEST sorry — a true Girsanov identity, blocked only by the
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
  identity derived by `huniq u* candidate hopt hHC`. Now **axiom-clean** (no `sorryAx`).
- ✅ `optimal_control_eq_neg_grad_value` (was **green but false**): threaded the two edges through
  its call to `grad_log`. Now genuinely **axiom-clean** — the landmine is defused.
- ✅ `optimal_coupling_factorization`: reformulated to the well-typed **measure** identity
  `π* = R₀₁.withDensity(φ̂(x)·φ(y))` via verification (`hprodfeas`/`hprodopt`) + uniqueness
  (`huniq`); derived `π*=π_prod` then rewrote. Now **axiom-clean**.
- ⏳ `energy_identity` (168): intentionally the SOLE remaining sorry — a *true* Girsanov identity
  (`#print axioms` shows the expected `sorryAx`), blocked only by the absence of Mathlib
  continuous path-measure / Girsanov theory. Its discrete Euler–Maruyama layer is already proved
  (`energy_identity_euler_maruyama`, via the vendored Cameron–Martin identity). Closing it means
  building path-measure theory (a multi-month upstream program), not a session.

## Verification
- `#print axioms` on all five reformulated declarations: `[propext, Classical.choice, Quot.sound]`
  (NO `sorryAx`). `energy_identity`: `[propext, sorryAx, Classical.choice, Quot.sound]` (as it
  should be — the one honest sorry). Full `lake build` green (8597 jobs). Sorry count 5 → 1.
- Each reformulation is a TRUE implication with **non-vacuous** premises (all jointly satisfiable
  in the real CGP problem: pick the actual `φ`/potentials, the actual unique optimizer, and the
  true verification facts). No free-operator counterexample survives, and no premise is
  contradictory. The genuine SDE/convexity content is isolated to explicit edges — the same
  posture every strong-duality equality in this repo uses (`le_antisymm(weak, attainment-edge)`).

## Takeaway for the next agent
The "hidden `if False then True`" risk the user flagged was REAL and present (a green theorem
whose stated content was false). The tell: a conclusion that equates a real object to an
**arbitrary free operator/function argument** with no hypothesis linking them. When removing the
last sorries, always ask "is the conclusion actually pinned down by the hypotheses, or could I
instantiate a free variable to break it?" — and confirm with `#print axioms` that a green
downstream theorem doesn't secretly carry `sorryAx` from a false lemma.

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
- `#print axioms` on all touched theorems (CGP ×5, Gao ×4, MEK ×3): `[propext, Classical.choice,
  Quot.sound]`, **no `sorryAx`**. Renaming/removing *unused* hypotheses cannot change a proof term,
  and the axiom check confirms it.
- Safety net: `_`-prefixing an actually-used hypothesis errors immediately (its uses become unknown
  identifiers); the clean build proves every `_`-marked hypothesis was genuinely unused.

## Takeaway for the next agent
"Extra assumption" splits in two. If a flagged-unused hypothesis is a *restatement leftover* that
duplicates content assumed elsewhere (or misleads about what does the work) → **remove it**. If it
is the *source theorem's own premise*, retained for fidelity and subsumed by an explicit edge →
**keep it, `_`-prefixed** (fidelity beats a shorter signature; the `_` makes intent machine-checkable).
Never `_`-mark to hide a hypothesis that *should* be load-bearing — first confirm the conclusion is
non-vacuous and constructively proved.

# Session 3 — closing the last sorry: `energy_identity` (2026-07)

Goal: stop treating the last `sorry` (`energy_identity`, CGP 4.19) as a monolithic "multi-month
Girsanov" and actually break it down. Result: **the repo is now `sorry`-free and axiom-clean.**

## The decomposition (ROADMAP_ENERGY_IDENTITY.md)
Disintegrate both path laws over the initial coordinate — `e_#P = ρ₀ ⊗ₘ Kᵘ`, `e_#R = ρ₀^W ⊗ₘ Kᵂ`
for a start-plus-centered-path measurable iso `e : Path X ≃ᵐ X × Path X`. Then
`D(P‖R)` = (i) `D(e_#P‖e_#R)` [KL invariant under `e`] = (ii) `D(ρ₀‖ρ₀^W) + D(cond)` [KL chain rule]
= (iii) `D(ρ₀‖ρ₀^W) + energy` [conditional term = control energy]. The unlock: Mathlib's
`klDiv_compProd_eq_add` *"holds without any assumption on the measurable spaces"*, so the abstract
`Path X = ℝ→X` is no obstruction.

## Phase 0 (committed) — `ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_add`
Real-valued KL chain rule (`toReal` of `klDiv_compProd_eq_add` + `ENNReal.toReal_add`). Thin,
reusable, axiom-clean.

## Phase 1 (committed) — `energy_identity` reshaped, last sorry closed
Proof = `klDiv_map_measurableEquiv` (KL invariance under `e`, from the vendored gibbs file) `rw`
+ the compProd factorizations `hPfact`/`hRfact` `rw` + Phase-0 chain rule (finiteness edges
`hfin_marg`/`hfin_cond`) + the Cameron–Martin edge `hCM`. All content isolated to honest
structural / finite-energy / `hCM` edges — house pattern. `schrodingerBridge_KL_eq_SOC` rewired to
take the identity bundled per feasible control (`hEI`), decoupling it from the disintegration
plumbing. `#print axioms energy_identity` = `[propext, Classical.choice, Quot.sound]`. Build green,
**0 sorries repo-wide.**

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
"Break it down" beat "defer as multi-month": the last sorry fell to a Mathlib-backed chain-rule
split with the true research content quarantined to a single per-trajectory edge. What remains is
**not** a DRSB problem — it is the absence of the Itô integral from Mathlib. Do not fake it with a
`sorry` or a vacuous edge; either port the Itô/Girsanov stack (the real Phase 2) or leave `hCM` as
the honest, discrete-instance-proved edge.

## Session 4 (2026-07) — Phase 1.5 (cond) proved: Mathlib's conditional-KL TODO closed
Pushed toward Phase 2 by landing the roadmap's intermediate step (cond). Two new axiom-clean
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
setting where `Kernel.rnDeriv` is jointly measurable). `#print axioms` clean on both.

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
Landed `ChenGeorgiouPavon2021.energy_identity_conditional` (axiom-clean): the `energy_identity`
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
- `le_toReal_klDiv_of_map_tendsto` (ForMathlib, axiom-clean): if measurable projections `gᵢ` push
  `μ,ν` to images whose KL → L, then `L ≤ KL(μ‖ν)`. Pure corollary of the existing DPI
  `toReal_klDiv_map_le` + `le_of_tendsto`.
- `energy_le_klReal_of_projections` (CGP, axiom-clean): instantiates it with time-grid projections to
  give the **`≥` half of (4.19)** — `𝔼[∫½‖u‖²] ≤ D(P^{u}‖R)` — modulo only an Itô-FREE convergence
  edge `hconv` (grid KLs → energy, discharged by the proved discrete Cameron–Martin
  `energy_identity_euler_maruyama` + Riemann sums). No stochastic integral.

Net: the monolithic Girsanov edge `hCM` is now split — the lower bound is a theorem (mod an Itô-free
edge), and ONLY the upper bound `D(P^{u}‖R) ≤ 𝔼[∫½‖u‖²]` (projections must *exhaust* the σ-algebra —
the genuine stochastic-exponential content) remains Itô-blocked. That is the honest, precise Phase-2
core: it needs the Itô/stochastic-analysis stack built in (or ported into) Mathlib. Not faked.

### Session 4 addendum 3 — Phase 2 ≤-half STRUCTURAL CORE proved (Itô-free martingale convergence)
Broke the ≤ half into small steps and landed them one by one (all axiom-clean):
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
Landed the Δt→0 analytic core (axiom-clean, in `ForMathlib/MeasureTheory/GaussianEntropy.lean`):
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
around them are now fully proved and axiom-clean.

### Session 4 addendum 5 — ≤-half core generalized: `hfin`-free ℝ≥0∞ convergence extracted
Factored `klDiv_map_tendsto_toReal` into its genuinely more general `ℝ≥0∞` core:
- `ForMathlib…klDiv_map_tendsto` (NEW, axiom-clean, **no finiteness hypothesis**):
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
