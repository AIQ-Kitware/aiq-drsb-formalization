# STATUS.md — where this repo actually stands

> **Dated snapshot. This is the file that goes stale — update it, don't trust it blindly.**
> Evergreen orientation, conventions, and the traps live in [`AGENTS.md`](AGENTS.md);
> the running narrative of how we got here lives in [`JOURNAL.md`](JOURNAL.md);
> the work plan lives in [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).
>
> **Verify before you trust.** Two commands re-derive this whole file's factual core:
> ```bash
> cat lean-toolchain && grep -A2 '"name": "mathlib"' lake-manifest.json   # the real pin
> grep -rn --include=*.lean --exclude-dir=.lake --exclude-dir=.reference-clones --exclude-dir=reference -w sorry .
> ```

**Last updated: 2026-07-10**

## Snapshot

| | |
|---|---|
| Toolchain | `leanprover/lean4:v4.32.0-rc1` |
| Mathlib | `e3b73828…` (2026-07-09), `inputRev = master` — **policy: track latest master** |
| Open goals | **0** — the repo is `sorry`-free |
| DRSB card claims | ✅ **proved** (`wdrsb_cost_bound`, `sdrsb_cost_bound`) |
| WDRSB card assumption surface | ✅ **minimal** — the `hOT` attainment edge is **deleted**, not assumed |
| SDRSB card assumption surface | ✅ **minimal** — attainment, disintegration and transport edges all discharged; **no second moments** (plan carries `integrable_cost`) |
| Strong duality — Wasserstein | ✅ **EDGE-FREE** (`hge` proved: `ForMathlib.OT.dualValue_le_droValue`) |
| Strong duality — Sinkhorn | ✅ proved; `hge` still a hypothesis (same recipe applies) |
| `energy_identity` | ✅ **closed** — Girsanov content isolated to the explicit `hCM` edge |
| Birkhoff–Hopf contraction | ✅ **proved twice**, by two independent routes |
| Sinkhorn convergence | ✅ **proved** — no placeholder anywhere on the critical path |

Everything is `lake build` green and axiom-clean (`propext, Classical.choice, Quot.sound` only —
no `sorryAx`). ⚠️ `lake env lean <file>` typechecks source but `#print axioms` resolves against the
*compiled* `.olean`s: run `lake build` before trusting an axiom audit.

---

## CURRENT FRONTIER (2026-07-10) — none on the card path; the deferred campaign is next

**Both card claims are now edge-free.** `wdrsb_cost_bound` and `sdrsb_cost_bound` each take only
checkable regularity — integrability, finite second moments, and (for SDRSB) log-partition
conditions on the *dual*. No optimal-transport hypothesis, no attainment hypothesis, no
disintegration hypothesis. See § "The card claims' assumption surface".

The last blocker — `Wkappa` being `toReal`-valued, so that a singular coupling scored `0` entropy
and ball membership carried no information — is **fixed definitionally**. `Wkappa` now infimises
the `ℝ≥0∞` objective `sinkhornObjectiveENN`, in which a singular coupling correctly scores `⊤` and
drops out. Consequently `ForMathlib.OT.exists_isSinkhornPlan_of_mem_sinkhornBall` is a **theorem**:
ball membership yields, for each `η > 0`, a finite-entropy transport plan of budget `≤ ε + η`.

Two design points worth not re-deriving:

- `sinkhornBall` is `{μ | Wkappa ≠ ⊤ ∧ (Wkappa).toReal ≤ ε}`, **not** `{μ | Wkappa ≤ ofReal ε}`.
  The two agree for `ε ≥ 0`, but `ENNReal.ofReal` sends every negative radius to `0`, which would
  make a negative-radius ball equal `{μ | Wkappa = 0}` — nonempty when `p₀ = ν = μ = δₐ` — and
  would **falsify** `WangGaoXie2023.primal_feasible_radius_nonneg`.
- `ForMathlib.OT.mem_sinkhornBall_reference` proves the ball is **not vacuous** (`ν` itself is in
  it once the radius covers the independent coupling's cost). A theorem quantified over an empty
  ball would be vacuously true; this is the check the `if False then True` audit lesson demands.

`wassersteinBall`/`otCost` still carry the analogous **Bochner**-junk pathology, neutralised by the
`HasSecondMoment` hypotheses rather than by a better definition. Making `otCost` `ℝ≥0∞`-valued
would let `wdrsb_cost_bound` drop `hμ2`/`hp2` too, but `otCost` is used with a general cost `c` by
`BlanchetMurthy2019` (14 sites), `GaoKleywegt2023` (5) and `MohajerinEsfahaniKuhn2018` (4),
several of them constructively (`otCost_le_couplingCost` inside worst-case-measure builds). That is
a real refactor, not a rename, and it is *not* required for soundness of anything now proved.

## Upstream challenge layer (2026-07-10)

Reusable, paper-agnostic results are staged in `ForMathlib/` and exposed as comparator
challenges under `Challenge/`, mirroring `aiq-dkps-formalization`:

* **`MathlibCandidate/`** — the focused upstream push, three verified Mathlib gaps:
  `DonskerVaradhan` (the Gibbs variational formula — Mathlib has `Measure.tilted` and all its `llr`
  infrastructure but no DV statement), `KLConvexity` (`klDiv_mix_le`; Mathlib has the `smul` lemmas
  but no convexity of `klDiv` in its first argument, in either `ℝ` or `ℝ≥0∞`), and `Supergradient`
  (Mathlib has `ConcaveOn` and slope lemmas but **no** sub/supergradient existence).
* **`MathlibPending/`** — proven but held back: `KLChainRule`, `GibbsTilt`, `MeasurableArgmax`,
  `KLLowerSemicontinuous`, `IntegrableIntegralCompProd`, plus `TiltedKernel` and `BirkhoffHopf` as
  dependency-audit `Leaderboard`s only (their statements name project definitions, so a Mathlib-only
  `Conformance` cannot state them).

The DRSB paper libraries and the `Drsb` capstone are deliberately **not** comparator challenges: the
comparator certifies that a proof is dependency-clean, not that `couplings`/`sinkhornBall`/`droValue`
faithfully model the papers. That is a human reading task.

⚠ One gap claim was **wrong** when checked: Mathlib *does* have the additive KL chain rule
(`klDiv_compProd_eq_add`). What it lacks is the *disintegration* form
`klDiv (μ⊗ₘκ) (μ⊗ₘη) = ∫⁻ x, klDiv (κ x) (η x) ∂μ`. Corrected in `Challenge/README.md`.

All 18 listed leaves are axiom-clean and pass the local pre-flight
(`scripts/check_comparator_signatures.py`). The **real landrun comparator has not yet been run.**

## The remaining capstones (the next campaign)

**Nothing below is on the card path** — `wdrsb_cost_bound` and `sdrsb_cost_bound` are edge-free.
These are the strong-duality and continuum capstones. Re-verified against the pin 2026-07-10;
"ABSENT" means grep-verified absent from the pin *and* from `.reference-clones/`.

### Tier 0 — no new mathematics; wiring only

| Edge | Where | Status |
|---|---|---|
| ~~`hbddP`~~ | all four strong-duality thms | ✅ **DELETED (2026-07-10).** A function bounded above has bounded-above expectations, and a dual over `lam ≥ 0` already asserts `BddAbove (Set.range V)` as its `lam = 0` conjugate. `ForMathlib.OT.DroValue`. Four remain, only on worst-case-*structure* theorems (GK cor1/cor2ii, MEK), which carry no boundedness hypothesis to derive from. |
| ~~`hSinkAll`~~ | `WangGaoXie2023.strong_duality` | ✅ **DISCHARGED (2026-07-10).** The cost wart is fixed (Sinkhorn layer parametrized by `c`), the disintegration machinery moved into `WangGaoXie2023` next to `logPartition`, and `sinkhorn_cost_bound` is now edge-free. `strong_duality` assumes only regularity + `hattain`, and no longer needs a normed group. |
| `hKL` (dyadic KL-exhaustion) | `Continuum/Assembly.lean` | `KLExhaustion.lean` says it outright: once the dyadic σ-algebras are packaged as a filtration and identified with the projections, "the proof is exactly the already-proved `ForMathlib.MeasureTheory.klDiv_map_tendsto`". Structural, not mathematical. |
| `otCost` → `ℝ≥0∞` | `ForMathlib.OT` | The `Wkappa` fix, applied to the Wasserstein side. Would let `wdrsb_cost_bound` drop `hμ2`/`hp2`. |

### Tier 1 — the duality gap `hge`: ✅ **PROVED (2026-07-10)**

`hge` is no longer a hypothesis. `ForMathlib.OT.dualValue_le_droValue` proves the `≥` half of
Wasserstein-DRO strong duality — Blanchet–Murthy Thm 1 / Gao–Kleywegt Thm 1 — and
`GaoKleywegt2023.dualValue_le_primalValue` specializes it. Edge-free capstones:
`GaoKleywegt2023.strong_duality_thm1_of_regularity`, `Drsb.wdrsb_strong_duality_of_regularity`.

Three ingredients, all in `ForMathlib`:

1. `ForMathlib.OT.exists_coupling_lagrangian_ge` — the **converse Lagrangian bound**: `𝔼_ν[φ_λ]` is
   achieved, to within `ε`, by pushing `ν` forward along a measurable near-maximizer of the
   `c`-transform. The selector is `ForMathlib.MeasureTheory.exists_measurable_eps_argmax_of_separable`
   and needs **no Kuratowski–Ryll-Nardzewski**: on a separable domain a continuous integrand attains
   its supremum to within `ε` on a countable dense set, and `Nat.find` on an enumeration is
   measurable.
2. `ForMathlib.Analysis.exists_nonneg_multiplier'` — the **optimal multiplier**. Mathlib has
   `ConcaveOn` and the slope lemmas but **no sub/supergradient existence at all** (grep-verified);
   the one-dimensional case is `ForMathlib/Analysis/Supergradient.lean`.
3. `ForMathlib.OT.concaveOn_droValueAt` — the **DRO value function is concave and nondecreasing**,
   because the coupling set is convex (`mix_mem_couplings`) and cost/reward are affine on it.

**The trick in the assembly:** run (1) at `λ = λ* + η` for small `η > 0`, never at `λ*` itself. That
supplies `λ > 0` for the cost-integrability step *and* eliminates the `λ* = 0` case (inactive
constraint), since `t ≥ 0` makes `η(δ − t) ≤ ηδ`, absorbed by `η ≤ ε/(2δ)`. The dual set's
`BddBelow` — needed for `csInf_le` — comes from the *forward* Lagrangian bound at the zero-cost plan.

⚠ **Three claims made in this file earlier today were wrong**, each corrected only by attempting the
proof: `hge` is *not* an extreme-value argument reachable by Prokhorov; it does *not* need KRN; and
Chain 1's `XL` convex-analysis rows were *not* the critical path. What was actually missing was one
thirty-line supergradient lemma. Prokhorov / Portmanteau remain the tool for the **separate**
worst-case-measure-*existence* statements (`GaoKleywegt2023.worstCase_structure_cor1`,
`MohajerinEsfahaniKuhn2018.worstCase_exists`), which still assume attainment — a strictly stronger
statement than `hge`, and one the cards never need.

### The Sinkhorn `hge` — ✅ **PROVED (2026-07-10)**

`WangGaoXie2023.strong_duality` and `Drsb.sdrsb_strong_duality` **no longer carry `hge`.** It is
discharged by `WangGaoXie2023.sinkhornDual_le_droValue`, assembled from three ingredients:

* **(1) the converse Lagrangian bound** — `ForMathlib.OT.exists_coupling_sinkhorn_lagrangian_eq`
  (`WangGaoXie2023.exists_coupling_lagrangian_eq_logPartition` is the `rfl`-thin receipt). For every
  `λ, κ > 0`,

  `𝔼_μ[f] − λ·(𝔼_γ[c] + κ·KL(γ‖μ̂⊗ν)) = 𝔼_μ̂[v_x(λ)]`,  `γ = μ̂ ⊗ₘ P`,  `P x = ν.tilted ((f − λc(x,·))/(λκ))`.

  An **equality with an explicit witness**, not an `ε`-approximation: the Gibbs (over-measures)
  Donsker–Varadhan supremum is attained at the tilted measure, where the dual (over-functions)
  supremum the Wasserstein path uses is not. No measurable ε-argmax selection is needed.
  New API: `ForMathlib.MeasureTheory.tiltedKernel`, `klDiv_tilted_ne_top`,
  `entropic_gibbs_attained_tilted`, `ForMathlib.OT.integrable_integral_compProd`.

* **(2) the optimal multiplier** — `ForMathlib.Analysis.exists_nonneg_multiplier'`, unchanged.

* **(3) concavity of the entropic value function** — `ForMathlib.OT.concaveOn_sinkhornValueAt`,
  in the new `ForMathlib/OptimalTransport/SinkhornValueFunction.lean`. `couplingCost` is affine and
  `klDiv` is convex in its first argument — `ForMathlib.MeasureTheory.klDiv_mix_le`, `ℝ≥0∞`-valued
  and with **no finiteness hypotheses**, so it also supplies `klDiv_mix_ne_top`. The coupling set is
  convex in the *second* marginal (`mix_mem_couplings'`, the mirror of `mix_mem_couplings`, since
  Sinkhorn's nominal measure is the first marginal).

The assembly is `ForMathlib/OptimalTransport/SinkhornStrongDualityGe.lean`
(`sinkhornDual_le_sinkhornValueAt`, `sinkhornValueAt_le_droValue`), mirroring the Wasserstein
`StrongDualityGe.lean`: run (1) at `λ = λ* + η`, never at `λ*`. `BddBelow` of the dual set — without
which the `sInf` is the junk value `0` — is *derived*, from weak duality at a feasible point
(`WangGaoXie2023.expect_le_sinkhornDualObjective`, extracted for the purpose).

#### The one hypothesis that replaced `hge`: **Slater**

`hge` is gone, but not for free. The Wasserstein assembly takes its supergradient at `δ > 0` knowing
the value set is nonempty at `t = 0`, because the diagonal coupling has zero cost. **The entropic
objective has no zero** — even `γ = μ̂⊗ν` pays `∫∫c dμ̂dν`. So `ε` is interior to the value function's
domain exactly when some coupling is *strictly* feasible. Both capstones now take

`{t₀ : ℝ} (ht₀ : t₀ ∈ ForMathlib.OT.sinkhornDomain c f κ μ̂ ν) (ht₀ε : t₀ < ε)`

in place of `hge`. Mere feasibility (`hfeas`, i.e. `ε ≥ inf_γ obj γ`) is **not** enough, and no
rearrangement of the proof avoids it. This is a strictly better assumption surface: Slater is
checkable, `hge` was the conclusion. And it is **checked**: `Drsb.sdrsb_strong_duality_of_radius_gt_independent_cost`
discharges Slater from the single inequality `𝔼_{p₀⊗ν}[c] < ε`, because the independent coupling
`p₀ ⊗ ν` has vanishing entropic term (`ForMathlib.OT.sinkhornObjective_prodCoupling`). So the
capstone's hypotheses are jointly satisfiable, and the theorem is not vacuous. Whether duality survives at the boundary `ε = inf_γ obj γ` is
not established here either way.

Also proved on the entropic side: the DV **dual** variational formula
(`toReal_klDiv_eq_sSup_dvDualSet`) and setwise lsc of `klDiv` (`toReal_klDiv_le_of_tendsto_integral`).

### Tier 2 — Schrödinger-bridge structure (`ChenGeorgiouPavon2021.SocOt`)

| Edge | Mathematical content | Source |
|---|---|---|
| `hglue` | Léonard's gluing / path-space reconstruction (static coupling lifts to a path law of equal entropy) | Léonard, *A survey of the Schrödinger problem*, arXiv:1308.0215, Prop 2.3 / Thm 2.4. No Lean source. |
| `hstrict`, `huniq` | strict convexity of KL over `Π(ρ₀,ρ₁)`; uniqueness of the I-projection | Csiszár 1975 (*I-divergence geometry*). Mathlib has `strictConvexOn_klFun` — lifting it to `klDiv` over couplings is real but tractable. |
| `hprod_exists`, `hprodopt` | solvability of the Schrödinger system (existence of potentials `φ̂, φ`) | Rüschendorf–Thomsen; Nutz, *Introduction to Entropic Optimal Transport*, Thm 4.2. **The finite case is already proved in this repo** (matrix scaling + Birkhoff–Hopf); the continuum case is Csiszár's I-projection. |
| `hHC` | Hopf–Cole verification: the value-gradient control is optimal | CGP Thm 4.22; a stochastic-control verification theorem. Needs the SOC/PDE layer. |

### Tier 3 — continuum Girsanov (`hCM`, `hconv`, `hac`) — the genuine long-horizon port

- `hac` (**Cameron–Martin quasi-invariance**, `W.map (·+h) ≪ W`) is the nearest. Both halves of the
  route now exist in-repo: the continuum reference `ForMathlib.MeasureTheory.wienerMeasure` (vendored
  Kolmogorov extension, sorry-free, axiom-clean) and `ForMathlib.absolutelyContinuous_of_densityProcess`
  (`≪` from a uniformly-integrable martingale density process). Missing: the CM density process on
  `wienerMeasure` (Brick 2 of `ROADMAP_ENERGY_IDENTITY.md`), which needs finite-dimensional Gaussian
  **Radon–Nikodym derivatives** (we have only the KL, `klDiv_stdGaussian_map_add`). Paper: Bogachev,
  *Gaussian Measures*, Thm 2.4.5; Da Prato–Zabczyk.
- `hCM` / `hconv` (**Girsanov**) — `⚠️ ABSENT EVERYWHERE`. `RemyDegenne/brownian-motion` has Brownian
  existence sorry-free but only a *simple-process* stochastic integral (its `DoobMeyer.lean` carries
  25 open goals). `raphaelrrcoelho/formal-mathfin` has an Itô development, but its `Girsanov.lean` is
  a single Black–Scholes martingale statement and `GaussianGirsanov.lean` is a finite-dimensional
  Esscher tilt — **neither is the Girsanov theorem**. Stochastic exponential (Doléans-Dade): absent
  everywhere. This remains the multi-session port, and no existing Lean artifact shortcuts it.
- **Kakutani / infinite-product absolute continuity**: the *sequence-model* Cameron–Martin/Kakutani
  theorem is **already proved** here (`ForMathlib/MeasureTheory/GaussianCameronMartin.lean`, Phase 2a:
  `klDiv_stdSeqGaussian_map_add_of_summable` + the `⊤` converse). What is still absent everywhere is a
  general Hellinger/Kakutani dichotomy — needed only if a route other than the CM density process is
  taken.

**Kolmogorov extension is CLOSED**, not deferred: vendored as `ForMathlib/KolmogorovExtension/`
(Apache-2.0, attributed) and used by `ForMathlib.MeasureTheory.wienerMeasure`; both sorry-free and
axiom-clean. Mathlib's own `Probability/BrownianMotion/` still lacks it.

## The card claims' assumption surface

`wdrsb_cost_bound` used to assume `hOT`: that `W₂²(μ,p₀) ≤ ε` is witnessed by a coupling of cost
`≤ ε` with integrable cost. **Both halves of that were theorems, and it is now deleted.**

- *Attainment was never needed.* `W₂²` is defined as an `sInf`, so it yields a plan of cost `< ε + η`
  for every `η > 0` and **never** one of cost `≤ ε` — that is the attainment theorem, false without
  compactness/lower-semicontinuity. Run the Lagrangian bound at `ε + η` and let `η ↓ 0`
  (`le_of_forall_pos_le_add`). The card's `≤` half never touched the T4 seam.
- *Integrability was not an assumption.* Finite second moments of the marginals force **every**
  coupling's quadratic cost to be integrable (`‖x−y‖² ≤ 2‖x‖² + 2‖y‖²`).

What replaced it: `HasSecondMoment μ` and `HasSecondMoment p₀`. These are **strictly weaker**, and
that is machine-checked, not asserted: `Drsb.wdrsb_cost_bound_of_ot_edge` derives the card bound from
the *old* hypothesis set, using `integrable_normSq_of_mem_couplings_of_integrable_cost` to get `hμ2`
out of `hOT` + `hp2`. The converse fails — no moment condition manufactures a minimizer.
`sdrsb_cost_bound_of_attained_disintegration` is the same receipt on the entropic side.

`wdrsb_strong_duality` additionally now **discharges** `hfeas` (the diagonal coupling gives
`W₂²(p₀,p₀) ≤ 0 ≤ ε`) and `hOT`. Its surviving edges are exactly the `≥`/worst-case-measure
attainment (`hattain`, `hbddP`) — the genuine T4 seam — plus regularity.

On the entropic side `sdrsb_cost_bound` lost all three edges in turn — attainment, then
disintegration, then transport:

- **Attainment**, by the same `sInf`/`ε + η` argument as WDRSB.
- **Disintegration**, by `Drsb.hasSinkhornDisintegration_of_isSinkhornPlan`: hand over a transport
  plan `γ ∈ Π(p₀, μ)` with `γ ≪ p₀ ⊗ ν` and finite `klDiv`; `Measure.condKernel` supplies `P`,
  `Measure.integral_compProd` moves both the reward and the cost onto the slices, and the chain rule
  (`η := Kernel.const X ν`) turns the entropy into `∫ KL(P x ‖ ν) dp₀`. The a.e. slice facts —
  `P x ≪ ν`, `Integrable (llr (P x) ν)` — fall out of `klDiv_ne_top_iff` on the a.e. finite slices.
  *Prerequisite:* `WangGaoXie2023.sinkhorn_weak_duality_kernel` and `IsSinkhornDisintegration` had to
  be weakened from `∀ x` to `∀ᵐ x ∂p₀`. A `condKernel` is only determined up to a `p₀`-null set, so
  the `∀ x` form was unusable by its one intended caller. `isProbabilityMeasure` stays `∀ x`
  (`condKernel` is a Markov kernel on the nose).
- **Transport**, by `ForMathlib.OT.exists_isSinkhornPlan_of_mem_sinkhornBall`, once `Wkappa` became
  `ℝ≥0∞`-valued: ball membership *is* the plan.

Canonical objects, not anonymous existentials: `ForMathlib.OT.IsSinkhornPlan` (a coupling with
`mem_couplings`, `absolutelyContinuous`, `klDiv_ne_top`, `objective_le`) and
`Drsb.IsSinkhornDisintegration` (a conditional family, twelve named fields) with its existential
wrapper `Drsb.HasSinkhornDisintegration`. Proofs use field names, not conjunct positions.

New reusable layers, both upstreamable (Mathlib has no Kantorovich layer at all):
`ForMathlib/OptimalTransport/Coupling.lean` (product & diagonal couplings, `couplings_nonempty`,
near-optimal plan extraction, second-moment ⟹ cost-integrability and its converse, the `klReal` junk
lemma) and, in `ForMathlib/MeasureTheory/KLChainRule.lean`, the slice consequences of a finite
conditional KL (`aemeasurable_klDiv_kernel`, `ae_klDiv_kernel_ne_top`,
`integrable_toReal_klDiv_kernel`).

## The projective-metric frontier — closed

The finite Birkhoff–Hopf contraction theorem, which the
2026-07-10 survey found **exists nowhere in Lean** (`SURVEY_LEADS.md` § Projective-metric frontier),
is now proved here from scratch — and proved *twice*, deliberately.

### Two independent proofs of the same seam

`ForMathlib.Matrix.positive_kernel_strict_birkhoff_contraction_coefficient` is the public seam that
`FranklinLorenz.lean` consumes. Both routes discharge it; neither uses the other (grep-verified: no
`PaperRoute` file references any Doeblin theorem). They share only the definitions and the
elementary `sSup`/positivity lemmas.

| | `BirkhoffHopf.lean` — **Doeblin route** | `PaperRoute/*` — **Eveson–Nussbaum route** |
|---|---|---|
| Shape | one direct estimate | the paper's 8-step chain, theorem-for-theorem |
| Key step | sum `hweight` over one index ⇒ pointwise `p ≤ B q` | reduce to a 2-dimensional subspace |
| Analytic core | weighted AM–GM (`Real.geom_mean_le_arith_mean2_weighted`) | MVT on `g t = log(αe^t+1) − log(e^t+α)` |
| Constant | coarse `(B−1)/B` directly | sharp `(α−1)/(α+1)`, then weakened |
| Calculus? | **none** | yes (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) |

**The Doeblin route is the short one and it is not in the literature we distilled.** The published
proofs treat the two-atom case as the irreducible core and reduce the `n`-coordinate problem to it —
Carroll (2004) Step 3 by linear programming, Eveson–Nussbaum by 2-dimensional subspaces. Neither
reduction is needed: normalizing `p_j ∝ a_j y_j`, `q_j ∝ b_j y_j` and **summing the pairwise weight
hypothesis over one index** collapses it to the pointwise Doeblin condition `p_j ≤ B q_j`. Two linear
facts then force `u/v ≤ (λ+R)/(1+λR)`, and one application of weighted AM–GM finishes. The
coarseness of `(B−1)/B` is exactly what makes that last step elementary — the earlier note in this
file claiming the coarse constant "does not appear to make the proof easier" was wrong.

Consequently `two_point_weighted_average_…` is now a **corollary** (instantiate the finite theorem at
`κ = Fin 2`), not a prerequisite. The arrow in the papers is reversed.

### Why keep both

The paper route earns its keep: it makes the Lean text checkable against a citation, line by line
(Prop 2.9(b), Lemma 3.11, Lemma 3.12, Lemma 5.1, Thm 5.3, Thm 6.2 each have a named theorem), and it
proves the **sharp** constant `(α−1)/(α+1)` where the Doeblin route only gets `(B−1)/B`. If anyone
ever needs the sharp Birkhoff constant `tanh(Δ/4)`, `PaperRoute/TwoByTwo.lean` already has it.

Two deliberate departures from the sources, both recorded in the docstrings:

- **Prop 2.9**: the *nonnegative-hull* statement is the general one — the argument never uses
  `∑ w = 1` — so the convex-hull statement is its corollary rather than a separate proof.
- **Lemma 5.1**: the paper's doubly-stochastic + IVT normalization is unnecessary. With
  `ρ = A₀₀A₁₁/(A₀₁A₁₀)` (and `hdet` says exactly `ρ ≠ 1`), the witnesses `α = √ρ`,
  `colScale = (√(A₀₁A₁₁/(A₀₀A₁₀)), 1)`, `rowScale = (1/A₀₁, 1/(A₁₀·colScale₀))` are explicit;
  `ρ < 1` is handled by a row swap, which sends `ρ ↦ 1/ρ`.

### ⚠️ A statement bug that was found and fixed

`hard_core_franklinLorenz_right_column_pairwise_log_correction_geometric_bound` assumed
`IsBirkhoffHopfContractionCoefficient G γ` **alone**. That is not enough: the orbit alternates
`a (k+1) = p / (G · b k)` and `b (k+1) = q / (Gᵀ · a k)`, so the contraction recursion applies each
kernel on alternate half-steps. Deriving `Gᵀ`'s coefficient from `G`'s would require `γ` to be the
*sharp* Birkhoff constant — a strictly harder theorem, so the hypothesis is now explicit and is
discharged by `positive_kernel_strict_birkhoff_contraction_coefficient_transpose`, whose explicit
coefficient is transpose-invariant.

**The general lesson:** an alternating algorithm needs its operator's coefficient *and its
transpose's*. Grep for any other seam that takes a one-sided contraction hypothesis.

### How Sinkhorn convergence closes

`FranklinLorenz.lean`'s two hard cores are proved. With `S k = Gᵀ·a k`, `T k = G·b k`, the updates
read `b (k+1) = q / S k`, `a (k+1) = p / T k`. Since `x ↦ c/x` is a projective isometry, the two
correction spreads `α k = d(a (k+1), a k)`, `β k = d(b (k+1), b k)` satisfy `β (k+1) ≤ γ·α k` and
`α (k+1) ≤ γ·β k`. So `M k = max (α k) (β k)` obeys the **single-step** recursion `M (k+1) ≤ γ·M k`,
giving `M k ≤ γ^k · M 0` with no parity argument. Hard core 4 (the left/row side) is then an
*instantiation*, not a second proof: `IsFiniteFranklinLorenzScalingOrbit` is symmetric under
`(p,q,G,a,b) ↦ (q,p,Gᵀ,b,a)` — the row and column updates swap into each other.

### Upstreaming

Nothing here exists in Mathlib. The clean PR candidates, in dependency order:
`finiteHilbertProjectiveLogSpread` + its `sSup` API → `positive_kernel_birkhoff_hopf_contraction`
(the Doeblin proof is short and self-contained) → `matrix_scaling_exists`. Already queued from
earlier passes: `toReal_klDiv_map_le` (KL data-processing) and
`exists_measurableEmbedding_nat_of_separating`.

---

## Landed work (history)

*Kept for provenance. The per-session narrative — including the soundness audits and what each
proof actually cost — is in [`JOURNAL.md`](JOURNAL.md).*

- **Next steps + the full triage live in [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).**
  Per the user (2026-07): **no Fable** — decompose each remaining target into its natural
  subproblems and prove step-by-step with the thinking budget turned up. The SDE/PDE and
  OT-measurable-selection blocks may still need a documented `dependency` or a Mathlib-infra lift
  (decide with the coordinator). ForMathlib upstreaming queue:
  DV ✓, Normalization ✓, WeakDuality ✓ (three kernels, incl. the Ξ-restricted one),
  SinkhornScaling ✓ (`matrix_scaling_exists`), **KLDataProcessing ✓ (`toReal_klDiv_map_le` — the
  KL data-processing inequality; a clean standalone Mathlib PR candidate)**,
  **PathEmbedding ✓ (`exists_measurableEmbedding_nat_of_separating` — standard-Borel + countable
  separating family ⇒ measurable embedding into `ℕ→ℝ` with measurable left inverse; also a Mathlib
  PR candidate)**.
- **Source-pass note (2026-07-07):** `ForMathlib/MeasureTheory/GaussianCameronMartin.lean`
  stages the next sequence-model Cameron–Martin brick from `PLAN_CONTINUUM_CLOSURE.md` as a
  candidate no-placeholder overlay: iid `stdSeqGaussian`, `prefixFiltration`, finite-prefix marginals,
  shift/restriction commutation, and `cmDensityProcess`. The producing sandbox had no Lean compiler;
  run `lake env lean ForMathlib/MeasureTheory/GaussianCameronMartin.lean` before marking M2.4 done.

- **Plan A(i) DONE (2026-07-04) — the continuum embedding edge is now a THEOREM**
  (`ForMathlib/MeasureTheory/PathEmbedding.lean`, all dependency-clean; JOURNAL Session 4 addendum 8).
  `energy_eq_klReal_via_embedding`'s abstract measurable-embedding hypothesis is *constructed* for the
  continuous-path model (`C(T,ℝ)`, dense-time evaluation), via Mathlib's existing `ContinuousMap`
  Polish instances + Lusin–Souslin — **no brownian-motion vendor needed**. `eq_toReal_klDiv_continuousMap_of_tendsto`
  is the continuum identity for `C(T,ℝ)` laws with the embedding edge discharged; only `hconv`
  (gap #2 Girsanov) + the `SBData.Path := C([0,1],X)` re-typing (roadmap step 3) remain.
- When a `reference/` result is validated and promoted, update `reference/README.md`.

> **2026-07-08 module-layout note (GPT-5.5 Thinking).** Public aggregate imports remain stable,
> but the theorem libraries are split further. `ForMathlib.MeasureTheory.GaussianCameronMartin`
> is now an aggregate over `Basic`, `Energy`, `FiniteKL`, `InfiniteKL`, `Density`, and
> `AbsoluteContinuity`. `ChenGeorgiouPavon2021.Continuum.WienerDyadic` is an aggregate over
> `Continuum.Wiener.*`; `Continuum.Closure` is split into Sobolev, KL-exhaustion,
> quasi-invariance, and assembly modules; `SocOt` is split into dynamic, static, entropic-OT,
> and Sinkhorn wrappers. Downstream code may keep importing the aggregate modules.
>
> **Progress-bar policy.** Future placeholders should live only on the mathematical theorem targets
> needed to discharge final DRSB assumptions. Do not add placeholders to downstream integration/assembly
> lemmas that merely consume those targets; those should be wired only after the target theorems are
> proved or stated as explicit hypotheses/interfaces.

- **Done:** repo scaffolded; `ForMathlib` + 5 paper libraries + `Drsb` capstone all
  `lake build` green; prose transcriptions + PDFs in place; `formalization.yaml` maps
  every declaration to its source.
- **Proofs landed (proof pass, foundational-first):**
  - `ForMathlib.MeasureTheory.DonskerVaradhan` — the full DV family (dependency-clean).
  - `ForMathlib.MeasureTheory.Normalization.isProbabilityMeasure_inv_univ_smul` —
    normalize a finite nonzero measure to a probability measure (new; the first
    pipeline extraction — a genuine Mathlib gap, consumed by `exists_worstCase_gibbs`).
  - `WangGaoXie2023.logPartition_eq_gibbs_sSup` (DV applied to the tilted reward),
    `worstCase_conditional_tilted` (density rewrite), and
    `exists_worstCase_gibbs` (Remark 4: normalize the unnormalized Gibbs measure → a
    probability measure ∝ the tilt; now via the ForMathlib lemma).
  - `ChenGeorgiouPavon2021.staticSB_eq_entropicOT` (T0: the `hgibbs` rewrite — when the
    endpoint law IS the entropic-OT reference, the two `sInf`s coincide).
  - `BlanchetMurthy2019.wdro_strong_duality_dualFn` — the `Lc`-form of
    `wdro_strong_duality`, derived from it by defeq. Not an independent strong-duality
    proof; the debt stays in one place.
  - `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost` — the OT-DRO
    per-coupling **weak-duality kernel** (ported from `reference/V4.lean`, generalized to
    arbitrary cost `c`); dependency-clean.
  - ⭐ **BOTH DRSB evaluation-card claims PROVED, dependency-clean** — the project's headline
    result `𝔼_perturbed[V] ≤ 𝔼_worst-case[V]` for both balls:
    - `Drsb.wdrsb_cost_bound` (Wasserstein): weak-duality kernel + `sqCost` symmetry, under
      regularity + the OT-attainment edge `hOT`.
    - `Drsb.sdrsb_cost_bound` (Sinkhorn): composes the proved
      `WangGaoXie2023.sinkhorn_weak_duality_kernel` (per-point Gibbs/DV bound integrated
      over `p₀`) with `budget ≤ ε`, under `hκ>0` + the Sinkhorn attainment+disintegration
      edge `hSink`; dual restricted to `0<lam` (the `lam=0` `logPartition` is junk — a
      third statement issue found this pass; ess-sup convention unencoded).
    The cards need only the `≤` direction; the strong-duality `≥` seams are now discharged
    too (below), each modulo one explicit attainment hypothesis rather than a placeholder.
  - **General duality + the "strong = weak + attainment" pattern** (dependency-clean):
    `GaoKleywegt2023.weak_duality_prop1` (general Wasserstein `v_P ≤ v_D`, via the kernel +
    coupling ε-approx + the unconditional `Real.sSup_neg` for `Φ`↔sup-form) and
    `GaoKleywegt2023.strong_duality_thm1` = `le_antisymm(weak, attainment)` — the `≥` is a
    single explicit **attainment edge**, isolating the whole strong-duality gap to that one
    OT measurable-selection fact. `Drsb.wdrsb_strong_duality` delegates to it (`sqCost`
    symmetric ⇒ `Lc = −Φ`), completing the **WDRSB capstone** (cost bound + strong duality).
  - **Both weak-duality kernels are staged in `ForMathlib.OT`** (paper-agnostic,
    upstreamable): `expect_le_dualIntegrand_add_lam_couplingCost` (Wasserstein) and
    `expect_kernel_le_lam_sinkhornBudget_add_logPartition` (entropic/Sinkhorn) — the two
    "from-scratch" Mathlib gaps the cards descend from.
  - **Atop-a-placeholder reductions** (concentrate debt, not dependency-clean):
    `ChenGeorgiouPavon2021.schrodingerBridge_KL_eq_SOC` (sInf-translation atop
    `energy_identity`) and `optimal_control_eq_neg_grad_value` (atop
    `optimal_control_eq_grad_log` + a `grad`-negation edge).
  - **ALL strong-duality *equalities* proved** (2026-07), each `le_antisymm(weak,
    attainment)` with the `≥` isolated to one explicit OT-attainment hypothesis:
    `BlanchetMurthy2019.wdro_strong_duality` (primary Wasserstein), `WangGaoXie2023.strong_duality`
    (Sinkhorn Theorem 1(II)), and the two **`Drsb` capstones** `wdrsb_strong_duality` /
    `sdrsb_strong_duality` — **`Drsb` is now proved** (all four card+duality results land).
  - `WangGaoXie2023.primal_feasible_radius_nonneg` (was the mis-stated `primal_feasible_iff`)
    — the honest necessity half of Theorem 1(I), `0 ≤ κ ⇒ (Nonempty → 0 ≤ ε)`, dependency-clean
    (see §6). Sufficiency is the deferred ρ̄-ball attainment edge.
- **Finite Sinkhorn scaling — ✅ PROVED, dependency-clean (2026-07):**
  `ForMathlib.matrix_scaling_exists` + `ForMathlib.sinkhorn_potentials_exist`
  (`ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean`). Mathlib has **neither** Brouwer
  nor the Birkhoff/Hilbert-metric contraction (grep-verified), so the proof is a **log-domain
  convex minimization** of `ψ(b)=∑ᵢ pᵢ log(∑ⱼ Gᵢⱼ bⱼ) − ∑ⱼ qⱼ log bⱼ` over the open simplex:
  boundary blow-up `−qⱼ log bⱼ→+∞` confines the sublevel set to an explicit compact set
  (extreme value theorem — no coercivity lemma), and the marginal equations fall out of the
  1-D directional derivatives along `eⱼ−eₖ` (`IsLocalMin.hasDerivAt_eq_zero`), with **mass
  conservation `∑p=∑q` exactly killing the Lagrange multiplier**. `ChenGeorgiouPavon2021.
  sinkhorn_potentials_exist` now delegates to a proved proof. `matrix_scaling_exists`
  is a clean general lemma staged for Mathlib upstreaming (Sinkhorn scaling is a genuine gap).
- **Vendored external proof + discrete energy identity — ✅ landed (2026-07):** vendored
  `mrdouglasny/gibbs-variational`'s `GaussianEntropy.lean` (Apache-2.0, commit `75e08d8`) →
  `ForMathlib/MeasureTheory/GaussianEntropy.lean` (Cameron–Martin `KL(N(·+h)‖N)=½‖h‖²`;
  attribution in file header + README + `formalization.yaml` + `SURVEY_LEADS.md`). Built on
  it, the **proved, dependency-clean** Euler–Maruyama discrete energy identity
  `ForMathlib…klDiv_emShift_eq_emEnergy` → `ChenGeorgiouPavon2021.energy_identity_euler_maruyama`:
  `(KL(P^u‖P^0)).toReal = ∑ₖ Δt·½‖u_k‖²`, the discrete/Gaussian layer of `energy_identity`
  (4.19) — the quantity the card measures (§3). The continuous `energy_identity` stays a bare
  placeholder (count unchanged at 12); the single remaining edge is the Δt→0 SDE limit
  (PROOF_PIPELINE §2).
- **Worst-case structure — ✅ BOTH GaoKleywegt corollaries PROVED, dependency-clean (2026-07);
  `GaoKleywegt2023` is now proved:**
  - `dataDriven_worstCase_cor2ii` (Cor 2(ii), eq. 29 — the `≤ N+1`-atom empirical worst case):
    `μ*` built as the explicit `K = 2` weighted-Dirac double-sum; probability measure,
    `∈ ambiguitySet` (explicit transport plan + `ForMathlib.OT.otCost_le_couplingCost`),
    closed-form `Ψ`-expectation and the eq. (29) split-form identity all **proved**. Local
    copies of `isProbabilityMeasure_wsum`/`integral_wsum`/`map_wsum` (→ ForMathlib dedup TODO).
  - `worstCase_structure_cor1` (Cor 1(ii), eq. 27 — the general-`ν` 2-map transport
    `μ* = pstar·T̄#ν + (1−pstar)·T*#ν`): same house pattern via `Measure.map` pushforwards +
    `integral_map` (with **regularity edges** since `c`/`Ψ` carry no standing measurability);
    2nd marginal `= ν` because `snd∘(T,id)=id`; eq. (27) measure form is `rfl`.

  Both are §5-safe: the structured optimizer is **not** hypothesized — only genuinely-weaker
  ingredient edges are (mixture weight, measurable a.e.-argmin maps/atoms, feasibility budget,
  and one `≥` attainment edge — the `le_antisymm(constructive, one edge)` posture shared with
  `MohajerinEsfahaniKuhn2018.worstCase_exists`).
- **Data-driven duality equality — ✅ PROVED, dependency-clean (2026-07); `MohajerinEsfahaniKuhn2018`
  is now proved:** `worstCaseExpectation_eq_dual` (Thm 4.2). `le_antisymm(weak, attainment)`:
  the weak `≤` is **proved** — `csSup_le → le_csInf → per-(Q,λ)` (η/(λ+1) trick) reducing to the
  **new** `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost_restrict` (the `Ξ`-restricted
  Lagrangian kernel — `integral_mono_ae` since the source marginal is `Ξ`-supported) + the
  empirical collapse + the OT ε-approx edge; the `≥`/attainment isolated to one edge.
  **⚠ STATEMENT CORRECTION:** the ball is now `wass1BallΞ` (`P(Ξ)`-restricted). The `ℝ`-valued
  (total) `ℓk` encoding drops the paper's `+∞`-off-`Ξ` / `P(Ξ)` restriction, so the raw
  `wass1Ball` equality is *unsound* for `Ξ ≠ univ` (an escaping `Q` beats the `Ξ`-dual);
  restricting the ball to `P(Ξ)` restores it — same fidelity-correction class as the Sinkhorn
  external-`ν` fix / `primal_feasible_radius_nonneg` (§6). `[BorelSpace X]` added for
  `IsClosed Ξ ⇒ MeasurableSet Ξ`.
- **First crack in the SDE frontier — ✅ `dynamic_eq_static_SB` PROVED (one direction),
  dependency-clean (2026-07); via a NEW KL data-processing inequality.** The Léonard dynamic⇄static
  SB equivalence: `le_antisymm(gluing-edge, DPI-direction)`. `staticSBValue ≤ schrodingerBridgeValueKL`
  is **genuinely proved** — the endpoint projection `e = (ω↦(ω₀,ω₁))` sends a feasible path law to
  a coupling in `Π(ρ₀,ρ₁)`, and coarse-graining can't increase KL, so `klReal(e#P‖endpointLaw) ≤
  klReal(P‖R)`. That inequality is the **new `ForMathlib.MeasureTheory.toReal_klDiv_map_le`** — the
  KL **data-processing inequality**, a *genuine Mathlib gap* (Mathlib has the KL chain rule but no
  DPI / f-divergence file), proved by conditional Jensen on the convex `klFun` (`ConvexOn.map_condExp_le`)
  + `toReal_rnDeriv_map` (pushforward RN-derivative = conditional expectation). Honest edges `hac`
  (`P ≪ R`), `hfin` (finite KL), `hne`; the gluing (path-reconstruction) `≤` isolated to `hglue`.
- **Soundness audit + fix (2026-07 — see [`JOURNAL.md`](JOURNAL.md)):** the four **under-specified**
  statements — `optimal_control_eq_grad_log` / `_sigma_grad_log` / `_grad_value` (HJB) and
  `optimal_coupling_factorization` — were **false as stated** (they equate `u*`/`dens*` to a *free*
  operator/function argument with no linking hypothesis; `grad := 0` refutes them). Worse,
  `optimal_control_eq_neg_grad_value` was **green but false** — it compiled only by `rw`ing through
  the false `grad_log` (Lean dependency audit carried `unsound dependency marker`): a genuine hidden `if False then True`.
  All four are now **reformulated to TRUE statements** and are **dependency-clean**: the real SDE/OT
  content (Hopf–Cole / product-form **verification** — the candidate is optimal — + optimizer
  **uniqueness**) is isolated to explicit non-vacuous edges (`hHC`/`hprodopt`, `huniq`), and the
  identity is *derived* (the `isolate-content-to-an-edge` posture used everywhere here). Blast
  radius was contained: `Drsb` uses `V` abstractly, so no card claim was ever affected.
- **`ChenGeorgiouPavon2021.energy_identity` is CLOSED** (Session 3): reshaped via the roadmap
  disintegration + KL chain rule, with the Girsanov content isolated to the explicit `hCM` edge
  (whose discrete Euler–Maruyama instance `energy_identity_euler_maruyama` is proved). The
  Session-9 theorem-target scaffold has likewise been converted from executable placeholders into
  hypothesis/structure **interfaces** (`EnergyIdentityTargets.lean` &c. carry **zero** open goals).

---