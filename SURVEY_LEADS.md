# SURVEY_LEADS.md — external Lean/proof leads to mine & re-check

A dated registry of external artifacts (repos, Mathlib PRs, generated-proof corpora,
Zulip threads, papers) that may supply proofs for the DRSB foundational chains
([`FOUNDATIONS.md`](FOUNDATIONS.md)). Kept so we can **follow up and re-check for updates
later** — many of these are moving targets (open PRs, active repos).

**Last swept: 2026-07-10** (targeted re-survey for the **projective-metric frontier** —
Hilbert projective metric / Birkhoff–Hopf contraction / Perron–Frobenius / Sinkhorn convergence;
see [§ Projective-metric frontier](#projective-metric-frontier-birkhoffhopf--hilbert-metric--pf--sinkhorn-re-survey-2026-07-10).
Prior: 2026-07-04 (three continuum energy-identity gaps —
see [§ Continuum energy-identity: the three named gaps](#continuum-energy-identity-the-three-named-gaps-re-survey-2026-07-04) — plus `rjwalters/lean-genius`); full
sweep 2026-07-03. Provenance uneven; corpus-mining frontier still open, below).

> ## ⚖️ Vendoring & attribution policy (READ before pulling in ANY external proof)
> Nothing here is vendored yet. When we DO adapt/copy an external proof, provenance is
> mandatory — verified truth does not waive credit or licensing:
> 1. **License first.** Confirm the source license permits reuse and is compatible with
>    ours (Apache-2.0). Mathlib is Apache-2.0; other repos vary (check, don't assume).
>    Record the license in the vendored file and in this registry row.
> 2. **Credit the original author** in the file header — name/handle, repo URL, and the
>    **source commit hash** (a permalink), plus "adapted by …" if we modified it. Mirror
>    the DKPS `ForMathlib` header convention ("Formalized by … ; golfed by …").
> 3. **Keep upstream license/notices** (e.g. bundle their `LICENSE`, keep copyright
>    headers) when copying verbatim; mark derivative works as such.
> 4. **Provenance metadata**: log source repo + commit + license + retrieval date in the
>    file and in `formalization.yaml` (and, for `mathlib-slop`, its per-theorem ledger).
> 5. Prefer **re-deriving from the statement** over copying when the license is unclear —
>    an independently authored proof of the same theorem sidesteps the licensing question
>    (and multiple proofs are welcome anyway).
>
> **Before depending on ANY lead: verify its build status, placeholder inventory, AND license.**
Legend: ⭐ high value · ⚠ low-trust/scaffold · 🔁 moving target (re-check).
Where only a project name is given (no org), find via GitHub **code search** on the
distinctive filename; URLs are recorded when the source gave an exact org/repo.

---

## Use-now / highest value

| Lead | Link | Chain | Note |
|---|---|---|---|
| ⭐ **Mathlib `Topology.Sion`** | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sion.html | 1 | Sion minimax (`minimax'`, `exists_isSaddlePointOn`). **Use directly.** |
| ⭐ **`gpeyre/flow-sinkhorn`** 🔁 ✅AUDITED 2026-07-03 | https://github.com/gpeyre/flow-sinkhorn | 3, 1-heavy | **AUDITED (do this before re-proving any entropic-OT/Sinkhorn lemma):** MIT license (Apache-compatible, reusable); ~43.5k lines, **~1605 lemmas, `Comparator/Solution.lean` is PROVED** (the only 28 placeholders are in `Comparator/Challenge.lean`, the challenge *spec* — the `leanprover/comparator` AI-proof harness pattern, so this is very likely AI-assisted proof work). Real proved content: entropic-OT/Sinkhorn fixed points (`prop_hgamma_ot`, `prop_kappa_ot` = c-transform/potential decomposition), finite KL + **Pinsker** (`prop_pinsker_normalized`, `lem_pinsker_nonnormalized`), **LP↔entropic reduction** (`thm_approx_linprog`), KL-dual convergence *rate* (`thm_kl_dual_rate`, `PerStepAscent`, `GapResidual`, `Rate`). **Scope caveat:** all FINITE/discrete (`Fintype`, graphs) — no continuous measurable OT, no stochastic analysis. So it does NOT drop-in-close any current DRSB placeholder (our 6 SDE are Chain-4; our 6 worst-case are continuous-measure OT), BUT it is the raw material for the "reduce worst-case-structure to finite/discrete OT" strategy — most relevant to the **data-driven/empirical** worst-case theorems (`MohajerinEsfahaniKuhn2018.*`, `GaoKleywegt2023` Cor 2), whose nominal IS a finite measure. NB: our `ForMathlib.matrix_scaling_exists` (Sinkhorn existence) was proved in-house 2026-07 *before* this audit — cross-check against `prop_hgamma_ot`/`prop_kappa_ot` before upstreaming. |
| ⭐ **Mathlib PF PR cluster** 🔁 | #39919 (Collatz–Wielandt / Perron root), #39920 (PF for primitive matrices), #39917 (aux) — https://github.com/leanprover-community/mathlib4/pull/39919 etc. | 3 | Mathlib-native; build PF on these so upstream composes. |
| Mathlib PF merged infra | https://github.com/leanprover-community/mathlib4/pull/28728 | 3 | Irreducible+Primitive matrices + Quiver links (merged Jul 2025). |
| Mathlib `cgf`/`mgf` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Basic.html | 2 | log-partition = `ProbabilityTheory.cgf`. Use. |
| ⭐ **`StatLean` / `Stat-Lean`** | GitHub code search: `KLDivergence.lean`, `Entropy.lean`, `PinskerInequality.lean`, `GaussianKLMulti.lean`, `Fano/MutualInformation.lean` | 2 | native KL / entropy / Pinsker / Gaussian-KL / Fano / mutual-info; "for-Mathlib" quality — **first repo to inspect after Mathlib for Chain 2** |
| ⭐ **Mathlib `Measure/Prokhorov`, `Measure/Tight`, `Measure/Portmanteau`** ✅**NEW IN PIN, verified 2026-07-10** | `MeasureTheory.isCompact_closure_of_isTightMeasureSet`, `IsTightMeasureSet`, `Measure/Portmanteau.lean` | 1 | **The compactness half of worst-case-measure *attainment*.** Tight ambiguity ball ⇒ compact closure ⇒ the `sSup` of a usc functional is attained. ⚠ This serves the "a worst-case measure exists" statements (`GaoKleywegt2023.worstCase_structure_cor1`, `MohajerinEsfahaniKuhn2018.worstCase_exists`) — it does **not** reach the strong-duality edge `hge` (zero duality gap), which needs measurable selection. Still missing for attainment: lsc of the transport cost, and lsc of `klDiv` (setwise lsc now proved). |
| ⭐ **Mathlib doubly-stochastic API** | `Analysis/Convex/Birkhoff.lean`, `Analysis/Convex/DoublyStochasticMatrix.lean`, `LinearAlgebra/Matrix/Stochastic.lean` | 3 | native finite-dim stochastic/doubly-stochastic matrix API — **start the Sinkhorn build here**, not from PF (see FOUNDATIONS.md Chain 3) |

## Projective-metric frontier: Birkhoff–Hopf / Hilbert metric / PF / Sinkhorn (re-survey 2026-07-10)

Targeted sweep for what the **current** frontier actually needs (`ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf*`,
`ChenGeorgiouPavon2021/SocOt/Sinkhorn/Convergence/Compactness/FranklinLorenz.lean`). The earlier sweeps
predate this rabbit hole, so nothing here was previously checked through this lens.

**Headline: for the two theorems we actually need, there is NOTHING to vendor or depend on.**
They must be authored in-house — which is what `ForMathlib/…/BirkhoffHopf.lean` is already doing.

| Target | Mathlib (pin `e3b73828`, 2026-07-09) | Anywhere else in Lean | Verdict |
|---|---|---|---|
| **Hilbert projective metric** | ❌ absent | ❌ **nothing exists, in any repo** | author in-house |
| **Birkhoff–Hopf contraction** (`tanh(Δ/4)`) | ❌ absent | ❌ **nothing exists, in any repo** | author in-house |
| Perron–Frobenius eigenvalue theory | ❌ absent (PRs open, unmerged) | ✅ two sorry-free Lean 4 repos | available — **but likely off our critical path** |
| Sinkhorn / matrix scaling convergence | ❌ absent | 🟡 partial, *wrong proof route* | in-house |

### ⚠️ Name-collision traps (every `Birkhoff`/`Hilbert` hit in Mathlib is a DIFFERENT theorem)
Do not let a grep hit fool you — **none** of these is our target:
- `Analysis/Convex/Birkhoff.lean` → Birkhoff–**von Neumann** (doubly-stochastic = convex hull of permutations)
- `Order/Birkhoff.lean` → Birkhoff **representation** (finite distributive lattices)
- `Dynamics/BirkhoffSum/*` → **ergodic** Birkhoff sums/averages
- `Analysis/InnerProductSpace/*`, `l2Space` → **Hilbert space**; `…/Projection.lean` → Hilbert **projection** theorem
- `Analysis/Oscillation.lean` → modulus of continuity, *not* Hilbert-metric oscillation
- `Analysis/Convex/Gauge.lean` → **Minkowski** gauge, unrelated
- "Perron" → Paolo **Perrone** (category theory) and the **Perron integral**; "Frobenius" → Frobenius **norm** / **endomorphism**; "Wielandt" → group-theory Jordan–Wielandt

### What Mathlib *does* have (pin-verified)
- `Matrix.IsIrreducible` / `Matrix.IsPrimitive` + quiver interface — `LinearAlgebra/Matrix/Irreducible/Defs.lean` (PR **#28728**, merged 2025-10-30). **Definitions only**: grep for `spectralRadius`/`Perron`/`eigenvalue` in that dir is empty.
- Generic `ConvexCone` API (`Analysis/Convex/Cone/*`) and order cones. The cone *substrate* exists; no comparability relation, no Hilbert metric, no projective diameter is built on it.

### Mathlib PF PR cluster — still ALL OPEN as of 2026-07-10 🔁
Re-checked; **none merged**, so a pin bump does not help. Do not plan around these landing.

| PR | Content | State |
|---|---|---|
| #39917 | aux matrix/topology lemmas | OPEN (author considering closing; folded into #39919) |
| #39918 | core lemmas for nonnegative matrices | OPEN |
| #39919 | Collatz–Wielandt fn + Perron root bounds | OPEN, **merge conflict** with master |
| #39920 | PF for primitive matrices | OPEN, labeled `blocked-by-other-PR` (on #39919) |

Docs-site `PerronFrobenius/Primitive.html` **404s** — independent confirmation it is not on master.

### External PF sources (sorry-free, permissive) — ready if PF is ever needed
> ⚠️ Per `AGENTS.md`, our finite Sinkhorn existence (`ForMathlib.matrix_scaling_exists`) was proved
> **without** Perron–Frobenius (log-domain convex minimization). PF may not be on the critical path at all.

| Lead | License | Lean/toolchain | Open goals | Content |
|---|---|---|---|---|
| ⭐ `mkaratarakis/HopfieldNet` (`MCMC/PF/…/PerronFrobenius/`) commit `0bbb8999` | **MIT** (repo-level; ⚠ **no per-file copyright headers** — you must add attribution on vendoring) | Lean 4, `v4.27.0-rc1` (older than our pin → expect API drift) | **0** across 9 PF files | Most complete finite-dim PF in Lean: `exists_positive_eigenvector_of_primitive`, `maximizer_is_eigenvector`, `perron_root_pos_of_primitive`, `uniqueness_of_positive_eigenvector`, spectral dominance. **This is the source behind PRs #39919/#39920** — prefer tracking the PRs (lands Apache-2.0 upstream). |
| `mrdouglasny/spectral-positivity` commit `9af3c3a7` | **Apache-2.0** + per-file headers (cleanest provenance) | Lean 4, `v4.30.0` | **0** repo-wide | `perron_frobenius` (their `IsIrreducible` bundles a self-loop ⇒ really *primitivity*), `collatz_wielandt_monotone`, `allpos_has_pos_eigenvec`; bonus infinite-dim `jentzsch_theorem_proved`, `spectral_gap`. Self-contained Apache fallback. |

### `gpeyre/flow-sinkhorn` — re-examined, does NOT help here
MIT, Lean 4, commit `ff053cc1`; 28 open goals all confined to `Comparator/Challenge.lean` (the AI-proof-harness *spec*), `Comparator/Solution.lean` proved.
**Grep for `hilbert|birkhoff|tanh|projective|matrix.scaling|doubly.stochastic` = 0 hits.** Its Sinkhorn convergence goes via **KL-descent + Pinsker**, not the Hilbert metric, and it never states Franklin–Lorenz (1989). Reusable for finite entropic-OT *rates*; supplies **none** of our contraction machinery.

### Honest method caveat
No `gh` CLI / GitHub token in the survey environment, so authenticated **code**-search (`/search/code`) could not be run (401); grep.app/Sourcegraph were rate-limited. The negatives rest on web search + GitHub *repo* search + pinned-Mathlib grep + direct clone inspection, which corroborate each other. **A keyed code-search is the one stone left unturned** — worth one re-check before anyone concludes "definitely nowhere".

---

## Chain 2 — Donsker–Varadhan / KL / Gibbs / PAC-Bayes

> We already have the **full DV equality proved** in `ForMathlib` — these are for KL
> lemmas / Boué–Dupuis / alternate proofs, not the DV equality itself.

| Lead | Link | AI? | Note |
|---|---|---|---|
| DV Zulip thread ⭐ | `leanprover-community/archive` → `On Potentially Formalizing Donsker Varadhan.json` (https://github.com/leanprover-community/archive) | — | first stop for Chain-2 context, blockers, who's working nearby |
| `mrdouglasny/gibbs-variational` ✅**VENDORED** 2026-07-03 (commit `75e08d8`) | https://github.com/mrdouglasny/gibbs-variational | **Apache-2.0** (reusable) | **VENDORED** `GaussianEntropy.lean` → `ForMathlib/MeasureTheory/GaussianEntropy.lean` (verbatim, namespace `GibbsVariational → ForMathlib.MeasureTheory`; commit `75e08d8`, retrieved 2026-07-03, dependency-clean under our pin; attribution in file header + README + `formalization.yaml`). Supplies **`klDiv_stdGaussian_map_add`** (KL of a shifted std Gaussian = ½‖h‖² — the finite Cameron–Martin / Girsanov relative-entropy identity) + `klDiv_gaussianReal_shift`, `klDiv_pi`/`klDiv_prod`, `klDiv_map_measurableEquiv`. **Used** to prove the proved Euler–Maruyama discrete energy identity (`ForMathlib…klDiv_emShift_eq_emEnergy` → `ChenGeorgiouPavon2021.energy_identity_euler_maruyama`), the discrete/Gaussian layer of the Chain-4 `energy_identity` (the Euler–Maruyama relaxation the DRSB card measures). — *Original audit:* 4 files, 1 placeholder total (in `Variational.lean`, not this file); our DV equality supersedes its `Variational.lean`; `BoueDupuis.neg_log_integral_exp_neg_le` still available if needed. |
| `Robby955/FormalSLT` | https://github.com/Robby955/FormalSLT | mixed | PAC-Bayes KL / McAllester / change-of-measure; also `statlean-v0.1.jsonl` (structured theorem map — mine it) |
| `hawkrobe/linglib` | https://github.com/hawkrobe/linglib | mixed | `GibbsVariational.lean`, RSA Gibbs material |
| `the-omega-institute/automath` | https://github.com/the-omega-institute/automath | mixed | `XiReverseKLDVPoissonVariational.lean` (reverse-KL DV) |
| `FujiHaruka/information-theory` | https://github.com/FujiHaruka/information-theory | mixed | KL variational lower / Fatou / inventory docs |
| `szl-holdings/lutar-lean` | https://github.com/szl-holdings/lutar-lean | mixed | `Wave14/LogSumInequality`, `Wave6/SubGaussianKL`, `Wave9/TimeUniformPACBayes`; mirror at `szl-holdings/a11oy` (`lutar-lean__Lutar.lean` — corpus artifact) |
| Quantum relative-entropy repos (lemma-mining only) | `zblore/csd-lean4` (`QuantumInfo/StrongSubadditivity`), `leanprover-community/physlib`, `Timeroot/Lean-QuantumInfo`, `Hayata-Yamasaki-Group/lean-quantum`, `LionSR/TNLean` (`KleinInequality`, `VonNeumann`) | mixed | matrix entropy / trace-log / relative-entropy convexity / data-processing lemmas — mine, not direct deps |
| `bangyen/leansharp` | https://github.com/bangyen/leansharp | mixed | `PacBayesBasis.lean` |
| `mlinegar/ThinkingTrees` ⚠ | https://github.com/mlinegar/ThinkingTrees | — | Lean 3, variational-bound-adjacent; likely stale |

## Chain 1 roots — convex analysis / Fenchel (author ourselves; no direct hit)

| Lead | Link | Note |
|---|---|---|
| AMBER (Construction-Verification) | https://arxiv.org/abs/2602.01291 | applied-math bench: convex analysis, optimization, numerical algebra, high-dim prob — closest terrain for Fenchel scaffolding |
| CAM-Bench | https://arxiv.org/abs/2605.17255 · repo `optpku/CAM-Bench` https://github.com/optpku/CAM-Bench | 1000 applied-math Lean targets (optimization, numerical LA) |
| `iamkarthikbk/edith` ⚠ | https://github.com/iamkarthikbk/edith | `GeometricProgramming.lean`; low-trust, convex/duality-adjacent |
| `hxrts/stat-mech` | https://github.com/hxrts/stat-mech | `StatMech/Hamiltonian/Legendre.lean` — finite-dim Legendre-transform skeleton (best adjacent Fenchel hit) |
| CAM-Bench `problem-100.lean` | repo `optpku/CAM-Bench` https://github.com/optpku/CAM-Bench · https://arxiv.org/abs/2605.17255 | recurs around convex-conjugate / Legendre queries; applied convex-analysis fragments |
| `atlas-lean`, `ReasBook` ⚠ | GitHub code search | flagged in the search map for Chain-1 roots; low-trust, verify |
| Mathlib `label:LLM-generated Analysis Convex Gauge` | (PR search, see recipes below) | Convex/Gauge API terrain — not Fenchel, but adjacent |

## Chain 1-heavy — Kantorovich / Wasserstein / general OT (scaffolds only; defer)

| Lead | Link | Note |
|---|---|---|
| `gpeyre/flow-sinkhorn` (again) | https://github.com/gpeyre/flow-sinkhorn | `Applications/OT`, `AppendixEOT` — entropic-OT duality, the realistic OT angle |
| `lean-eval-leaderboard` ⚠ | GitHub code search: `ProblemMongeKantorovich.lean` | benchmark scaffold, not a mature branch |
| `LeanAide` ⚠ | GitHub code search: `Kantorovich_old_aristotle.lean` (Aristotle-generated) | scaffold |
| `athanor-ai/pythia` ⚠ | https://github.com/athanor-ai/pythia | `OptimalTransport/WassersteinDistanceNonneg.lean` |

> Strategy: **reduce to finite/discrete OT** (LP + Sion) to sidestep general measurable OT.

## Chain 3 — Perron–Frobenius / matrix positivity (beyond the cluster above)

| Lead | Link | Note |
|---|---|---|
| `mrdouglasny/spectral-positivity` ✅**AUDITED 2026-07-10** | https://github.com/mrdouglasny/spectral-positivity · file: https://raw.githubusercontent.com/mrdouglasny/spectral-positivity/main/SpectralPositivity/Matrix/PerronFrobenius.lean | PF, Jentzsch, Collatz–Wielandt eigenvector. **Apache-2.0, per-file headers, 0 open goals, Lean 4 `v4.30.0`.** Ready to vendor if PF is ever needed. See § Projective-metric frontier. |
| `mrdouglasny/pphi2` | https://github.com/mrdouglasny/pphi2 | `TransferMatrix/Positivity.lean` — positivity-transfer lemmas |
| `LionSR/TNLean` | https://github.com/LionSR/TNLean | `TNLean/QPF/Primitive.lean` — "primitive"/transfer-matrix adjacent |
| `selfreferencing/Agentic-Capital-Desktop` ⚠ | https://github.com/selfreferencing/Agentic-Capital-Desktop | `PROMPT_3_PERRON_FROBENIUS_COMPLETE.md`; scaffolded, low trust |
| ⭐ `mkaratarakis/HopfieldNet` ✅**AUDITED 2026-07-10** | https://github.com/mkaratarakis/HopfieldNet · paper https://arxiv.org/abs/2512.07766 | **MIT, 0 open goals across 9 PF files, Lean 4 `v4.27.0-rc1`.** Most complete finite-dim PF in Lean (existence + positivity + uniqueness/simplicity + dominance). **Correction to the earlier note:** it is *not* independent of the Mathlib PR cluster — it **is** the source behind #39919/#39920 (same author). Prefer tracking the PRs. ⚠ No per-file copyright headers. See § Projective-metric frontier. |

## Chain 4 — stochastic analysis (defer; radar only)

| Lead | Link | Note |
|---|---|---|
| ⭐ `RemyDegenne/brownian-motion` 🔁 ✅RE-AUDITED 2026-07-04 | https://github.com/RemyDegenne/brownian-motion | **Apache-2.0**. **RE-AUDIT (2026-07-04, for continuum gap #1):** README confirms it **constructs the projective family of Gaussians AND its projective limit via the Kolmogorov extension theorem**, giving a **full Brownian measure on `ℝ≥0`-indexed path space** — the exact piece the pinned Mathlib lacks (Mathlib's `Probability.BrownianMotion.GaussianProjectiveFamily` proves the family consistent but says the extension "is not in Mathlib yet"). Results are **"now migrating to Mathlib"** — so **gap #1 (Kolmogorov extension → continuum reference measure) is a *vendor / wait-for-upstream*, NOT a from-scratch port.** Itô "in progress" (building toward Itô's lemma); still **NO Girsanov, no KL** (gap #2 remains open). **Re-check before Phase-2 continuum work.** (We upgraded our pin to latest master `d3716e6d` on 2026-07-04 — the extension is **still not landed** there; keep watching.) |
| ⭐ `raphaelrrcoelho/formal-mathfin` 🔁 ✅AUDITED 2026-07-03 | https://github.com/raphaelrrcoelho/formal-mathfin | **Apache-2.0** (reusable) · **AUDITED (survey note was badly stale — it is NOT immature):** 227 files, ~45k lines, **build-enforced dependency-clean** (`DependencyAudit.lean` `#guard_msgs`; the only real placeholder is one càdlàg-modification lemma). **Substantial Itô development** (`ItoIntegralProcess*`, `ItoFormula*`, `ItoProcessQV`, isometry lemmas — note `ito_isometry_discrete*` are the *discrete* isometries), **`SDEExistence.lean`** (Picard–Banach existence/uniqueness — but **scalar 1-D**), `FeynmanKacHeatEquation.lean`, `ChangeOfMeasure`/`MarkovPathMeasure`, and `ConvexDuality`/`SuperhedgingDuality`/`ConvexSeparation`. ⚠ **RE-AUDIT 2026-07-10: it does NOT contain the Girsanov theorem.** `Foundations/Girsanov.lean` has exactly one theorem, `bs_discounted_isQMartingale` (Black–Scholes-specific); `GaussianGirsanov.lean` is a finite-dimensional Gaussian Esscher tilt; `Binomial/Girsanov.lean` is the discrete binomial analogue. **Do not plan a "port the Girsanov" task against this repo — there is nothing to port.** Verify the Itô layer's generality yourself before planning against it too. **Scope caveat:** 1-D / finance-flavoured, and **no relative-entropy/KL** (grep-empty) — so it does NOT drop-in-close our multi-D Schrödinger-bridge controls (`energy_identity` needs KL between path measures). But it is the **real Itô/SDE foundation** to refound `ChenGeorgiouPavon2021`'s abstract `SBData` on, and `ConvexDuality` may feed Chain-1. Likely AI-assisted (45k lines, fast cadence). |
| Brownian motion in Lean (paper) | https://arxiv.org/abs/2511.20118 | construction of Brownian motion |
| Verified math-finance library (paper) | https://arxiv.org/abs/2606.01356 | L2 Itô integral, risk-neutral pricing measure |

## The strong-duality capstone: `hge` (survey 2026-07-10, **corrected**)

The last edge on all four strong-duality capstones is **`hge : dualValue ≤ primalValue`** — the
duality gap is zero. It replaced `hattain` ("some feasible `μ` attains the dual value"), which
bundled the gap with attainment; the proofs only used the gap. `hbddP` is gone too.

⚠ **Correction to an earlier entry in this file.** `hge` is *not* reachable by tightness +
Prokhorov. That route yields *attainment of the supremum*, which `hge` no longer needs. `hge` is
Blanchet–Murthy Thm 1 / Gao–Kleywegt Thm 1, and its proof selects near-maximizers `x(y)` of the
`c`-transform `sup_x (f x − λ* c(x,y))` and pushes the nominal forward — i.e. it needs
**Kuratowski–Ryll-Nardzewski measurable selection**, `ABSENT` from Mathlib (FOUNDATIONS Chain 1).

| Gap | Needed for | Lean status | Source |
|---|---|---|---|
| ~~measurable selection (KRN)~~ | `hge` ingredient (1) | ✅ **SIDESTEPPED, 2026-07-10.** KRN is not needed: for a *continuous* integrand on a *separable* domain the supremum is achieved to within `ε` on a countable dense set, and `Nat.find` on an enumeration gives a measurable ε-argmax. `ForMathlib.MeasureTheory.exists_measurable_eps_argmax{,_of_separable}` + `ForMathlib.OT.exists_coupling_lagrangian_ge` (the converse Lagrangian bound). Axiom-clean. | Villani Thm 5.10 (`c`-transform); Blanchet–Murthy 2019 Thm 1 |
| ~~optimal multiplier / complementary slackness~~ | `hge` ingredient (2) | ✅ **PROVED 2026-07-10** — `ForMathlib.Analysis.exists_nonneg_multiplier`. Mathlib has `ConcaveOn` + slope lemmas but **no sub/supergradient existence anywhere** (grep-verified); `ForMathlib/Analysis/Supergradient.lean` supplies the 1-D case and is upstreamable as-is. | Blanchet–Murthy 2019 Thm 1; Gao–Kleywegt 2023 Thm 1 / Prop 2 |
| **concavity of the DRO value function** | `hge` ingredient (3) — **the only thing still missing** | **ABSENT (ours to write).** `h t = sup{𝔼_μ[f] : ∃π, 𝔼_π[c] ≤ t}` is concave because `a·π₁+(1−a)·π₂` couples `a·μ₁+(1−a)·μ₂` with `ν`, and cost/reward are affine in the coupling. Plus Slater (`0<δ`) for finiteness near `δ`, and continuity of a concave function on the interior. Measure-theoretic bookkeeping, not new analysis. | — |
| **(A) lsc of the transport cost / `otCost`** | attainment (worst-case-measure existence), *not* `hge` | **ABSENT** | Villani, *OT Old and New*, Thm 4.1; Santambrogio §1.2 |
| **convexity of `klDiv` in its first argument** | the *entropic* value function's concavity (Sinkhorn `hge` ingredient 3) | ✅ **PROVED 2026-07-10** — `ForMathlib.MeasureTheory.toReal_klDiv_mix_le`. Mathlib has `klDiv` + `toReal_klDiv_smul_left/right` but **no convexity** (grep-verified). Two-line corollary of the DV *dual* formula: `KL(·‖ν)` is a sup of affine functionals. Upstreamable. | Dupuis–Ellis; Csiszár |
| **(B) lsc of `klDiv`** | attainment on the entropic ball | 🟡 **setwise version PROVED 2026-07-10** (`ForMathlib.MeasureTheory.toReal_klDiv_le_of_tendsto_integral`); weak version needs bounded *continuous* test functions (Lusin upgrade) | Dupuis–Ellis Lemma 1.4.3 |
| **(C) Donsker–Varadhan *dual* variational formula** | the route to (B) | ✅ **CLOSED 2026-07-10** — `toReal_klDiv_eq_sSup_dvDualSet`, axiom-clean. Not the Gibbs formula (`isGreatest_donskerVaradhan`, sup over *measures*, attained); this sups over *functions* and is not attained. | Dupuis–Ellis Prop 1.4.2 |

⚠ The trap in (C), and what its proof is built around: Lean's `llr μ ν x = log (dμ/dν x)` with
`Real.log 0 = 0`, so `exp (llr μ ν) = 1` — *not* `0` — on `{dμ/dν = 0}`. `truncLLR` puts `-n`, not
`0`, on that (μ-null) set; the partition functions then converge to exactly `1`.

## Continuum energy-identity: the three named gaps (re-survey 2026-07-04)

Proving the DRSB continuum energy identity `D(P^{u,ρ₀}‖R) = D(ρ₀‖ρ₀^W) + 𝔼[∫₀¹ ½‖u‖²]` (CGP 4.19)
past its Euler–Maruyama instance is now walled by **three sharply-named, disjoint missing Mathlib
pieces** (everything around them — discrete Cameron–Martin, KL DPI, the projection-exhaustion
martingale theorem `ForMathlib.klDiv_map_tendsto`, and the Riemann-quadrature limit
`ForMathlib.tendsto_emEnergy_sampled` — is proved & dependency-clean). Were these anticipated at survey
time? Two of three; here is the mapping so we don't re-derive the wall each session:

| Gap | Needed for | Anticipated 2026-07-03? | Status after re-survey | Lead / action |
|---|---|---|---|---|
| **(1) Kolmogorov extension** ✅ **VENDORED + DONE 2026-07-04** — `ForMathlib/KolmogorovExtension/` (3 files, Apache-2.0, attributed, dependency-clean) + `ForMathlib.MeasureTheory.wienerMeasure` (the continuum reference `R` on `ℝ≥0→ℝ`, `IsProbabilityMeasure`, projective-limit property). Gap closed in-project. | the continuum reference path measure on `ℝ→X` | Partially (on radar via `brownian-motion`, but not called out as the reference-measure blocker) | **SOLVED in a standalone Apache-2.0 package** — `RemyDegenne/kolmogorov_extension4` provides `projectiveLimit` + `isProjectiveLimit_projectiveLimit` for Polish/standard-Borel index spaces (source-verified 2026-07-04). It is **~2 local files** (`KolmogorovExtension.lean` + `RegularContent.lean`) building on Mathlib's own `MeasureTheory.Constructions.ProjectiveFamilyContent` (already in our pin). `brownian-motion`'s `Gaussian/ProjectiveLimit.lean` shows the assembly: `gaussianLimit := projectiveLimit gaussianProjectiveFamily _`. | **VENDOR `kolmogorov_extension4` (2 files, fix v4.31→v4.32 API drift) + apply `projectiveLimit` to Mathlib's `BrownianReal.projectiveFamily` (already in-pin, proven consistent) ⇒ the continuum reference `R` in a few lines.** NOT multi-session. (Can't just `require` it: it pins Lean v4.31.0, we're on v4.32.0-rc1 → Mathlib-rev conflict; vendor instead.) |
| **(2) Itô / Girsanov stack** | the feedback-drift path-measure density `dP^u/dR` (a stochastic exponential) | **Yes** — audited `formal-mathfin` (1-D/finance Girsanov, no KL) + `brownian-motion` (Itô in progress) | Still open (both sources 1-D and/or KL-free) | Port `formal-mathfin` Itô/SDE → multi-D + add KL; the genuine multi-session project. |
| **(3) Infinite-product absolute continuity (Kakutani dichotomy)** | any *concrete* infinite-dimensional instance (`∏ N(cₙ,1) ≪ ∏ N(0,1)` iff `∑cₙ²<∞`) | **No** — new; only surfaced when we tried the `infinitePiNat` concrete route this session | Open; **no known Lean source** (pin has only Riesz–Markov–Kakutani, unrelated) | Add to query terms; author ourselves or find a Hellinger-integral / Kakutani-dichotomy lead. |

**"We can always upgrade the Mathlib pin" — does it close any gap? (UPGRADED 2026-07-04).**
Done — bumped the pin `476fb97b62` (2026-06-11) → latest master `d3716e6d` (Lean `v4.31.0-rc2` →
`v4.32.0-rc1`); clean build (8662 jobs), all headline theorems still dependency-clean. **The upgrade
closes none of the three gaps yet** (re-checked against the new pin):
- **Gap #1** — master's `Probability/BrownianMotion/GaussianProjectiveFamily.lean` *still* says Kolmogorov
  extension "is not in Mathlib yet"; `MeasureTheory/Constructions/` has only the `IsProjectiveLimit`
  predicate (`Projective.lean`) + the premeasure content (`ProjectiveFamilyContent.lean`) + **the newly
  present `ClosedCompactCylinders.lean`** — the *tightness/compactness ingredient* for the extension. So
  it is **actively being assembled upstream but not landed.** Action: **watch master and bump the pin the
  moment the extension theorem lands** (cheapest path); if we need it sooner, vendor from
  `RemyDegenne/brownian-motion` (Apache-2.0, already has it). This is the gap most likely to close by
  upgrade in the near term.
- **Gap #2 (Itô/Girsanov)** — `Mathlib/Probability` on master has **no** Girsanov / stochastic-integral /
  Itô file. Upgrade won't help; still the multi-session port.
- **Gap #3 (Kakutani)** — not on master (no Hellinger / infinite-product-ac declaration). Upgrade won't help.

So the standing posture: **re-check master + upgrade opportunistically at Phase-2 start (gap #1 first),
and vendor from `brownian-motion` only if upstream lags.** Bumping the pin also risks breaking our proved
`ForMathlib` layer, so do it deliberately (rebuild + Lean dependency audit re-verify), not reflexively.

### `rjwalters/lean-genius` — surveyed 2026-07-04 (NEGATIVE for our chains; collaboration lead)
| Lead | Link | Note |
|---|---|---|
| `rjwalters/lean-genius` 🔁 ✅SURVEYED 2026-07-04 | https://github.com/rjwalters/lean-genius | **Research *platform* (open-problem attack surface: Erdős, irrationality, fixed-point, Yang–Mills), not a probability library.** 5,679 `.lean` files. **License: mostly per-file Apache-2.0** (headers "Copyright (c) 2026 Lean Genius / RJ Walters … Released under Apache 2.0"; some ported-from-DeepMind-AlphaProof with their own attribution) — **but NO top-level `LICENSE` file** (several headers say "as described in the file LICENSE", which is absent → flag when collaborating). **NEGATIVE for all three gaps and for every theorem we've proved:** grep-empty on `girsanov`, `ito`, `klDiv`, `condExp`/`martingale`, `gaussian`, `riemann`, `DPI`; `kakutani`→ 152× the *fixed-point* theorem, `kolmogorov`→ SLLN/complexity, `cameron`→ Cameron–*Erdős*, `brownian`→ a local first-passage `BrownianMotion` struct in `BallotProblemOQ02OQ02OQ05.lean` (hitting-time measurability, Karatzas–Shreve). **Only genuine neighbour:** `Proofs/AntitoneIntegralSumComparison.lean` (`integral_sandwich`) — the monotone integral-test sandwich, itself a thin wrapper of Mathlib `AntitoneOn.sum_le_integral`/`integral_le_sum`; cross-referenced from our `ForMathlib…tendsto_equispaced_riemannSum` docstring as related work. **Collaboration:** maintainer **RJ Walters** (`rjwalters`) is a desirable future collaborator on navigable AI-proof webs — no reuse yet, but keep on the radar and attribute if we ever do. |

## Declaration search engines (find hidden supporting lemmas — semantic, not name-match)

| Tool | Link | Use |
|---|---|---|
| LeanExplore | https://arxiv.org/abs/2506.11085 | indexes declarations across many Lean packages; downloadable DB/API |
| LeanSearch v2 | https://arxiv.org/abs/2605.13137 · repo `frenzymath/LeanSearch-v2` (`benchmark/MathlibQR.json`) | global-premise retrieval + benchmark; query for premise groups (stochastic matrices, convexity, KL, Sion, Birkhoff) |
| Moogle / LeanSearch / `loogle` | (web) | quick premise/lemma lookup by type/name |

Use these for the *supporting* lemmas (convexity, stochastic matrices, KL, finite sums,
eigenvalues) rather than the top-level theorems.

## Generated-proof corpora — QUERY THESE (ordinary GitHub search misses them)

The search-strategy shift: mine large generated/searched-proof datasets for the query
terms below, rather than more theorem-name GitHub searches.

| Corpus | Link | What |
|---|---|---|
| Lean-GitHub | https://arxiv.org/abs/2407.17227 | compiled ~all Lean4 GitHub repos (InternLM) |
| Lean-Workbook / InternLM2.5-StepProver | https://arxiv.org/abs/2410.15700 | searched proofs over large Lean problem sets |
| OProofs / OProver | https://arxiv.org/abs/2605.17283 | 1.77M statements, 6.86M verified proofs, agentic trajectories (incl. failures/repairs) |
| LeanNavigator | https://arxiv.org/abs/2503.04772 | 4.7M generated theorems/proofs via state-transition graphs over Mathlib4 |
| AXLE / Dependency Math | https://arxiv.org/abs/2606.26442 · https://prover.dependencyatic-ai.com/ · Putnam2025 https://reservoir.lean-lang.org/@DependencyMath/Putnam2025 | proof extraction/verify/repair infra + generated artifacts |
| Goedel-Prover / V2 | https://arxiv.org/abs/2502.07640 · https://arxiv.org/abs/2508.03613 | 29.7K generated Lean-Workbook proofs; released models/code/data |
| Leanabell-Prover-V2 | https://arxiv.org/abs/2507.08649 | verifier-integrated repair trajectories; released data/models |
| DeepSeek-Prover-V2 | https://arxiv.org/abs/2504.21801 | recursive subgoal decomposition; ProverBench |
| LeanMarathon | https://arxiv.org/abs/2606.05400 | long-horizon Lean projects (blueprint/DAG); agent-produced structure |
| Lean Refactor | https://arxiv.org/abs/2605.20244 | refactor patterns / proof-strategy DB for cleaning generated attempts |

> These agent-prover mines rarely hold our exact theorems but often hold **nearby
> generated lemmas** (convexity, KL, finite sums, matrices) worth repurposing.

**Priority query terms** (for corpora AND `label:LLM-generated` PR search):
```
Donsker Varadhan · Gibbs variational · KL variational · PAC Bayes
Fenchel · Legendre · convex conjugate
Kantorovich · Wasserstein · optimal transport · coupling · cTransform · Lipschitz
Sinkhorn · KLProjection · matrix scaling
Perron Frobenius · Collatz Wielandt · primitive matrix
Feynman Kac · Girsanov · Ito
Kolmogorov extension · projective limit · IsProjectiveLimit · cylinder measure
Kakutani dichotomy · infinite product measure · mutual singularity · Hellinger integral · equivalence of Gaussian measures
```

## Mathlib PR search recipes (what actually worked)

- **`label:LLM-generated` × AREA, not theorem name.** Exact theorem-term searches were
  mostly empty; area clusters productive: `label:LLM-generated LinearAlgebra Matrix`
  (→ `Matrix/Nondegenerate`, …), `label:LLM-generated Analysis Convex Gauge`,
  `label:LLM-generated Analysis` (→ RKHS/spectral).
- **Prover-name searches** beyond the label: `Seed Prover`, `lean-eval`, `Aristotle`,
  `Harmonic` (e.g. a symplectic-determinant PR credited to Seed Prover / lean-eval).
- **"Agent golf" index PRs** map LLM-touched areas (not theorem sources): #37968,
  #38104 (MeasureTheory), #38144 (NumberTheory); query "Extracted from #37968".
- **Zulip `AI-authored-projects`** channel — closed/generated-PR discovery surface
  (also the `AI-assisted MDS and spectral PRs` topic).

## Exhaustion status & the next frontier (as of 2026-07-03)

**Manual discovery (web / GitHub / Zulip / registry) is ~saturated** — diminishing returns
after several passes. **The remaining frontier is bulk corpus mining**: scripted exact +
fuzzy search over the generated-proof datasets and declaration indices (above). Only if a
corpus pass over the query terms below also comes up empty is the search *genuinely*
exhausted.

| Surface | Exhausted? | Verdict |
|---|---|---|
| GitHub exact theorem search | yes | diminishing returns |
| Mathlib PR/issue (label/closed) | mostly | maybe one more label pass, low yield |
| Zulip archive | **no** | READ the exact DV & PF threads, don't just locate them |
| Reservoir / package registry | mostly | low yield |
| **Generated-proof corpora** | **no** | the remaining frontier — bulk-query it |
| Chain 3 sources | no | Mathlib doubly-stochastic base + `flow-sinkhorn` still to inspect |
| Chain 2 sources | mostly | `gibbs-variational` AUDITED (Gaussian-KL lemmas reusable); `flow-sinkhorn` AUDITED (finite KL/Pinsker); DV Zulip + `YuanheZ/lean-stat-learning-theory` (ICML2026 SLT, 91⭐) still to skim |
| Chain 4 sources | AUDITED, **claim corrected 2026-07-10** | `formal-mathfin` (⭐ Apache-2.0): has a real Itô development, but **NOT Girsanov** — `Foundations/Girsanov.lean` is the single Black–Scholes statement `bs_discounted_isQMartingale`, and `GaussianGirsanov.lean` is a finite-dimensional Esscher tilt. `brownian-motion` (Apache-2.0): Brownian existence is sorry-free, but its stochastic integral covers only **simple processes** (`DoobMeyer.lean` carries 25 open goals). **Girsanov and the stochastic exponential (Doléans-Dade) are ABSENT from every Lean source surveyed.** Nothing drop-in; nothing shortcuts the port. |
| Chain 1-heavy OT | mostly (manually) | likely absent bar finite/scaffold fragments |
| Chain 4 | enough for now | defer |

**Next concrete move:** download/index `Lean-GitHub`, `Lean-Workbook` searched proofs,
`OProofs` (if accessible), `LeanNavigator`, `LeanSearch-v2` data, `LeanExplore` DB,
`CAM-Bench`, `AMBER` (also `Pythagoras-Prover`/ALF, arXiv 2606.12594); then exact+fuzzy
grep the query-terms block above (Sinkhorn, matrix scaling, doubly stochastic, Birkhoff,
Perron, Collatz, KL, Pinsker, Donsker, Varadhan, Fenchel, Legendre, convex conjugate,
Sion, Kantorovich, Wasserstein, coupling, cTransform, Ito, Girsanov, FeynmanKac).

## Re-check cadence
The 🔁 items (flow-sinkhorn, the PF PR cluster, brownian-motion, formal-mathfin) are
active — re-sweep before starting the corresponding chain, and again at PR-prep time
(Mathlib master moves; a gap may have closed). Update **Last swept** above when you do.


## Sinkhorn `hge` — what is left (2026-07-10)

Ingredient (1), the converse Lagrangian bound, is **proved** and landed
(`ForMathlib/OptimalTransport/SinkhornConverse.lean`). Two concrete gaps remain, both now named:

1. **`klDiv_mix_ne_top`** (Lean gap, no known source). `klDiv (a•μ₁ + b•μ₂) ν ≠ ⊤` from
   `klDiv μᵢ ν ≠ ⊤`. Mathlib has neither this nor the ENNReal-valued convexity
   `klDiv (a•μ₁+b•μ₂) ν ≤ a·klDiv μ₁ ν + b·klDiv μ₂ ν` it would follow from. Route: joint convexity
   of `x ↦ x log x` on the Radon–Nikodym derivatives, or `fDiv` convexity if Mathlib grows it.
   Our `toReal_klDiv_mix_le` is *not* enough — it takes the mixture's finiteness as a hypothesis.

2. **A Slater (strict-feasibility) hypothesis** for the entropic ball. Unlike the Wasserstein cost,
   the Sinkhorn objective `𝔼_γ[c] + κ·KL(γ‖μ̂⊗ν)` has no zero, so `ε` interior to the value
   function's domain means `ε > inf_γ obj(γ)`, strictly. This is a *statement* change, not a proof
   gap: `hge` will be derived from `hslater : ∃ γ, sinkhornObjective c κ μ̂ ν γ < ε` rather than from
   `hfeas`. Literature check still owed: Wang–Gao–Xie's own regularity conditions (prose
   `sinkhorn-dro-duality.md` §3) should be re-read against this, since a paper stating duality under
   mere feasibility would be overclaiming at the boundary.
