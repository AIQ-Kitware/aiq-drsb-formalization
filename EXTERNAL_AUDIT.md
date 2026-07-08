# EXTERNAL_AUDIT.md — what external Lean results exist for the DRSB gaps (verified)

The **verdict layer** for [`SURVEY_LEADS.md`](SURVEY_LEADS.md) (which lists *leads*). This
file records the result of **rigorously auditing** those leads — clone + Lean dependency audit /
placeholder inventory + license check + exact-theorem inspection — plus a systematic GitHub
**repository + code** sweep and the pinned-Mathlib grep. Goal: an honest, reproducible
"what exists / what's absent" map for the remaining placeholders, so nobody re-searches ground
already covered or re-proves something that exists.

**Swept: 2026-07-03/04**, incl. the generated-proof / declaration-index corpora
(Lean-Workbook, LeanSearch, LeanExplore, LeanStateSearch) on 2026-07-04. Method + queries at
the bottom (reproducible). Counts/licenses verified by clone, not by README claim.

---

## TL;DR

There **is** substantial, permissively-licensed, often-AI-assisted Lean work adjacent to
our chains (correcting an earlier over-broad "nothing external" claim). But **none of it
drop-in-closes any of the 8 remaining placeholders** — every usable result is *finite/discrete*
or *1-D/finance*, while our gaps are continuous multi-D stochastic control and
continuous-measure worst-case OT. The specific mathematics our hardest placeholders need
(**HJB / Hopf–Cole, Schrödinger bridge, general Kantorovich duality, measurable
selection, KL between path measures**) has **zero** presence anywhere on GitHub — not in
repo metadata, not in file contents, not in Mathlib. What's reusable is *building blocks*
(finite entropic-OT, Gaussian-KL, an Itô/SDE foundation) that require a bridge, which is
where the parallel vendoring effort is aimed.

The 2026-07-04 sweep of the generated-proof / declaration-index corpora (Lean-Workbook,
LeanSearch, LeanExplore, LeanStateSearch) **re-confirms this under *semantic* search**, not
just lexical: the hard objects surface only false friends, and the Lean-Workbook olympiad
corpus is 0. The sweep's one actionable byproduct is an **already-in-pin, untapped** Mathlib
minimax framework — `Mathlib.Probability.Decision.Risk` (`minimaxRisk`/`bayesRisk`) — flagged
as *candidate* (not proven-fitting) scaffolding for the worst-case-duality `le` direction.

---

## Coverage map — external state vs. the 8 remaining placeholders

| Sorry (remaining) | Math needed | External Lean state | Verdict |
|---|---|---|---|
| `ChenGeorgiouPavon2021.energy_identity` | Girsanov ⇒ **KL between path measures** | `formal-mathfin` has Girsanov (BS-specific) + change-of-measure but **no KL**; `gibbs-variational` has finite Gaussian-KL (Cameron–Martin) | **partial** (Gaussian/EM-discrete only — being vendored) |
| `…optimal_control_eq_grad_log` / `…_sigma_grad_log` | Hopf–Cole log-transform of the value fn | **Absent** everywhere (0 repos, 0 code hits) | **absent** |
| `…optimal_control_eq_grad_value` | HJB / verification theorem | **Absent** (HJB has 0 Lean repos; RL "Bellman" is discrete-MDP only) | **absent** |
| `…dynamic_eq_static_SB` | Schrödinger-problem static⇄dynamic (Léonard) | **Absent** ("Schrödinger" hits are the QM *equation*, not the *bridge*) | **absent** |
| `…optimal_coupling_factorization` | entropic-OT coupling factorization | `flow-sinkhorn` (finite entropic-OT) only | **partial** (finite; needs bridge) |
| `MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` | data-driven Wasserstein-DRO strong duality | `flow-sinkhorn` finite OT + LP↔entropic reduction; Mathlib `Sion` for minimax; **in-pin `Probability.Decision.Risk` minimax weak-duality (untapped, candidate `le` scaffolding)** | **partial** (finite-reduction path exists; bridge) |
| `GaoKleywegt2023.{worstCase_structure_cor1 / dataDriven_worstCase_cor2ii}` | worst-case-measure **construction** / measurable selection | **Absent** (measurable selection = 0 repos; general OT duality = 0); `Decision.Risk` bounds minimax but not the *construction* | **absent** |

---

## Per-repo audit (cloned + verified)

### ⭐ Usable building blocks (permissive license, real proofs)

- **`gpeyre/flow-sinkhorn`** — **MIT** · ~43.5k lines, **~1605 lemmas, `Comparator/Solution.lean`
  PROVED** (the 28 placeholders are all in the `Comparator/Challenge.lean` *spec* — the
  `leanprover/comparator` **AI-proof-harness** pattern; strong signal this is AI-assisted).
  Real content: entropic-OT/Sinkhorn fixed points (`prop_hgamma_ot`), **c-transform /
  potential decomposition** (`prop_kappa_ot`), finite KL + **Pinsker**, **LP↔entropic
  reduction** (`thm_approx_linprog`), KL-dual convergence *rates*. **All finite/discrete
  (`Fintype`, graphs)** — no continuous measurable OT. Use for the *data-driven* worst-case
  placeholders (finite nominal). Cross-check `matrix_scaling_exists` (proved in-house) against it.

- **`raphaelrrcoelho/formal-mathfin`** — **Apache-2.0** · ~45k lines, **build-enforced
  dependency-clean** (`DependencyAudit.lean` `#guard_msgs`; only real placeholder = one càdlàg
  modification). Full continuous stochastic analysis: **Itô integral + Itô formula** (L²
  isometry, local martingales, quadratic variation; scalar + a 2D + a CLM version — **not
  general ℝⁿ**), **`SDEExistence.lean`** (Picard–Banach, **scalar 1-D**),
  **`Girsanov.lean`** (**Black–Scholes-specific** `bs_discounted_isQMartingale`),
  **`FeynmanKacHeatEquation.lean`** (**1-D heat kernel only**), `ConvexDuality` /
  `SuperhedgingDuality` (finite-dim separation / superhedging). **No KL / relative entropy
  anywhere. No HJB / optimal-control PDE.** So it does not close our controls, but it is the
  real Itô/SDE *foundation* to eventually refound `SBData` on. Likely AI-assisted (scale/cadence).

- **`mrdouglasny/gibbs-variational`** — **Apache-2.0** · 4 files, 1 placeholder. Its DV/Gibbs
  variational (`Variational.lean`) is superseded by our in-house DV. **Genuinely useful:**
  `GaussianEntropy.lean` — **`klDiv_stdGaussian_map_add`** (KL of a shifted std Gaussian =
  ½‖h‖², the finite **Cameron–Martin / Girsanov relative-entropy** identity), `klDiv_pi` /
  `klDiv_prod` (KL of products), `klDiv_map_measurableEquiv`. The discrete/Gaussian core of
  `energy_identity`. **Best small vendoring target** (being vendored).

### Foundational / adjacent (not directly usable)

- **`RemyDegenne/brownian-motion`** — **Apache-2.0** · Brownian construction complete
  (Gaussian/Kolmogorov/Chentsov); Itô in progress; **no Girsanov, no SDE-existence**
  (grep-confirmed). Migrating to Mathlib — a future dependency, not usable now.
- **`mrdouglasny/spectral-positivity`** — **Apache-2.0** · Perron–Frobenius / Jentzsch.
  Chain-3 infra we **no longer need** (Sinkhorn scaling proved without PF).

### Checked and rejected

- **`markusdemedeiros/Metrology`** — 47k lines of **approximate/relational (differential-
  privacy) couplings** (`ARCoupling`, `DPCouplings`, `AddCoupl`) — a **false friend**: these
  are coupling-*liftings* for relational program logic / DP, **not OT transport plans** (no
  Wasserstein / Kantorovich / cost). 86 placeholders. **No LICENSE file** (unvendorable). Not usable.
- **`stvsun/neural_atlas_MPMcontact` (`OTContact/BrenierProposed.lean`)** — self-labeled
  "PROPOSED — not machine-checked"; Brenier existence is placeholder-backed, only a toy
  `Int`-quantile identity is proved. Not usable.
- **`luaartist/Yang-Mills-Lean-4-Scaffold-Archive`** — YM mass-gap scaffold; vacuous
  `Prop`-field structures (AGENTS §5 anti-pattern); **NOASSERTION** license. Not usable.
- QM-Schrödinger repos (`PhysLean`/`physlib`), RL/MDP-Bellman (`lean-dojo/TorchLean`,
  `nktkt/gondolin`), Bellman-Ford / shortest-path, and assorted crank ("p-vs-np proofs")
  — all matched keyword searches but are **the wrong "Schrödinger" / "Bellman"** (QM
  equation, discrete MDP, graph algorithm), not our continuous stochastic control.

---

## Decisive absences (repo search **and** authenticated code search = 0)

These areas — where 5 of the 8 placeholders live — have **no Lean presence at all**, anywhere:

- **Hamilton–Jacobi–Bellman / viscosity solutions / continuous stochastic control** — 0.
- **Schrödinger bridge** (the stochastic-control object) — 0.
- **General / continuous Kantorovich–Rubinstein OT duality** — 0 (only finite `flow-sinkhorn`).
- **Measurable selection / Kuratowski–Ryll-Nardzewski** — 0 dedicated repos (Mathlib has
  scattered `measurableSet_of_…`, no worst-case-measure selector).
- **Hopf–Cole**, **Fenchel–Rockafellar duality** — 0.

Consistent with the pinned-Mathlib grep (`476fb97b62`): Kantorovich/Wasserstein/Girsanov
all absent; `condKernel`/disintegration and `Topology.Sion` present.

---

## What this means for the 8 placeholders

- **6 Chain-4 controls:** the specific theory is *absent*, not merely unvendored. Realistic
  paths: (a) the **Gaussian/Euler–Maruyama discrete** relaxation the card actually measures,
  using `gibbs-variational`'s Cameron–Martin KL (energy_identity — in progress); (b)
  otherwise documented `dependency`s with provenance, or a long-horizon Mathlib-SDE build on
  `formal-mathfin` / `brownian-motion`. **Do not expect a vendored close.**
- **2 worst-case-structure:** the **finite/data-driven** ones are the tractable target via
  `flow-sinkhorn`'s finite entropic-OT + LP-reduction + `Mathlib.Topology.Sion` — a real
  bridge, not a drop-in. The **general** worst-case measurable-selection has no external help.

---

## Method (reproducible)

- **Repo search** (GitHub `/search/repositories`, `language:Lean`, unauthenticated): the
  chains' terms — optimal transport, Kantorovich, Wasserstein, Girsanov, stochastic
  integral/differential, Hamilton-Jacobi, stochastic control, measurable selection,
  Schrödinger (bridge), Feynman-Kac, Fenchel, convex conjugate, relative entropy, Donsker-
  Varadhan, distributionally robust, Sinkhorn, Perron-Frobenius. Tool:
  `dev/tools/search_github_prs.py` (repurposed) / inline scripts.
- **Code search** (GitHub `/search/code`, needs auth — run by the maintainer with a personal
  token, results relayed): girsanov, kantorovich, wassersteinDuality, schrodinger,
  "hamilton jacobi", bellman, hopfCole, "feynman kac", viscositySolution, measurableSelection
  (403'd — rerun pending), kuratowski, convexConjugate, fenchelRockafellar, "stochastic
  control", entropicOptimalTransport, boueDupuis, distributionallyRobust. `+language:lean`.
- **Clone audits:** shallow-clone + `grep -c placeholder/admit/dependency` + `theorem/lemma` name grep +
  license file + spot-read of the load-bearing file. Repos above audited at the commits noted
  in `SURVEY_LEADS.md`.
- **LLM-PR pool:** all 414 closed-unmerged `LLM-generated` mathlib PRs swept (see
  `dev/journals/2026-07-03-mathlib-llm-proof-mining-journal.md`) — nothing for our gaps.
- **Corpus / declaration indices** (own web APIs): Lean-Workbook via HuggingFace
  `datasets-server` (`GET /search?dataset=internlm/Lean-Workbook&query=…` — rows inspected,
  not just counted); LeanSearch semantic (`POST leansearch.net/search`,
  `{"query":[term],"num_results":N}`); LeanStateSearch (`premise-search.com/api/search` —
  NL-rejecting, inapplicable); LeanExplore (`leanexplore.com/api/v1/search` — API-key-gated,
  not run). Same term list as above. In-pin presence of any surfaced Mathlib decl verified
  directly in `.lake/packages/mathlib` at `476fb97b62`.

## Generated-proof / declaration-index corpora — MINED 2026-07-04

The one previously un-mined layer, now swept via each service's own web API (not `gh`).
Reproducible calls in the Method section. **Net: no drop-in close, but the semantic sweep
surfaced in-pin Mathlib assets a literal name-grep had missed, and re-confirmed the hard
absences under semantic (not just lexical) matching.**

- **Lean-Workbook** (`internlm/Lean-Workbook`, autoformalized olympiad/textbook corpus, via
  HuggingFace `datasets-server` full-text search): **0 relevant.** All apparent hits are
  word-collision false matches — verified by pulling the rows: "measurable selection" →
  combinatorial *"measure* / *choose"* problems; "distributionally robust" → *"distribut*"*;
  "convex conjugate" → generic convexity / *complex* conjugate. Zero measure-theoretic
  stochastic-control content (expected: it's competition math).
- **LeanSearch** (`leansearch.net`, semantic Mathlib index — `POST /search`,
  `{"query":[…],"num_results":N}`): the **value-add layer.** Semantic matching surfaced real
  Mathlib declarations that the earlier literal grep for *"Girsanov" / "Kantorovich" /
  "Wasserstein"* missed because Mathlib names them differently — and **all are already
  present at our pinned rev `476fb97b62`** (verified in `.lake/packages/mathlib`), so this is
  "already in scope," not "bump the pin":
  - `InformationTheory.klDiv` + the whole **`KullbackLeibler`** namespace (`Basic`, `KLFun`,
    **`ChainRule`** with `klDiv_compProd_eq_add` / `klDiv_compProd_left`) and
    `MeasureTheory.Measure.tilted` (Gibbs/Esscher tilt). **Already heavily used** by the repo
    (142 refs; `ChainRule` is used in `ForMathlib/…/GaussianEntropy.lean`, DV via
    `integral_le_klDiv_add_log_integral_exp`). Not a new lead — confirms the EM-discrete
    `energy_identity` path is built on the right Mathlib infrastructure.
  - **`Mathlib.Probability.Decision.Risk`** (`ProbabilityTheory.minimaxRisk`, `bayesRisk`,
    with `bayesRisk_le_minimaxRisk` and `iSup_bayesRisk_le_minimaxRisk` — the weak-duality
    direction of kernel-based statistical decision theory). **In-pin and 0 repo references —
    the one genuinely untapped asset this sweep found.** Candidate scaffolding for the
    `le`/weak-duality direction of the worst-case-duality placeholders
    (`MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual`,
    `GaoKleywegt2023.*`). **Caveat, not a solution:** `Decision.Risk` is structured over a
    prior/loss/`Kernel` triple, whereas our DRO worst-case is over a Wasserstein/transport
    ball — the mapping is non-obvious and may not fit; flagged for the proof agents to
    evaluate, not asserted to close anything.
- **Hard objects re-confirmed absent under *semantic* search** (strong negative — a concept
  index would surface them under any name if they existed): for *"Hamilton-Jacobi-Bellman",
  "Schrödinger bridge stochastic control", "Kantorovich duality", "Hopf-Cole"*, LeanSearch's
  top hits were all **false friends** — `Decision.Risk`/`HahnBanach` (HJB),
  `Probability.Decision.Risk` (SB), `Topology.MetricSpace.GromovHausdorff` /
  `Analysis.Convex.Cone.Dual` (Kantorovich), `Analysis.Fourier` / `MellinInversion`
  (Hopf-Cole). Consistent with the GitHub + Mathlib-grep zeros.
- **LeanExplore** (`leanexplore.com`, `GET /api/v1/search`) — **not mined: requires an API
  key.** Its only corpus beyond Mathlib (which LeanSearch already covers semantically) is
  **PhysLean**, i.e. QM/physics — the "Schrödinger *equation*," not the stochastic-control
  *bridge*; low marginal value. Left for a keyed rerun if ever needed.
- **LeanStateSearch** (`premise-search.com/api/search`) — **inapplicable:** its `query` must
  be a *Lean proof state*, not a natural-language concept (API rejects NL outright), and it
  indexes Mathlib only. It's a premise-retrieval-given-a-goal tool, not a concept/absence
  probe.

**Corpus-layer verdict:** closed. No generated or indexed corpus contains a usable proof of
any hard gap; the only actionable output is the in-pin, untapped **`Decision.Risk` minimax
scaffolding** (candidate for the worst-case-duality `le` direction) — recorded, not overstated.

## Still open / low-priority

- **`measurableSelection` code search** 403'd mid-run — rerun to confirm the 0 (repo search
  and LeanSearch semantic both already = 0).
- **`YuanheZ/lean-stat-learning-theory`** (ICML2026 SLT, 91⭐) — KL / Le Cam / minimax;
  Chain-2-adjacent (our DV is done), low priority; skim if convenient.
