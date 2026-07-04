# EXTERNAL_AUDIT.md — what external Lean results exist for the DRSB gaps (verified)

The **verdict layer** for [`SURVEY_LEADS.md`](SURVEY_LEADS.md) (which lists *leads*). This
file records the result of **rigorously auditing** those leads — clone + `#print axioms` /
`sorry` inventory + license check + exact-theorem inspection — plus a systematic GitHub
**repository + code** sweep and the pinned-Mathlib grep. Goal: an honest, reproducible
"what exists / what's absent" map for the remaining `sorry`s, so nobody re-searches ground
already covered or re-proves something that exists.

**Swept: 2026-07-03/04.** Method + queries at the bottom (reproducible). Counts/licenses
verified by clone, not by README claim.

---

## TL;DR

There **is** substantial, permissively-licensed, often-AI-assisted Lean work adjacent to
our chains (correcting an earlier over-broad "nothing external" claim). But **none of it
drop-in-closes any of the 8 remaining `sorry`s** — every usable result is *finite/discrete*
or *1-D/finance*, while our gaps are continuous multi-D stochastic control and
continuous-measure worst-case OT. The specific mathematics our hardest sorries need
(**HJB / Hopf–Cole, Schrödinger bridge, general Kantorovich duality, measurable
selection, KL between path measures**) has **zero** presence anywhere on GitHub — not in
repo metadata, not in file contents, not in Mathlib. What's reusable is *building blocks*
(finite entropic-OT, Gaussian-KL, an Itô/SDE foundation) that require a bridge, which is
where the parallel vendoring effort is aimed.

---

## Coverage map — external state vs. the 8 remaining sorries

| Sorry (remaining) | Math needed | External Lean state | Verdict |
|---|---|---|---|
| `ChenGeorgiouPavon2021.energy_identity` | Girsanov ⇒ **KL between path measures** | `formal-mathfin` has Girsanov (BS-specific) + change-of-measure but **no KL**; `gibbs-variational` has finite Gaussian-KL (Cameron–Martin) | **partial** (Gaussian/EM-discrete only — being vendored) |
| `…optimal_control_eq_grad_log` / `…_sigma_grad_log` | Hopf–Cole log-transform of the value fn | **Absent** everywhere (0 repos, 0 code hits) | **absent** |
| `…optimal_control_eq_grad_value` | HJB / verification theorem | **Absent** (HJB has 0 Lean repos; RL "Bellman" is discrete-MDP only) | **absent** |
| `…dynamic_eq_static_SB` | Schrödinger-problem static⇄dynamic (Léonard) | **Absent** ("Schrödinger" hits are the QM *equation*, not the *bridge*) | **absent** |
| `…optimal_coupling_factorization` | entropic-OT coupling factorization | `flow-sinkhorn` (finite entropic-OT) only | **partial** (finite; needs bridge) |
| `MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` | data-driven Wasserstein-DRO strong duality | `flow-sinkhorn` finite OT + LP↔entropic reduction; Mathlib `Sion` for minimax | **partial** (finite-reduction path exists; bridge) |
| `GaoKleywegt2023.{worstCase_structure_cor1 / dataDriven_worstCase_cor2ii}` | worst-case-measure **construction** / measurable selection | **Absent** (measurable selection = 0 repos; general OT duality = 0) | **absent** |

---

## Per-repo audit (cloned + verified)

### ⭐ Usable building blocks (permissive license, real proofs)

- **`gpeyre/flow-sinkhorn`** — **MIT** · ~43.5k lines, **~1605 lemmas, `Comparator/Solution.lean`
  SORRY-FREE** (the 28 `sorry`s are all in the `Comparator/Challenge.lean` *spec* — the
  `leanprover/comparator` **AI-proof-harness** pattern; strong signal this is AI-assisted).
  Real content: entropic-OT/Sinkhorn fixed points (`prop_hgamma_ot`), **c-transform /
  potential decomposition** (`prop_kappa_ot`), finite KL + **Pinsker**, **LP↔entropic
  reduction** (`thm_approx_linprog`), KL-dual convergence *rates*. **All finite/discrete
  (`Fintype`, graphs)** — no continuous measurable OT. Use for the *data-driven* worst-case
  sorries (finite nominal). Cross-check `matrix_scaling_exists` (proved in-house) against it.

- **`raphaelrrcoelho/formal-mathfin`** — **Apache-2.0** · ~45k lines, **build-enforced
  axioms-clean** (`AxiomAudit.lean` `#guard_msgs`; only real `sorry` = one càdlàg
  modification). Full continuous stochastic analysis: **Itô integral + Itô formula** (L²
  isometry, local martingales, quadratic variation; scalar + a 2D + a CLM version — **not
  general ℝⁿ**), **`SDEExistence.lean`** (Picard–Banach, **scalar 1-D**),
  **`Girsanov.lean`** (**Black–Scholes-specific** `bs_discounted_isQMartingale`),
  **`FeynmanKacHeatEquation.lean`** (**1-D heat kernel only**), `ConvexDuality` /
  `SuperhedgingDuality` (finite-dim separation / superhedging). **No KL / relative entropy
  anywhere. No HJB / optimal-control PDE.** So it does not close our controls, but it is the
  real Itô/SDE *foundation* to eventually refound `SBData` on. Likely AI-assisted (scale/cadence).

- **`mrdouglasny/gibbs-variational`** — **Apache-2.0** · 4 files, 1 `sorry`. Its DV/Gibbs
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
  Wasserstein / Kantorovich / cost). 86 `sorry`s. **No LICENSE file** (unvendorable). Not usable.
- **`stvsun/neural_atlas_MPMcontact` (`OTContact/BrenierProposed.lean`)** — self-labeled
  "PROPOSED — not machine-checked"; Brenier existence is `sorry`-backed, only a toy
  `Int`-quantile identity is proved. Not usable.
- **`luaartist/Yang-Mills-Lean-4-Scaffold-Archive`** — YM mass-gap scaffold; vacuous
  `Prop`-field structures (AGENTS §5 anti-pattern); **NOASSERTION** license. Not usable.
- QM-Schrödinger repos (`PhysLean`/`physlib`), RL/MDP-Bellman (`lean-dojo/TorchLean`,
  `nktkt/gondolin`), Bellman-Ford / shortest-path, and assorted crank ("p-vs-np proofs")
  — all matched keyword searches but are **the wrong "Schrödinger" / "Bellman"** (QM
  equation, discrete MDP, graph algorithm), not our continuous stochastic control.

---

## Decisive absences (repo search **and** authenticated code search = 0)

These areas — where 5 of the 8 sorries live — have **no Lean presence at all**, anywhere:

- **Hamilton–Jacobi–Bellman / viscosity solutions / continuous stochastic control** — 0.
- **Schrödinger bridge** (the stochastic-control object) — 0.
- **General / continuous Kantorovich–Rubinstein OT duality** — 0 (only finite `flow-sinkhorn`).
- **Measurable selection / Kuratowski–Ryll-Nardzewski** — 0 dedicated repos (Mathlib has
  scattered `measurableSet_of_…`, no worst-case-measure selector).
- **Hopf–Cole**, **Fenchel–Rockafellar duality** — 0.

Consistent with the pinned-Mathlib grep (`476fb97b62`): Kantorovich/Wasserstein/Girsanov
all absent; `condKernel`/disintegration and `Topology.Sion` present.

---

## What this means for the 8 sorries

- **6 Chain-4 controls:** the specific theory is *absent*, not merely unvendored. Realistic
  paths: (a) the **Gaussian/Euler–Maruyama discrete** relaxation the card actually measures,
  using `gibbs-variational`'s Cameron–Martin KL (energy_identity — in progress); (b)
  otherwise documented `axiom`s with provenance, or a long-horizon Mathlib-SDE build on
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
- **Clone audits:** shallow-clone + `grep -c sorry/admit/axiom` + `theorem/lemma` name grep +
  license file + spot-read of the load-bearing file. Repos above audited at the commits noted
  in `SURVEY_LEADS.md`.
- **LLM-PR pool:** all 414 closed-unmerged `LLM-generated` mathlib PRs swept (see
  `dev/journals/2026-07-03-mathlib-llm-proof-mining-journal.md`) — nothing for our gaps.

## Open frontier (not yet mined)

- **Generated-proof corpora** (Lean-Workbook, OProofs, LeanNavigator, LeanExplore /
  LeanSearch declaration indices) — the one un-mined layer; own web APIs, not `gh`. Given
  the whole-GitHub zero result for our exact terms, expect *nearby* lemmas at best.
- **`measurableSelection` code search** 403'd mid-run — rerun to confirm the 0 (repo search
  already = 0).
- **`YuanheZ/lean-stat-learning-theory`** (ICML2026 SLT, 91⭐) — KL / Le Cam / minimax;
  Chain-2-adjacent (our DV is done), low priority; skim if convenient.
