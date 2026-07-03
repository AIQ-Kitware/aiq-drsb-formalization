# AGENTS.md — orientation for anyone (esp. AI agents) picking up this repo

Read this first. It captures *why* this repo exists, *what* has been established, and
the *traps* — the context that is expensive to re-derive and easy to lose. Companion
docs: [`README.md`](README.md) (build + library map), [`prose/README.md`](prose/README.md)
(the published-theorem chain), [`formalization.yaml`](formalization.yaml) (per-declaration
source map).

---

## 1. What this repo is for (the one-paragraph version)

This is a **Lean 4 formalization of the theorems behind the GaTech "DRSB" MAGNET
evaluation cards.** It is one node in a broader AIQ TA1 effort: for each team's
evaluation card, state the *idealized theorem* the card's claim rests on, then draw an
explicit **"assumption → relaxation" edge** from each Lean hypothesis to the empirical
card code that relaxes/approximates it. The point is to make precise **what the proof
actually guarantees vs. what the card measures.** DRSB was chosen because — unlike most
TA1 cards, which are empirical thresholds — its claim *is* a known theorem
(distributionally-robust strong duality), so it is genuinely formalizable.

The precedent and template is the sibling repo
[`../aiq-dkps-formalization`](../aiq-dkps-formalization) (JHU DKPS), which fully
formalizes four papers behind the JHU cards. **We are mirroring its structure.**

### The broader effort (context you will not find in this submodule)

These live in the **parent repo** (`aiq-eval-runner`, one level up from
`formalizations/`):

- **`../../docs/planning/ta1-formalization-edges.md`** — the master write-up of the
  "formalization edge" idea, a proof-of-concept on JHU DKPS, and a formalizability
  grading of every TA1 team. DRSB is graded **High**. *Read this to understand the
  mission.*
- **`../../docs/ta1/gatech_drsbm.md`** — the DRSB team doc (contact, cards, assets).
- **`../../ta1/GaTech-DRSBM/`** — the actual GaTech code + the two cards this repo
  targets (see §3).
- **`../../docs/ta1_evaluation_guide.md`** — how MAGNET cards / evaluations work.

MAGNET is the AIQ evaluation framework: each TA1 team ships **cards** (YAML encoding a
scientific claim + a measurement pipeline); `python -m magnet.evaluation <card>` returns
VERIFIED / FALSIFIED / INCONCLUSIVE.

---

## 2. Provenance & the single most important caveat

> ⚠️ **The DRSB manuscript is UNPUBLISHED.** The code calls it `drsbm_paper`; it cites
> its own **"Eq. 47"** (the log-partition worst-case bound) and **"Algorithm 5: Relaxed
> Schrödinger Bridge."** There is also an unpublished companion **"TwoPager"** with a
> **PAC-Bayes Theorem 4** (Eqs. 116–126). **None of these are on arXiv or any index**
> (searched thoroughly, 2026-07). So every "Eq. 47 / Algorithm 5 / Theorem 4 / Eq.
> (116)–(126)" reference comes from the **code + the coordinator**, *not* a PDF.
> **Do not cite those numbers as if published.** To pin them, get the manuscript from
> **Jinhwan Sul (GaTech)**.

Because of this, we formalize the **published theorems the DRSB claims compose**, then
the `Drsb` capstone states the DRSB-specific results in those terms. The published
sources *are* real, downloaded, and transcribed (see §4).

---

## 3. What DRSB actually does (so the theorems make sense)

DRSB trains a **Schrödinger-bridge / stochastic-optimal-control** generative model and
certifies a **distributionally-robust worst-case cost bound** on its value function
$$V(x) = \mathbb E\!\left[\int_0^1 \tfrac12\|u_t\|^2\,dt + \rho\,g(X_1)\ \middle|\ X_0=x\right].$$

The two evaluation cards (in `../../ta1/GaTech-DRSBM/magnet_eval/cards/`) assert, for a
perturbed source distribution $\mu$ in an ambiguity ball around the nominal $p_0$:
$$\mathbb E_\mu[V] \le \mathbb E_{\text{worst-case}}[V].$$

- **`wdrsb_cost_bound.yaml`** — ambiguity set = **Wasserstein-2 ball** (only perturbations
  with `in_ball == True`).
- **`sdrsb_cost_bound.yaml`** — ambiguity set = **Sinkhorn-divergence ball**; the bound
  carries the **log-partition term** $-\rho\log\mathbb E_\nu[e^{g}]$ = DRSB "Eq. 47".

The estimator (`AdjointMatcher`, "Algorithm 5") is *reward-fine-tuning-as-SOC*; the
empirical relaxations (sup-over-ball → max over ~3 perturbations, exact worst-case →
Gaussian closed form, exact $\mathbb E_\mu[V]$ → Euler–Maruyama SDE, exact $W_2$ →
empirical OT) are the "edges" the broader effort wants to draw. See
`../../docs/planning/ta1-formalization-edges.md` §GaTech.

---

## 4. The published-theorem chain (what proves what)

Every link is transcribed in [`prose/`](prose/) (source PDFs in `prose/papers/`,
**git-ignored** — re-download with `curl https://arxiv.org/pdf/<id>`). One Lean library
per theorem-bearing paper:

| Link in the DRSB argument | Library | Published anchor | arXiv |
|---|---|---|---|
| SB ⇄ SOC ⇄ entropic-OT; value fn $V$; $u^\*=\nabla\log\varphi$ | `ChenGeorgiouPavon2021` | Chen–Georgiou–Pavon, SIAM Rev. 2021 | 2005.10963 |
| Wasserstein-DRO strong duality (primary) | `BlanchetMurthy2019` | Blanchet–Murthy, Math OR 2019 | 1604.01446 |
| Wasserstein-DRO duality + worst-case dist. | `GaoKleywegt2023` | Gao–Kleywegt, Math OR 2023 | 1604.02199 |
| Data-driven Wasserstein-DRO reformulation | `MohajerinEsfahaniKuhn2018` | Esfahani–Kuhn, Math Prog 2018 | 1505.05116 |
| **Sinkhorn-DRO log-partition dual (= Eq. 47)** | `WangGaoXie2023` | Wang–Gao–Xie, Oper. Res. 2023 | 2109.11926 |
| PAC-Bayes (Catoni) — TwoPager Thm 4 | `Alquier2024` | Alquier, FnT ML 2024 | 2110.11216 |
| Donsker–Varadhan / Gibbs (shared root) | `ForMathlib` | classical (Dupuis–Ellis etc.) | — |

Provenance-only (documented in prose, **no Lean library** this pass): Léonard 1308.0215
(SB survey); DSBM 2303.16852, GSBM 2310.02233, Adjoint Matching 2409.08861 (the matching
*estimator*, not the robustness claim). Add libraries for these only if a proof needs them.

The **`Drsb` capstone** composes the above:

| Card / DRSB result | Capstone declaration | Discharged by |
|---|---|---|
| `wdrsb_cost_bound.yaml` | `Drsb.wdrsb_cost_bound`, `Drsb.wdrsb_strong_duality` | `BlanchetMurthy2019` / `GaoKleywegt2023` |
| `sdrsb_cost_bound.yaml` | `Drsb.sdrsb_cost_bound`, `Drsb.sdrsb_strong_duality` | `WangGaoXie2023` |
| DRSB "Eq. 47" | `Drsb.eq47Bound` | code-derived formula (unpublished) |
| TwoPager Theorem 4 | `Drsb.twopager_theorem4` | `Alquier2024` |

---

## 5. Repo conventions & workflow (how to work here without breaking things)

- **First-pass policy: STATEMENTS ONLY.** Every theorem body is `:= by sorry`. We are
  matching statements to the papers *first*; proofs come later. Do not start proofs
  unless explicitly asked.
- **Faithfulness rule:** re-derive every statement from `prose/` (which cites the printed
  theorem/eq numbers), **not** from `reference/`. Put a `/-- -/` docstring on each
  theorem citing the prose file + source number; inline-comment each hypothesis.
- **`reference/` is quarantined** ([`reference/README.md`](reference/README.md)):
  old hand-written attempts (`V1/V4/WellKnown.lean`), **trap-laden, NOT built**. Their
  *object definitions* (couplings, `W2sq`, Sinkhorn ball) are fine to reuse for Lean
  syntax; their *theorem statements* are the traps (e.g. `V4`'s
  `optimal_control_eq_neg_grad_value` was a **vacuous existential** — the whole reason we
  restarted). **`reference/WellKnown.lean` has *complete, axiom-clean proofs* of
  Donsker–Varadhan and Hoeffding** — port those into `ForMathlib` to drop `sorry`s for
  free (the statements there are already the intended ones).
- **Shared vocabulary lives in `ForMathlib.OT`** (`open ForMathlib.OT`): `expect`,
  `klReal`, `couplings`, `otCost`, `W2sq`, `wassersteinBall`, `Wkappa`, `sinkhornBall`,
  `droValue`. Use these so the paper libs and the capstone compose. A paper library
  imports only `Mathlib` + `ForMathlib` (keep them independent); only `Drsb` imports the
  paper libs.
- **Syntax-check a single file with `lake env lean <Lib>/Basic.lean`** (fast, ~30–60 s
  for the Mathlib import, no build lock). **Do NOT run `lake build` in parallel** with
  other agents — it takes a lock. Success = exit 0 with only `warning: declaration uses
  'sorry'`; fix every red `error:`.
- **`set_option autoImplicit false`** in every file (also set globally in `lakefile.toml`).
- **Note `λ` is a reserved keyword** in Lean 4 — the DRO multiplier is spelled `lam`.

### Adding a new paper library
1. `NewPaper.lean` containing only `import NewPaper.Basic`.
2. `NewPaper/Basic.lean`: `import Mathlib` (+ `ForMathlib.OptimalTransport.Basic` / DV),
   `set_option autoImplicit false`, `namespace NewPaper`, defs + `sorry` theorems.
3. Add `[[lean_lib]] name = "NewPaper"` to `lakefile.toml` (and to `defaultTargets`).
4. `lake env lean NewPaper/Basic.lean` until clean; then update `formalization.yaml`
   `sources`/`main_results` and this table.

---

## 6. Known gotchas discovered this session (do not re-learn the hard way)

- **Wang–Gao–Xie symbol swap:** the paper's $\varepsilon$ = *entropic regularizer* (our
  Lean `κ`) and $\rho$ = *ball radius* (our Lean `ε`) — reversed from intuition, and both
  collide with DRSB's own $\rho$ (terminal-cost weight) / $\varepsilon$ (budget). See the
  header of `WangGaoXie2023/Basic.lean` and `prose/sinkhorn-dro-duality.md`.
- **Esfahani–Kuhn uses the 1-Wasserstein metric** (unsquared `‖ξ−ξ̂‖`), whereas DRSB and
  Gao–Kleywegt use `W₂²`. Cost order differs; flagged in `MohajerinEsfahaniKuhn2018`.
- **No Mathlib SDE / path-measure theory.** `ChenGeorgiouPavon2021` captures the
  controlled dynamics via an abstract `structure` (`SBData`) with `grad`/`lap`/potentials
  as fields/hypotheses. This is expected; keep statements faithful and comment each
  abstracted object.
- **The two hard proof seams:** the strong-duality **`≥` (attainment) direction** of
  `wdro_strong_duality` / `WangGaoXie2023.strong_duality` needs an optimal-transport
  measurable-selection / worst-case-measure construction **not in Mathlib**. The **`≤`
  (weak duality)** direction and the **Donsker–Varadhan** step *are* tractable (weak
  duality was even proved in `reference/V4.lean` as `wdro_lagrangian_bound`).
- **KL is extended-valued in Mathlib** (`InformationTheory.klDiv : ℝ≥0∞`); we use
  `(klDiv μ ν).toReal`. `(⊤).toReal = 0`, so guard `∀ρ` statements with `ρ ≪ π` where the
  real and extended conventions agree.

---

## 7. Build / environment

- Toolchain **`leanprover/lean4:v4.31.0-rc2`** (pinned in `lean-toolchain`); Mathlib pinned
  in `lake-manifest.json` (rev `476fb97…`, same as the DKPS repo).
- Fresh setup: `lake exe cache get` (downloads prebuilt Mathlib oleans, ~minutes) then
  `lake build`. Builds green; each leaf emits exactly one `sorry` warning.
- **Never commit** `.lake/` or `prose/papers/*.pdf` — both are git-ignored.

## 8. Git / submodule

- This is a **git submodule** of `aiq-eval-runner`; its `origin` is a local path
  (`/home/joncrall/code/aiq-drsb-formalization`). Commit here; to share:
  `git push origin main`, then in the parent
  `git add formalizations/aiq-drsb-formalization` to bump the pointer.
- Commit style: end messages with the project's `Co-Authored-By` trailer.

## 9. Current status & next steps

- **Done:** repo scaffolded; `ForMathlib` + 6 paper libraries + `Drsb` capstone all
  `lake build` green as **statements with `sorry` bodies**; prose transcriptions + PDFs
  in place; `formalization.yaml` maps every declaration to its source.
- **Next (suggested order):** (1) expert review of statements vs. the PDFs, DRO-dual
  hypotheses first; (2) port the proved Donsker–Varadhan / Hoeffding lemmas from
  `reference/WellKnown.lean` into `ForMathlib` (free `sorry` removals); (3) proofs,
  foundational-first: DV → Sinkhorn/Wasserstein weak duality → capstone bounds; the
  strong-duality `≥` direction (§6) is the research-grade seam — scope it explicitly.
- When a `reference/` result is validated and promoted, update `reference/README.md`.

## 10. Resource accounting — the climate cost of the LLM work (DO THIS)

Every commit here is produced by an LLM agent. We keep a legible, **measured**
record of the compute each commit cost, so the repo's lifetime climate footprint
can be tallied. The accounting is designed to be near-zero effort for you.

**The rule (one of two ways):**
- **Preferred — install the hook once, then forget it:**
  `git config core.hooksPath dev/hooks`. After that every `git commit`
  auto-records usage; you do nothing.
- **Otherwise, run one command right after you commit:**
  `python3 dev/resource_tally.py record`

Then, when you finish a work session, refresh the repo-lifetime totals:
`python3 dev/resource_tally.py rollup` (updates the `lifetime_totals` block in
`formalization.yaml`).

**What it does / what's honest about it** (see `formalization.yaml`
`automation.resource_accounting` and the header of `dev/resource_tally.py`):
- **Measured** (ground truth, read from your session transcript): model, and
  input / cache-write / cache-read / output tokens, **deduped by message id** — the
  transcript logs each message several times with identical usage, so summing raw
  records overcounts ~2.6×. Do **not** hand-count tokens; the tool reads the log.
- **Estimated:** inference seconds (`output_tokens ÷ throughput`, assumption
  `time-v0`, unvalidated).
- **Deferred:** energy (kWh) and carbon (gCO₂e). We store tokens/time + the commit
  timestamp now, and compute energy/carbon later (the timestamp pins the grid's
  carbon intensity at commit time). The ledger is recomputable, so better factors
  can be applied retroactively.

**Why it's correct under concurrency / never under- or over-counts:**
- Usage is attributed **per session** (each agent = its own transcript file =
  disjoint turns), keyed by `(session_id, commit)`; the ledger
  (`dev/resource-ledger.jsonl`) is append-only under an `flock`. Two agents in this repo
  at once cannot double-count each other.
- A `record` sweeps a session's turns in `(last-watermark, commit_ts]`; the next
  commit continues from that watermark, so no turn is dropped or counted twice.
- `python3 dev/resource_tally.py reconcile` sweeps any un-committed trailing
  turns into a `pending@…` bucket so work that never produced a commit is still
  counted.

**Codex / other agents:** pass your own log with
`python3 dev/resource_tally.py record --transcript <path/to/session.jsonl>`.

**Porting to another repo:** copy `dev/resource_tally.py`, add the
`resource_accounting` block to that repo's manifest, and add this section to its
`AGENTS.md`. Its only Claude-Code-specific assumption is the transcript location
(`~/.claude/projects/<munged-cwd>/<session>.jsonl`); everything else is generic.
