# AGENTS.md — orientation for anyone (esp. AI agents) picking up this repo

Read this first. It captures *why* this repo exists, *what* has been established, and
the *traps* — the context that is expensive to re-derive and easy to lose. Companion
docs: [`README.md`](README.md) (build + library map), [`prose/README.md`](prose/README.md)
(the published-theorem chain), [`formalization.yaml`](formalization.yaml) (per-declaration
source map), [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md) (the proof-pass work plan: every
remaining `sorry` ranked by difficulty, the us-vs-Fable split, and the ForMathlib
upstreaming queue), [`FOUNDATIONS.md`](FOUNDATIONS.md) (the classical-theorem *chains*
under DRSB — DKPS-style — with grep-verified Mathlib gaps and search terms for mining
existing AI/human Lean proofs).

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
> Schrödinger Bridge."** **Neither is on arXiv or any index** (searched thoroughly,
> 2026-07). So every "Eq. 47 / Algorithm 5" reference comes from the **GaTech code**
> (comments), *not* a PDF. **Do not cite those numbers as if published.** To pin them,
> get the manuscript from **Jinhwan Sul (GaTech)**.
>
> ⚠️ A **"TwoPager Theorem 4" / PAC-Bayes** objective was previously carried in this
> repo but has been **excised** (see git log): it originated in the `reference/`
> scratch (`V1/V4`), is **not referenced by either card or the GaTech code**, and the
> theorem was flawed. Do not re-introduce it.

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
| Donsker–Varadhan / Gibbs (root under the Sinkhorn dual) | `ForMathlib` | classical (Dupuis–Ellis etc.) | — |

Provenance-only (documented in prose, **no Lean library** this pass): Léonard 1308.0215
(SB survey); DSBM 2303.16852, GSBM 2310.02233, Adjoint Matching 2409.08861 (the matching
*estimator*, not the robustness claim). Add libraries for these only if a proof needs them.

The **`Drsb` capstone** composes the above:

| Card / DRSB result | Capstone declaration | Discharged by |
|---|---|---|
| `wdrsb_cost_bound.yaml` | `Drsb.wdrsb_cost_bound`, `Drsb.wdrsb_strong_duality` | `BlanchetMurthy2019` / `GaoKleywegt2023` |
| `sdrsb_cost_bound.yaml` | `Drsb.sdrsb_cost_bound`, `Drsb.sdrsb_strong_duality` | `WangGaoXie2023` |
| DRSB "Eq. 47" | `Drsb.eq47Bound` | code-derived formula (unpublished) |

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
  restarted). **`reference/WellKnown.lean` has *complete, axiom-clean proofs* of the
  Donsker–Varadhan family** — these have been ported into
  `ForMathlib.MeasureTheory.DonskerVaradhan` (the free `sorry` removals). **Do NOT
  pull the PAC-Bayes / "TwoPager Theorem 4" material (`V1/V4`'s
  `clip`/`gClip`/`BCE`/`pac_bayes_*`) into the canonical chain** — it is card-irrelevant
  and was excised (see §2 and git log).
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
- **`WangGaoXie2023.primal_feasible_iff` is suspected mis-stated** (still `sorry`; do
  not try to prove it as-is). `(sinkhornBall μhat κ ε).Nonempty ↔ 0 ≤ ε` is likely
  *false* for the coupling-based `ForMathlib.OT.Wkappa`: for a non-degenerate nominal,
  `Wkappa κ μhat μhat > 0` (the product coupling has positive `𝔼‖x−y‖²`; the diagonal
  coupling — zero cost — is singular w.r.t. the product, so its KL term is `+∞`). Hence
  at `ε = 0` the RHS holds but the ball is empty. The paper's Sinkhorn discrepancy has
  `W(P,P)=0` under its conditional/regularised definition, which `Wkappa` does not
  encode. Fix the statement (prose re-derivation) before attempting a proof.

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

- **Done:** repo scaffolded; `ForMathlib` + 5 paper libraries + `Drsb` capstone all
  `lake build` green; prose transcriptions + PDFs in place; `formalization.yaml` maps
  every declaration to its source.
- **Proofs landed (proof pass, foundational-first):**
  - `ForMathlib.MeasureTheory.DonskerVaradhan` — the full DV family (axiom-clean).
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
- **Next steps + the full triage live in [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).**
  Headline: the **card cost bounds need only WEAK duality** (`≤`), so the tractable
  critical path is `weak_duality_prop1` (T3, Fable) → `Drsb.*_cost_bound` (T2). The
  strong-duality `≥` / SDE-PDE block is T4 (not in Mathlib) — defer/axiomatize. The
  ForMathlib upstreaming queue (DV ✓, Normalization ✓, WeakDuality 🔜, SinkhornScaling 🔜)
  is the "Mathlib-contributable proofs" pipeline.
- When a `reference/` result is validated and promoted, update `reference/README.md`.

## Resource accounting — the resource cost of the LLM work (CRITICAL: DO THIS EVERY COMMIT)

Every commit here is produced by an LLM agent; we keep a measured record of the
compute each commit cost. It is near-zero effort:

- Install once: `git config core.hooksPath dev/resource_tally/hooks` — then every
  commit auto-records. (Or run `python3 dev/resource_tally/resource_tally.py record`
  right after committing.)
- At the end of a work session: `python3 dev/resource_tally/resource_tally.py rollup`.
- Codex/other agents: `record --transcript <path/to/session.jsonl>`.

Tokens/model are MEASURED from your session transcript (deduped by message id — do
not hand-count). The ledger (`dev/resource_tally/data/resource-ledger.jsonl`) 
is append-only, per-session, concurrency-safe. See `dev/resource_tally/README.md`.
