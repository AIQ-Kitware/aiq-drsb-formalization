# AGENTS.md — orientation for anyone (esp. AI agents) picking up this repo

Read this first. It captures *why* this repo exists, the *conventions* you must follow, and
the *traps* — the context that is expensive to re-derive and easy to lose.

> **This file is evergreen: it should contain nothing that goes stale.** No open-goal counts, no
> pinned revisions, no "current" anything. For the dated snapshot — the pin, what is proved, what
> is open, and the live frontier — read **[`STATUS.md`](STATUS.md)** *before* starting work.

Companion docs: **[`STATUS.md`](STATUS.md)** (dated state — start here),
[`JOURNAL.md`](JOURNAL.md) (per-session narrative),
[`README.md`](README.md) (build + library map), [`prose/README.md`](prose/README.md)
(the published-theorem chain), [`formalization.yaml`](formalization.yaml) (per-declaration
source map), [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md) (the proof-pass work plan: every
remaining placeholder ranked by difficulty, the us-vs-Fable split, and the ForMathlib
upstreaming queue), [`FOUNDATIONS.md`](FOUNDATIONS.md) (the classical-theorem *chains*
under DRSB — DKPS-style — with grep-verified Mathlib gaps and search terms for mining
existing AI/human Lean proofs), [`SURVEY_LEADS.md`](SURVEY_LEADS.md) (dated, link-rich
registry of external Lean repos / Mathlib PRs / generated-proof corpora to mine and
re-check — includes the **vendoring & attribution policy**), and
[`PAPER.md`](PAPER.md) (the draft narrative for the AI-formalization method paper: the
*survey-and-stage* method, the related-work survey, and **SLOP** = *Sound Library of Open
Proofs*, the proposed permissive/searchable home for verified AI proofs).

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

## 2. Provenance — what this effort anchors on (and what it must ignore)

**The anchor is the GaTech MAGNET evaluation card + the published theorems it composes.**
Nothing else has normative weight here. Concretely: we formalize the theorem the two
cards' empirical measurement rests on (`E_μ[V] ≤ E_worst-case[V]`, §3), and discharge it
from the real, downloaded, transcribed published sources (§4). The `Drsb` capstone states
the card claims in those terms.

> ⚠️ **The GaTech team's own DRSB manuscript is NOT a source and carries ~0 weight.**
> Its internal labels (`drsbm_paper`, **"Eq. 47"**, **"Algorithm 5: Relaxed Schrödinger
> Bridge"**) appear only in **GaTech code comments** — never on arXiv or any index — and
> the manuscript itself was **wrong**. **Do not chase it, cite it as if published, or let
> it steer a statement.** Do NOT add "get the manuscript from the team" as an action item.
> Where a code label like "Eq. 47" is unavoidable, treat it purely as a *pointer at the
> card's bound formula*, whose backing is Wang–Gao–Xie (§4) — not as a theorem to match.
>
> ⚠️ Likewise a **"TwoPager Theorem 4" / PAC-Bayes** objective was previously carried here
> and has been **excised** (see git log): it lives only in the `reference/` scratch
> (`V1/V4`), is **not referenced by either card or the GaTech code**, and the theorem was
> flawed. `reference/` as a whole is near-0-weight scratch (see `reference/README.md`) —
> mine it only for a proof *pattern* that helps prove something the card actually needs.
> Do not re-introduce its content into the canonical chain.

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
  carries the **log-partition term** $-\rho\log\mathbb E_\nu[e^{g}]$ (backed by Wang–Gao–Xie,
  §4; the GaTech code labels it "Eq. 47", of no normative status — §2).

The estimator (`AdjointMatcher`, a *reward-fine-tuning-as-SOC* scheme the GaTech code
labels "Algorithm 5"); the
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
| **Sinkhorn-DRO log-partition dual** (SDRSB card's bound) | `WangGaoXie2023` | Wang–Gao–Xie, Oper. Res. 2023 | 2109.11926 |
| Donsker–Varadhan / Gibbs (root under the Sinkhorn dual) | `ForMathlib` | classical (Dupuis–Ellis etc.) | — |

Provenance-only (documented in prose, **no Lean library** this pass): Léonard 1308.0215
(SB survey); DSBM 2303.16852, GSBM 2310.02233, Adjoint Matching 2409.08861 (the matching
*estimator*, not the robustness claim). Add libraries for these only if a proof needs them.

The **`Drsb` capstone** composes the above:

| Card claim | Capstone declaration | Discharged by |
|---|---|---|
| `wdrsb_cost_bound.yaml` | `Drsb.wdrsb_cost_bound`, `Drsb.wdrsb_strong_duality` | `BlanchetMurthy2019` / `GaoKleywegt2023` |
| `sdrsb_cost_bound.yaml` | `Drsb.sdrsb_cost_bound`, `Drsb.sdrsb_strong_duality` | `WangGaoXie2023` |
| `sdrsb_cost_bound.yaml` bound formula | `Drsb.sdrsbTerminalBound` | `WangGaoXie2023` log-partition (`f := ρ·g`) |

---

## 5. Repo conventions & workflow (how to work here without breaking things)

- **First-pass policy: STATEMENTS ONLY.** Every theorem body is `:= by placeholder`. We are
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
  restarted). **`reference/WellKnown.lean` has *complete, dependency-clean proofs* of the
  Donsker–Varadhan family** — these have been ported into
  `ForMathlib.MeasureTheory.DonskerVaradhan` (the straightforward proof completions). **Do NOT
  pull the PAC-Bayes / "TwoPager Theorem 4" material (`V1/V4`'s
  `clip`/`gClip`/`BCE`/`pac_bayes_*`) into the canonical chain** — it is card-irrelevant
  and was excised (see §2 and git log).
- **Shared vocabulary lives in `ForMathlib.OT`** (`open ForMathlib.OT`): `expect`,
  `klReal`, `couplings`, `otCost`, `W2sq`, `wassersteinBall`, `Wkappa`, `sinkhornBall`,
  `droValue`. Use these so the paper libs and the capstone compose. A paper library
  imports only `Mathlib` + `ForMathlib` (keep them independent); only `Drsb` imports the
  paper libs.
- **Syntax-check a single leaf file with `lake env lean <path>.lean`** (fast, ~30–60 s
  for the Mathlib import, no build lock) when that file's imported local modules already
  have `.olean`s or are unchanged. **Do NOT run `lake build` in parallel** with other
  agents — it takes a lock. Success = exit 0 with only warnings; fix every red `error:`.
- **Aggregate-import files need a prebuild.** `ForMathlib/MeasureTheory/GaussianCameronMartin.lean`
  and `ChenGeorgiouPavon2021/Basic.lean` are intentionally aggregate imports over split theorem
  modules, so a fresh checkout must build their imported modules before direct-file checks. Use
  `dev/check_cgp_module_split.sh` for the canonical split smoke test.
- **`set_option autoImplicit false`** in every file (also set globally in `lakefile.toml`).
- **Note `λ` is a reserved keyword** in Lean 4 — the DRO multiplier is spelled `lam`.
- ⚠️ **GREP HYGIENE — never write the words `sorry` or `axiom` in a Lean comment or docstring.**
  They make the proof-debt inventory ungreppable. Say "placeholder" / "open goal", and
  "dependency audit" (for `#print axioms`). *This is why the prose in these docs reads oddly.*
  The rule buys you an exact inventory — a bare `sorry` tactic is then the **only** match:
  ```bash
  grep -rn --include=*.lean -w sorry ForMathlib Drsb ChenGeorgiouPavon2021 \
      BlanchetMurthy2019 GaoKleywegt2023 MohajerinEsfahaniKuhn2018 WangGaoXie2023
  ```
  (Exclude `.lake/` and `.reference-clones/` — vendored third-party trees have their own debt.)
  Markdown docs may use the literal words; Lean sources may not.

### The two house rules that keep this repo sound

- **Isolate content to an explicit edge; never to a placeholder.** When a theorem needs mathematics
  Mathlib does not have, do *not* leave a placeholder and do *not* invent a hypothesis that makes the
  statement vacuous. Add a **named, satisfiable** hypothesis carrying exactly the missing content, and
  *derive* the conclusion from it. The canonical shape is
  `le_antisymm(constructive-half, one-attainment-edge)` — used by every strong-duality equality here.
  An edge is only honest if its premises are **jointly satisfiable in the real problem**.
- ⚠️ **The `if False then True` landmine — check for it every time you remove a placeholder.**
  The tell is *a conclusion that equates a real object to a free operator/function argument with no
  hypothesis linking them* (e.g. concluding `u* = grad(log φ)` where `grad` is an unconstrained
  argument — instantiate `grad := 0` and the theorem is false). Such a statement can never be
  discharged soundly, and a downstream theorem that `rw`s through it will compile while being false.
  Four such theorems were found and fixed here; one was **green but false**. Always ask: *could I
  instantiate a free variable to break this conclusion?* — then confirm with a dependency audit
  (`#print axioms`) that a green theorem does not secretly carry the placeholder marker.
- **Progress-bar policy.** Placeholders mark **missing mathematical capstones only**, and live in the
  module owning that frontier. Do **not** add placeholders to downstream integration/assembly lemmas
  that merely consume those targets — prove them from the targets, or state the target as an explicit
  hypothesis/interface and wire it later.

### Editing docs: delete the wrong thing, don't annotate it

When you find a stale or wrong claim — in a doc, a docstring, or a comment — **fix it in place, or
delete it. Do not leave it standing with a correction bolted on.** A note that says *"⚠️ CORRECTION:
the paragraph below is out of date"* leaves the wrong claim there for the next reader to absorb, and
now there are two things to maintain instead of one.

> **Sometimes the fix is to make something not even mention the wrong thing.**

A reader should never have to reason about which of two adjacent statements is current. Concretely:
- Overwrite the stale sentence; don't append a rebuttal to it.
- If a whole section has been superseded, delete it or move it under an explicitly historical heading
  (`JOURNAL.md` is where history belongs) — don't leave it in the live orientation path.
- Corollary for this repo's layout: **evergreen files (`AGENTS.md`) must contain no counts, revisions,
  or "current" state at all** — not even correct ones, because they will not stay correct. Dated facts
  go in `STATUS.md`; narrative goes in `JOURNAL.md`.

### Adding a new paper library
1. `NewPaper.lean` containing only `import NewPaper.Basic`.
2. `NewPaper/Basic.lean`: `import Mathlib` (+ `ForMathlib.OptimalTransport.Basic` / DV),
   `set_option autoImplicit false`, `namespace NewPaper`, defs + theorem targets.
3. Add `[[lean_lib]] name = "NewPaper"` to `lakefile.toml` (and to `defaultTargets`).
4. `lake env lean NewPaper/Basic.lean` until clean; then update `formalization.yaml`
   `sources`/`main_results` and this table.

---

## 6. Known gotchas (do not re-learn the hard way)

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
- **Sinkhorn ball uses an EXTERNAL reference `ν`** (fixed 2026-07 by the Sinkhorn audit).
  Wang–Gao–Xie Def 1's entropic penalty is `KL(γ ‖ P̂ ⊗ ν)` with `ν` an *external*
  reference (Lebesgue/Gaussian) — the same `ν` the dual's log-partition integrates over —
  NOT the product of the two coupling marginals. The old `ForMathlib.OT.Wkappa`/
  `sinkhornBall` used `μ⊗μ̂` (marginals) and so mismatched the dual. Now:
  `Wkappa κ ν μ̂ μ`, `sinkhornBall μ̂ ν κ ε` carry `ν`; consumers (`WangGaoXie2023.strong_duality`,
  `primal_feasible_radius_nonneg`, `Drsb.sdrsb_*`) thread it. See `prose/sinkhorn-dro-duality.md`
  (audit-correction admonition).
- **`WangGaoXie2023.primal_feasible_iff` → `primal_feasible_radius_nonneg` (RESOLVED
  2026-07).** The naive `Nonempty ↔ 0 ≤ ε` is **false** for the raw `Wkappa` ball: even
  with the corrected external-`ν` reference, `Wkappa κ ν μ̂ μ̂ > 0` for a non-degenerate
  nominal (the entropic term forbids the diagonal coupling), so the ball's true
  nonemptiness threshold is the free energy `−κ·𝔼_μ̂[log ∫ e^{−c/κ} dν] ≥ 0`, generically
  `> 0`. Restated & **proved** as the honest **necessity** half — `0 ≤ κ ⇒ (Nonempty →
  0 ≤ ε)`, immediate from `Wkappa ≥ 0`. The paper's full `↔ ρ ≥ 0` (Theorem 1(I)) holds
  only after the reference-kernel/`ρ̄` reformulation to the KL-ball; its sufficiency
  direction is the worst-case-measure **attainment** edge (T4, deferred). The decl
  docstring records the full derivation.

---

## 7. Build / environment

- **Policy: track the latest Mathlib master** (`inputRev = master`). Bump with `lake update mathlib`,
  which also syncs `lean-toolchain`, then `lake build` and re-check dependency audits. Older
  toolchains are not kept on disk, so do **not** plan a proof around an older pin — if a lemma you
  need moved or was renamed upstream, adapt rather than pinning back.
- **The current toolchain and Mathlib rev are in `lean-toolchain` and `lake-manifest.json`. Read
  them; they are the only source of truth.** (Deliberately not repeated here.)
- Fresh setup: `lake exe cache get` (downloads prebuilt Mathlib oleans, ~minutes) then
  `lake build`. A fresh clone has **no** oleans — `cache get` first, or everything is slow.
  A full rebuild after a Mathlib bump takes **>10 minutes**; run it in the background.
- **Never commit** `.lake/` or `prose/papers/*.pdf` — both are git-ignored.

## 8. Git / submodule

- This is a **git submodule** of `aiq-eval-runner`; its `origin` is a local path
  (`/home/joncrall/code/aiq-drsb-formalization`). Commit here; to share:
  `git push origin main`, then in the parent
  `git add formalizations/aiq-drsb-formalization` to bump the pointer.
- Commit style: end messages with the project's `Co-Authored-By` trailer.

## 9. Where the project currently stands

**This section is deliberately empty of facts, because they go stale.**

- **Current state** (pin, open-goal inventory, the live frontier, what is proved) →
  [`STATUS.md`](STATUS.md).
- **How we got here** (per-session narrative, soundness audits, dead ends) →
  [`JOURNAL.md`](JOURNAL.md).
- **What to work on next** (ranked, with difficulty) → [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).
- **What exists externally** (vendorable proofs, Mathlib PRs, name-collision traps) →
  [`SURVEY_LEADS.md`](SURVEY_LEADS.md).

Re-derive the two facts that matter most rather than trusting any doc:

```bash
cat lean-toolchain && grep -A2 '"name": "mathlib"' lake-manifest.json   # the real pin
grep -rn --include=*.lean --exclude-dir=.lake --exclude-dir=.reference-clones --exclude-dir=reference -w sorry .
```

<!-- BEGIN llm_resource_tally v1.0.0 (managed block — regenerated by `install`; edits below will be overwritten) -->
## Resource accounting — the LLM compute this work costs (CRITICAL: do this every commit)

Every commit in this repo is produced by an LLM agent; we keep a **measured** per-commit
record of the tokens/model it cost (inference-time, energy & carbon are derived later).

- **After cloning**, wire the hook once (offline, idempotent): `python3 .llm_resource_tally/tool install`
- Thereafter every `git commit` auto-records. To record by hand: `python3 .llm_resource_tally/tool record`
- **At session end** (captures planning/chat that produced no commit): `python3 .llm_resource_tally/tool reconcile && python3 .llm_resource_tally/tool rollup`
- Codex agents: `python3 .llm_resource_tally/tool record --backend codex`
- Other non-Claude agents: `python3 .llm_resource_tally/tool record --backend <name> --transcript <path>`

**Tag what the work was** with `--label` (e.g. `record --label implementation`, or
`reconcile --label planning`) so non-code work is counted and attributable.

Tokens/model are MEASURED from your session transcript (deduped by message id — do NOT
hand-count). The ledger `.llm_resource_tally/ledger/` (at this repo's root) is append-only,
per-session, concurrency-safe, and stores measurements only.
<!-- END llm_resource_tally -->

## Project-wide theorem-target scaffold

`ChenGeorgiouPavon2021.ProjectTheoremTargets` imports the current global progress-bar scaffold.  New
placeholders should be added only for missing mathematical capstones and should be placed in the logical
module where the theorem belongs.  Do not add downstream assembly placeholders merely to connect already
named theorem targets; assembly should be proved from the targets or left until the targets are
proved.

<!-- lean4-skills:start -->
## Lean 4 Workflows

This project is configured to use lean4-skills.

Skill reference:
- /home/agent/.local/share/lean4-skills/plugins/lean4/skills/lean4/SKILL.md

Before running lean4-skills helper commands, source:

```bash
source .lean4-skills.env
```

Environment:
- LEAN4_PLUGIN_ROOT=/home/agent/.local/share/lean4-skills/plugins/lean4
- LEAN4_SCRIPTS=$LEAN4_PLUGIN_ROOT/lib/scripts
- LEAN4_REFS=$LEAN4_PLUGIN_ROOT/skills/lean4/references
- PATH includes $LEAN4_PLUGIN_ROOT/bin

Useful checks:

```bash
command -v lean4-skills-sorry-analyzer
lean4-skills-sorry-analyzer . --format=summary --report-only
```

Lean proof workflow notes:
- Prefer per-file checks with `lake env lean path/to/File.lean`.
- Use `lake build` as a final/project checkpoint gate.
- Do not change theorem statements or add axioms unless explicitly requested.
- Keep Lean lines near mathlib style, roughly 100 characters.
<!-- lean4-skills:end -->
