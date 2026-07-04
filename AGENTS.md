# AGENTS.md — orientation for anyone (esp. AI agents) picking up this repo

Read this first. It captures *why* this repo exists, *what* has been established, and
the *traps* — the context that is expensive to re-derive and easy to lose. Companion
docs: [`README.md`](README.md) (build + library map), [`prose/README.md`](prose/README.md)
(the published-theorem chain), [`formalization.yaml`](formalization.yaml) (per-declaration
source map), [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md) (the proof-pass work plan: every
remaining `sorry` ranked by difficulty, the us-vs-Fable split, and the ForMathlib
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
  - `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost` — the OT-DRO
    per-coupling **weak-duality kernel** (ported from `reference/V4.lean`, generalized to
    arbitrary cost `c`); axiom-clean.
  - ⭐ **BOTH DRSB evaluation-card claims PROVED, axiom-clean** — the project's headline
    result `𝔼_perturbed[V] ≤ 𝔼_worst-case[V]` for both balls:
    - `Drsb.wdrsb_cost_bound` (Wasserstein): weak-duality kernel + `sqCost` symmetry, under
      regularity + the OT-attainment edge `hOT`.
    - `Drsb.sdrsb_cost_bound` (Sinkhorn): composes the proved
      `WangGaoXie2023.sinkhorn_weak_duality_kernel` (per-point Gibbs/DV bound integrated
      over `p₀`) with `budget ≤ ε`, under `hκ>0` + the Sinkhorn attainment+disintegration
      edge `hSink`; dual restricted to `0<lam` (the `lam=0` `logPartition` is junk — a
      third statement issue found this pass; ess-sup convention unencoded).
    The cards need only the `≤` direction; the strong-duality `≥` seams are now discharged
    too (below), each modulo one explicit attainment hypothesis rather than a `sorry`.
  - **General duality + the "strong = weak + attainment" pattern** (axiom-clean):
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
  - **Atop-a-sorry reductions** (concentrate debt, not axiom-clean):
    `ChenGeorgiouPavon2021.schrodingerBridge_KL_eq_SOC` (sInf-translation atop
    `energy_identity`) and `optimal_control_eq_neg_grad_value` (atop
    `optimal_control_eq_grad_log` + a `grad`-negation edge).
  - **ALL strong-duality *equalities* proved** (2026-07), each `le_antisymm(weak,
    attainment)` with the `≥` isolated to one explicit OT-attainment hypothesis:
    `BlanchetMurthy2019.wdro_strong_duality` (primary Wasserstein), `WangGaoXie2023.strong_duality`
    (Sinkhorn Theorem 1(II)), and the two **`Drsb` capstones** `wdrsb_strong_duality` /
    `sdrsb_strong_duality` — **`Drsb` is now sorry-free** (all four card+duality results land).
  - `WangGaoXie2023.primal_feasible_radius_nonneg` (was the mis-stated `primal_feasible_iff`)
    — the honest necessity half of Theorem 1(I), `0 ≤ κ ⇒ (Nonempty → 0 ≤ ε)`, axiom-clean
    (see §6). Sufficiency is the deferred ρ̄-ball attainment edge.
- **Finite Sinkhorn scaling — ✅ PROVED, axiom-clean (2026-07):**
  `ForMathlib.matrix_scaling_exists` + `ForMathlib.sinkhorn_potentials_exist`
  (`ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean`). Mathlib has **neither** Brouwer
  nor the Birkhoff/Hilbert-metric contraction (grep-verified), so the proof is a **log-domain
  convex minimization** of `ψ(b)=∑ᵢ pᵢ log(∑ⱼ Gᵢⱼ bⱼ) − ∑ⱼ qⱼ log bⱼ` over the open simplex:
  boundary blow-up `−qⱼ log bⱼ→+∞` confines the sublevel set to an explicit compact set
  (extreme value theorem — no coercivity lemma), and the marginal equations fall out of the
  1-D directional derivatives along `eⱼ−eₖ` (`IsLocalMin.hasDerivAt_eq_zero`), with **mass
  conservation `∑p=∑q` exactly killing the Lagrange multiplier**. `ChenGeorgiouPavon2021.
  sinkhorn_potentials_exist` now delegates to a sorry-free proof. `matrix_scaling_exists`
  is a clean general lemma staged for Mathlib upstreaming (Sinkhorn scaling is a genuine gap).
- **Vendored external proof + discrete energy identity — ✅ landed (2026-07):** vendored
  `mrdouglasny/gibbs-variational`'s `GaussianEntropy.lean` (Apache-2.0, commit `75e08d8`) →
  `ForMathlib/MeasureTheory/GaussianEntropy.lean` (Cameron–Martin `KL(N(·+h)‖N)=½‖h‖²`;
  attribution in file header + README + `formalization.yaml` + `SURVEY_LEADS.md`). Built on
  it, the **sorry-free, axiom-clean** Euler–Maruyama discrete energy identity
  `ForMathlib…klDiv_emShift_eq_emEnergy` → `ChenGeorgiouPavon2021.energy_identity_euler_maruyama`:
  `(KL(P^u‖P^0)).toReal = ∑ₖ Δt·½‖u_k‖²`, the discrete/Gaussian layer of `energy_identity`
  (4.19) — the quantity the card measures (§3). The continuous `energy_identity` stays a bare
  `sorry` (count unchanged at 12); the single remaining edge is the Δt→0 SDE limit
  (PROOF_PIPELINE §2).
- **Worst-case structure — ✅ BOTH GaoKleywegt corollaries PROVED, axiom-clean (2026-07);
  `GaoKleywegt2023` is now sorry-free:**
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
- **Data-driven duality equality — ✅ PROVED, axiom-clean (2026-07); `MohajerinEsfahaniKuhn2018`
  is now sorry-free:** `worstCaseExpectation_eq_dual` (Thm 4.2). `le_antisymm(weak, attainment)`:
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
  axiom-clean (2026-07); via a NEW KL data-processing inequality.** The Léonard dynamic⇄static
  SB equivalence: `le_antisymm(gluing-edge, DPI-direction)`. `staticSBValue ≤ schrodingerBridgeValueKL`
  is **genuinely proved** — the endpoint projection `e = (ω↦(ω₀,ω₁))` sends a feasible path law to
  a coupling in `Π(ρ₀,ρ₁)`, and coarse-graining can't increase KL, so `klReal(e#P‖endpointLaw) ≤
  klReal(P‖R)`. That inequality is the **new `ForMathlib.MeasureTheory.toReal_klDiv_map_le`** — the
  KL **data-processing inequality**, a *genuine Mathlib gap* (Mathlib has the KL chain rule but no
  DPI / f-divergence file), proved by conditional Jensen on the convex `klFun` (`ConvexOn.map_condExp_le`)
  + `toReal_rnDeriv_map` (pushforward RN-derivative = conditional expectation). Honest edges `hac`
  (`P ≪ R`), `hfin` (finite KL), `hne`; the gluing (path-reconstruction) `≤` isolated to `hglue`.
- **Remaining `sorry`s (5) — ALL in `ChenGeorgiouPavon2021`:** `energy_identity` (continuous
  Girsanov; discrete/EM layer already proved), and four **under-specified** statements —
  `optimal_control_eq_grad_log` / `_sigma_grad_log` / `_grad_value` (HJB), `optimal_coupling_factorization`
  — which each equate `u*`/`dens*` to an *arbitrary passed-in operator* with **no linking
  hypothesis** (false for e.g. `grad := 0`), so honestly closing them needs the SDE *verification
  theorem* added as a hypothesis (statement work / TX), not a proof. Every Wasserstein/Sinkhorn DRO
  duality + worst-case-structure result (`BlanchetMurthy2019`, `GaoKleywegt2023`,
  `MohajerinEsfahaniKuhn2018`, `WangGaoXie2023`, `Drsb`) is PROVED — those five libraries are sorry-free.
- **Next steps + the full triage live in [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).**
  Per the user (2026-07): **no Fable** — decompose each remaining target into its natural
  subproblems and prove step-by-step with the thinking budget turned up. The SDE/PDE and
  OT-measurable-selection blocks may still need a documented `axiom` or a Mathlib-infra lift
  (decide with the coordinator). ForMathlib upstreaming queue:
  DV ✓, Normalization ✓, WeakDuality ✓ (three kernels, incl. the Ξ-restricted one),
  SinkhornScaling ✓ (`matrix_scaling_exists`), **KLDataProcessing ✓ (`toReal_klDiv_map_le` — the
  KL data-processing inequality; a clean standalone Mathlib PR candidate)**.
- When a `reference/` result is validated and promoted, update `reference/README.md`.

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
