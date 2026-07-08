# Agent prompt — vendor an external proof and use it to push a DRSB placeholder forward

You are working in the Lean 4 repo **`aiq-drsb-formalization`**. Your job: **vendor a
permissively-licensed external Lean result, attribute it correctly, and use it to advance
one of the remaining placeholders** — a real, honest step, no vacuous scaffolds.

Read first (do not skip): `AGENTS.md` (§2 provenance, §5 the vacuous-existential trap, §6
gotchas), `SURVEY_LEADS.md` (the **Vendoring & attribution policy** at the top — mandatory),
`FOUNDATIONS.md` §"Pulling a proof into the pipeline", `PROOF_PIPELINE.md` §2 (the 12
remaining placeholders). The external repos below were **rigorously audited on 2026-07-03**
(clone + grep + license check) — findings are in `SURVEY_LEADS.md` and
`dev/journals/2026-07-03-mathlib-llm-proof-mining-journal.md`. Trust those; re-verify the
specific lemma you vendor, not the whole ecosystem.

## The situation (why this is bridging, not drop-in)

Nothing external drop-in-closes our 12 placeholders: the 6 Chain-4 controls need
multi-dimensional controlled-diffusion Girsanov + **KL between path measures**; the 6
worst-case-structure results need continuous-measure OT worst-case construction. The
usable external work is **finite/discrete or 1-D**. So the deliverable is: vendor the
right *building block* with credit, then use it to either (a) close a placeholder via an honest
bridge, or (b) reduce a bare placeholder to *one explicit, documented hypothesis* (the house
pattern — `le_antisymm(proved, hypothesis)`, as already done for the strong-duality
seams) with the rest genuinely proved from the vendored lemma. **Never** discharge a placeholder
by hypothesising its own conclusion (AGENTS §5).

## Vendor targets (audited; pick per your chosen proof target)

1. **`mrdouglasny/gibbs-variational` — `GibbsVariational/GaussianEntropy.lean`**
   — **Apache-2.0** (trivially compatible), Mathlib-only, ~1 placeholder in the repo (not in
   this file — verify). Reusable lemmas we lack: `klDiv_stdGaussian_map_add` (KL of a
   shifted standard Gaussian `= ½‖h‖²` — the finite **Cameron–Martin / Girsanov
   relative-entropy** identity), `klDiv_gaussianReal_shift`, `klDiv_pi`/`klDiv_prod` (KL of
   product measures), `klDiv_map_measurableEquiv`. **This is the discrete/Gaussian core of
   `ChenGeorgiouPavon2021.energy_identity`** — the Euler–Maruyama + Gaussian-closed-form
   relaxation the DRSB card actually measures (AGENTS §3). *Small, clean — the recommended
   first target.*
2. **`gpeyre/flow-sinkhorn`** — **MIT** (compatible), ~1605 lemmas, `Comparator/Solution.lean`
   proved. Finite entropic-OT: `prop_kappa_ot` (c-transform / potential decomposition),
   `prop_hgamma_ot` (Sinkhorn fixed-point bounds), `thm_approx_linprog` (LP↔entropic
   reduction), finite KL + Pinsker. Use for the **data-driven / empirical** worst-case
   theorems (`MohajerinEsfahaniKuhn2018.*`, `GaoKleywegt2023` Cor 2), whose nominal IS a
   finite measure — the "reduce worst-case to finite OT" path. *Higher value, harder bridge.*
3. **`raphaelrrcoelho/formal-mathfin`** — **Apache-2.0**, ~45k lines, build-enforced
   dependency-clean. Full continuous Itô/SDE-existence(1-D)/Girsanov(BS)/Feynman-Kac +
   `ConvexDuality`. The real foundation to eventually refound `ChenGeorgiouPavon2021`'s
   abstract `SBData` on — but multi-D generalization + KL-of-path-measures is a
   multi-session build. *Do not start a full refactor in one pass; mine a specific lemma.*

## Recommended primary target (achievable this session)

**Vendor `GaussianEntropy.lean` (target 1) and use its Gaussian-KL lemmas to close, or
house-pattern-reduce, the discrete/Gaussian layer of `ChenGeorgiouPavon2021.energy_identity`.**

Concretely:
- The DRSB `energy_identity` (CGP (4.19)) says the control energy `½∫‖u‖²` equals a
  relative entropy `KL(P^u ‖ P^0)` between path laws. In the **Euler–Maruyama / Gaussian
  discretization** (the card's actual measurement), each step's law is a shifted Gaussian
  and `klDiv_stdGaussian_map_add` gives exactly `KL = ½‖drift·√Δt‖²`; summing over steps is
  the discrete energy. Prove this **discrete energy identity** as a new lemma
  (`ForMathlib` or `ChenGeorgiouPavon2021`), proved, from the vendored lemmas.
- Then wire it to `energy_identity`: if the continuous statement is out of reach, restate
  `energy_identity` as proved **modulo one explicit continuous-limit hypothesis** (the
  Euler–Maruyama → SDE limit — a documented OT/SDE edge, exactly the house pattern), with
  the discrete identity proved. This converts a bare placeholder into a proved-modulo-one-edge
  result and lands a genuinely reused external proof. If you find a fully proved close,
  even better — but do not fake one.

If you judge target 2 (flow-sinkhorn → a data-driven worst-case placeholder) more tractable,
that is an acceptable substitute — same rules.

## Vendoring mechanics (follow the policy exactly)

- Put vendored/adapted files under **`ForMathlib/…`** (or a clearly-named `vendor/` subtree
  if copying a file verbatim). Prefer **adapting/porting the specific lemma** into our
  vocabulary over bulk-copying; a re-derivation sidesteps licensing entirely, but if you
  copy, you MUST attribute.
- **File header (mandatory when copied/adapted):** original author + repo URL + **source
  commit permalink** (pin the exact commit you pulled from) + license (SPDX) + retrieval
  date + "adapted by …" if modified. Mirror the DKPS `ForMathlib` header convention.
- **Keep upstream license/notices.** Apache-2.0 and MIT are both compatible with ours
  (Apache-2.0); record the SPDX id. Do NOT vendor anything without a clear permissive
  license (e.g. the Yang-Mills archive is NOASSERTION → forbidden).
- **`README.md`**: add a "Vendored / adapted external proofs" section crediting each source
  (author, repo, commit, license). **`formalization.yaml`**: add a provenance entry for the
  vendored declaration. Update `SURVEY_LEADS.md`'s row (mark "VENDORED", with the commit).

## Workflow & acceptance criteria

- Syntax-check one file fast: `lake env lean <File>.lean` (no lock). Do NOT `lake build` in
  parallel. `set_option autoImplicit false` in every file; DRO multiplier is `lam` (`λ`
  reserved).
- The vendored lemma and any new lemma you prove must be **dependency-clean**:
  `Lean dependency audit <decl>` shows only `propext / Classical.choice / Quot.sound` (no `unsound dependency marker`).
- A full `lake build` is green at the end; any remaining placeholder is *strictly fewer or
  strictly more isolated* than before (a bare placeholder → an explicit named hypothesis counts
  as progress; a new bare placeholder does not).
- Attribution present in **file header + README + formalization.yaml**; `SURVEY_LEADS.md`
  updated. Keep the counts honest (`AGENTS.md` §9, `PROOF_PIPELINE.md` §2).
- Commit as you land (one commit per landed piece), ending the message with the project
  `Co-Authored-By` trailer; the resource-tally hook records automatically.

## Guardrails

- **Provenance anchor unchanged** (AGENTS §2): the DRSB manuscript / "Eq. 47" / `reference/`
  are ~0-weight. Vendor only to prove something the *card* needs.
- Verify the vendored lemma's *statement* against its source and against what you need —
  do not assume a name means what you hope. Watch the KL extended-valued gotcha (AGENTS §6):
  Mathlib `klDiv : ℝ≥0∞`; guard `μ ≪ ν`.
- If, after honest effort, the bridge is bigger than one session, land the **vendoring +
  attribution + the proved discrete lemma**, and leave a precise `PROOF_PIPELINE.md`
  note on the remaining edge. Partial, honest, attributed progress beats a forced close.
