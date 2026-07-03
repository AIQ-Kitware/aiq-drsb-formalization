# FOUNDATIONS.md — the classical-theorem chains under DRSB, and where to mine proofs

The DRSB results do not sit on Mathlib directly; like the DKPS formalization (whose
spine was **Gram rigidity → Courant–Fischer → Weyl → Davis–Kahan → MDS**), each DRSB
theorem rests on a **chain of well-known classical results**, several of which Mathlib
lacks. This file maps those chains, gives each link a **grep-verified Mathlib gap
status**, and lists **search terms** for surveying existing (AI- or human-authored) Lean
proofs to pull from. It is the DRSB analog of DKPS's `docs/planning/mathlib-candidates.md`.

Companion: [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md) (per-`sorry` ranking + us/Fable
split). Gap claims verified by `grep` against the pinned Mathlib
(`476fb97b621c…`, `lean4:v4.31.0-rc2`) on 2026-07-03 — **re-grep before porting**, and
prefer verifying over trusting memory (a recalled lemma name may be stale).
**Grep hygiene** (learned the hard way): never `head`-truncate a gap-verification grep.
The initial pass wrongly marked **Sion's minimax ABSENT** because `head -5` cut off
before `Mathlib/Topology/Sion.lean` (Analysis/ sorts before Topology/). A web survey
(2026-07) caught it — see §"External artifacts". Gap claims below are post-correction.

Legend: ✅ in Mathlib · 🟡 partial/related infra only · ❌ absent (from-scratch) ·
🟢 done in this repo. Effort: **S** verbatim port · **M** moderate (idiom/generalize) ·
**L** substantial · **XL** needs a missing Mathlib *area*.

---

## Chain 1 — Convex duality ⇒ Kantorovich ⇒ Wasserstein-DRO duality  ⚑ critical path

Powers `BlanchetMurthy2019.wdro_strong_duality`, `GaoKleywegt2023.{weak_duality_prop1,
strong_duality_thm1, …}`, `MohajerinEsfahaniKuhn2018.*`, and (via them) the WDRSB card.

```
Fenchel–Young / convex conjugate ❌
        │
        ├─► Fenchel–Rockafellar duality ❌ ─┐
        │                                    ├─► Kantorovich (OT) duality ❌ ─► Wasserstein-DRO WEAK duality 🟢  ⚑ (per-coupling kernel PROVED; assembly next)
Sion's minimax theorem ✅ (Mathlib.Topology.Sion) ──┘                                   │
                                                                                       ▼
   Rockafellar interchange (∫inf = inf∫) 🟡  +  measurable selection (KRN) ❌  ─────► Wasserstein-DRO STRONG duality ❌ (the `≥` seam)
```

| Link | Mathlib | Effort | Search terms (for the survey) |
|---|---|---|---|
| Fenchel–Young inequality / convex conjugate `f*` | ❌ (no `Analysis/Convex/{Conjugate,Fenchel}`; grep-verified absent) | M | `convex conjugate`, `Legendre transform`, `Fenchel–Young`, `fenchel_young_inequality`, `convexConjugate`, Rockafellar *Convex Analysis* §12 |
| Fenchel–Rockafellar duality | ❌ | L | `Fenchel duality`, `Fenchel–Rockafellar`, `conjugate duality`, `strong duality convex`, Rockafellar Thm 31.1 |
| **Sion's minimax theorem** | ✅ **`Mathlib.Topology.Sion`** (`Sion.minimax`, `Sion.minimax'`, `Sion.exists_isSaddlePointOn`) — USE DIRECTLY | — | (found) — note the `public theorem` module-system headers |
| Kantorovich(–Rubinstein) OT duality | ❌ core (only scaffolds/benchmarks found: `lean-eval-leaderboard` ProblemMongeKantorovich, LeanAide Kantorovich_old_aristotle, `athanor-ai/pythia` WassersteinDistanceNonneg, `gpeyre/flow-sinkhorn` Applications/OT + AppendixEOT) | XL | `Kantorovich duality`, `Kantorovich–Rubinstein`, `c-transform`, `Villani Thm 5.10`; **reduce to finite/discrete OT** (LP + Sion) to avoid general measurable OT |
| Rockafellar interchange `∫ inf = inf ∫` | 🟡 (`lintegral` monotone-conv only) | L | `interchange integral infimum`, `Rockafellar–Wets Thm 14.60`, `normal integrand`, `decomposable space` |
| Measurable selection (Kuratowski–Ryll-Nardzewski) | ❌ | XL | `measurable selection`, `Kuratowski Ryll-Nardzewski`, `Jankov von Neumann`, `exists_measurable_selector`, `measurableSet_of_isMinOn` |

> **Payoff shortcut (now partly banked):** the evaluation **cards need only the
> WEAK-duality node** (the `≤`, boxed ⚑) — no minimax, no Kantorovich, no selection. Its
> reusable kernel, the **per-coupling Lagrangian bound, is now PROVED**:
> `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost` (ported from
> `reference/V4.lean::wdro_lagrangian_bound`, generalized to arbitrary cost `c`). What
> remains for the card path is the *assembly* (`inf_π 𝔼_π[c] = otCost ≤ δ`, then `sup_μ`,
> `inf_λ`) → `GaoKleywegt2023.weak_duality_prop1` → the cost bounds. The rest of Chain 1
> (Fenchel + selection) is only for the STRONG-duality capstones — defer; and **Sion is
> now available** for the minimax step if the assembly wants it.

---

## Chain 2 — Entropic / Gibbs ⇒ Sinkhorn-DRO duality  (mostly built)

Powers `WangGaoXie2023.strong_duality` (the SDRSB card's log-partition bound term).

```
Gibbs' inequality (KL ≥ 0) ✅ ─► Donsker–Varadhan variational formula 🟢 (ForMathlib, PROVED)
                                          │
   cgf / log-partition ✅ (Mathlib mgf,cgf) ─┴─► entropic inner soft-max 🟢 (logPartition_eq_gibbs_sSup, PROVED)
                                                        │
                                                        ▼
                                        Sinkhorn-DRO WEAK duality ❌ (outer inf over λ + ball Lagrangian) ─► STRONG duality ❌ (`≥` seam)
```

| Link | Mathlib | Effort | Search terms |
|---|---|---|---|
| Donsker–Varadhan variational formula | 🟢 **proved here — full equality** (`ForMathlib.MeasureTheory.DonskerVaradhan`) | — | `Donsker–Varadhan`, `Gibbs variational principle`, `Measure.tilted`, `variational formula relative entropy`, Dupuis–Ellis |
| cumulant generating function = log-partition | ✅ (`Probability/Moments/Basic` `cgf`) | S | `cgf`, `mgf`, `cumulant generating function`, `log ∫ exp` |
| Sinkhorn-DRO weak duality (outer `inf_λ`) | ❌ | L | `Sinkhorn distributionally robust`, `entropic DRO dual`, `KL-DRO dual`, Wang–Gao–Xie 2021 (arXiv 2109.11926) |

*Healthiest chain, and we are AHEAD of the external art here.* Survey (2026-07) found
`mrdouglasny/gibbs-variational` (Mathlib-only Gibbs/DV work over Mathlib's `klDiv`), but
its README states only the **DV inequality** is proved while the **equality is a
skeleton/`sorry`** and is *false as written* due to `.toReal` on infinite KL. Our
`ForMathlib` DV is the **full `IsGreatest`/`sSup` equality, axiom-clean**, and it dodges
exactly that trap by guarding with `μ ≪ ν` + `toReal_klDiv_of_measure_eq` (AGENTS.md §6,
the extended-valued-KL gotcha). So: mine `gibbs-variational` for KL lemmas / the
finite-dim Boué–Dupuis bound, but **do not depend on its DV equality** — ours supersedes
it. Only the outer Lagrangian assembly remains (a T3 analog of Chain 1's weak node; the
equality side needs the same `ENNReal`/`EReal` care).

---

## Chain 3 — Perron–Frobenius ⇒ Sinkhorn scaling  (self-contained, finite-dim)

Powers `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` (now delegating to
`ForMathlib.LinearAlgebra.Matrix.SinkhornScaling`).

```
Birkhoff polytope / doubly-stochastic ✅ ─┐
                                          ├─► Hilbert projective metric / Birkhoff contraction ❌ ─► Perron–Frobenius (positive matrix) 🟡 ─► Sinkhorn–Knopp / matrix scaling ❌ (staged)
positive-matrix irreducibility defs 🟡 ───┘
```

| Link | Mathlib | Effort | Search terms |
|---|---|---|---|
| Doubly-stochastic / Birkhoff–von Neumann | ✅ (`Analysis/Convex/Birkhoff`, `LinearAlgebra/Matrix/DoublyStochasticMatrix`) | — | `doublyStochastic`, `Birkhoff polytope`, `Birkhoff von Neumann` |
| Perron–Frobenius (dominant eigenvalue/eigenvector of a positive matrix) | 🟡 **active Mathlib PR cluster** #39919 (Collatz–Wielandt / Perron root bounds), #39920 (PF for primitive matrices), #39917 (aux matrix/topology lemmas); merged #28728 (Irreducible+Primitive+Quiver). External `mrdouglasny/spectral-positivity` (PF, Jentzsch, Collatz–Wielandt) | L | `Perron Frobenius`, `Collatz–Wielandt`, `primitive matrix`, `spectral radius nonneg matrix` |
| Hilbert projective metric / Birkhoff contraction | ❌ | L | `Hilbert projective metric`, `Birkhoff contraction`, `Garrett Birkhoff`, `cone contraction` |
| **Sinkhorn–Knopp / matrix scaling (DAD)** | ❌ core (staged, `sorry`); external **`gpeyre/flow-sinkhorn`** has Lean Sinkhorn / KL-projection / duality / primal-dual-bounds files — inspect | L | `Sinkhorn Knopp`, `matrix scaling`, `RAS`, `DAD theorem`, `iterative proportional fitting`; in flow-sinkhorn: `KLProjection`, `DualConvergence`, `PrimalDualBounds` |

*Purely finite-dimensional and self-contained — a strong **Fable ticket (F2)**, provable
without any measure theory. Survey (2026-07) upgraded this chain twice: the **PF
sub-layer has an active Mathlib-native PR cluster** (#39919/#39920/#39917 — build on
these so the upstream composes; better than the archived Zulip thread), and
**`gpeyre/flow-sinkhorn`** is a live external Lean Sinkhorn/OT repo (verify its `sorry`
inventory and license before depending). Sinkhorn scaling in core Mathlib is still
new — but no longer obviously from-scratch.*

> **Recommended build path (revised by survey).** Don't start from Perron–Frobenius
> alone. **Start from Mathlib's doubly-stochastic / Birkhoff API**
> (`Analysis/Convex/Birkhoff`, `Analysis/Convex/DoublyStochasticMatrix`,
> `LinearAlgebra/Matrix/Stochastic`), then add the row/column scaling maps, positivity
> preservation, and KL / I-projection convergence — pulling auxiliary lemmas from
> `gpeyre/flow-sinkhorn`, `StatLean`, and the active PF PRs. PF becomes a sub-lemma, not
> the foundation. (See `SURVEY_LEADS.md`.)

---

## Chain 4 — Stochastic control / Schrödinger bridge  (DEEP — no Mathlib foundation)

Powers `ChenGeorgiouPavon2021.{energy_identity, optimal_control_eq_grad_log,
optimal_control_eq_grad_value, dynamic_eq_static_SB, optimal_coupling_factorization}`
and, at the paper level, the DRSB value function `V` itself.

```
Itô calculus / SDE ❌ ─► Girsanov ❌ ─► relative-entropy decomposition (energy identity) ❌
                                    └─► Feynman–Kac ❌ ─► Hopf–Cole ❌ ─► HJB / optimal control ❌
```

| Link | Mathlib | Effort | Search terms |
|---|---|---|---|
| Itô integral / SDE existence | ❌ | XL | `Itô integral`, `stochastic integral`, `stochastic differential equation`, `MeasureTheory stochastic` |
| Girsanov's theorem | ❌ | XL | `Girsanov`, `change of measure`, `Radon–Nikodym exponential martingale`, `Cameron–Martin` |
| Feynman–Kac | ❌ | XL | `Feynman–Kac`, `Kolmogorov backward equation` |
| Hamilton–Jacobi–Bellman / Hopf–Cole | ❌ | XL | `Hamilton Jacobi Bellman`, `Hopf–Cole transform`, `viscosity solution`, `dynamic programming PDE` |

> **Still defer — but "all absent" is no longer literally true.** Dedicated external
> Lean efforts exist: **`RemyDegenne/brownian-motion`** (Brownian motion complete;
> stochastic integral + Itô in progress) and **`raphaelrrcoelho/formal-mathfin`**
> (machine-checked math-finance: Itô core, Feynman–Kac wiring, partial Girsanov — with
> disclosed gaps in distributional Girsanov / SDE existence / PDE regularity). Neither is
> mature enough to be a low-risk dependency. Every link still needs a Mathlib *area* that
> core lacks; pending it, record these as documented `axiom`s with provenance, or keep as
> `sorry` and treat as out-of-scope for the cards (they underlie `V`'s construction, not
> the robustness bound). Decide with the coordinator. Keep both repos on the radar as
> future upstream dependencies.

---

## External artifacts & leads → [`SURVEY_LEADS.md`](SURVEY_LEADS.md)

The **dated, link-rich registry** of every external lead — repos, Mathlib PRs,
generated-proof corpora (Lean-GitHub, OProofs, LeanNavigator, CAM-Bench, AMBER, …),
Zulip threads, and the `label:LLM-generated × area` PR-search recipes — lives in
[`SURVEY_LEADS.md`](SURVEY_LEADS.md) so we can follow up and re-check moving targets.
Top hits, by chain:

- **Chain 1 roots:** Sion ✅ `Mathlib.Topology.Sion` (use now); Fenchel — author ourselves.
- **Chain 1-heavy / OT:** only scaffolds (`flow-sinkhorn` Applications/OT, benchmarks) — defer / reduce to finite-discrete.
- **Chain 2:** our DV equality leads; `gibbs-variational` etc. for KL lemmas only.
- **Chain 3:** ⭐ `gpeyre/flow-sinkhorn` (Sinkhorn+OT) and the active Mathlib PF PR cluster (#39919/20/17).
- **Chain 4:** `brownian-motion`, `formal-mathfin` exist but immature — radar only.

## Pulling a proof into the pipeline (harness)

Mirror DKPS's `Challenge/MathlibCandidate/<Name>/`:
1. **Spec** `Conformance.lean` — imports ONLY `Mathlib`, states the leaf as `sorry` (the
   ForMathlib statements here ARE the specs; Mathlib-only iff no `ForMathlib.OT`
   vocabulary needed — Chain 3 qualifies; Chain 1's weak node uses `ForMathlib.OT`).
2. **Collect** candidates in `Leaderboard.lean`; admissible iff `#print axioms <leaf>`
   shows no `sorry`/extra axioms. **Multiple independent proofs of one leaf are welcome**
   — different imports/tactics give robustness and a golf race.
3. **Golf** the winner (Opus, `mathlib-quality`), stage in `ForMathlib/<dest>.lean`,
   rewire the paper library to consume it (as `exists_worstCase_gibbs` /
   `sinkhorn_potentials_exist` do), update `formalization.yaml` + `PROOF_PIPELINE.md`.
4. **Provenance (mandatory if adapted/vendored).** Record original author, source repo +
   **commit permalink**, license (must be Apache-2.0-compatible), and retrieval date in
   the file header + `formalization.yaml`; keep upstream notices. Verified truth never
   waives credit — see `SURVEY_LEADS.md`'s vendoring policy. Prefer re-deriving from the
   statement when the license is unclear.

### Priority order for the survey
1. ⭐ **`gpeyre/flow-sinkhorn`** — spans Chain 3 (Sinkhorn) + Chain 1-heavy (entropic-OT); best payoff if its `sorry` inventory is thin.
2. **Mathlib `label:LLM-generated` × area** + the **PF PR cluster** — Mathlib-native, composes upstream.
3. **Sion** (use now) + author the **Fenchel-conjugate layer** ourselves.
4. Chain 2 KL/DV-adjacent corpora — supplementary (our DV leads); check the DV Zulip thread.
5. Chain 1-heavy general OT & Chain 4 — defer unless reduced to finite/discrete.

---

### Change log
- **Survey integration (2026-07):** corrected Sion → ✅ (`Mathlib.Topology.Sion`); added
  [`SURVEY_LEADS.md`](SURVEY_LEADS.md) (external-artifact registry + `label:LLM-generated`
  search strategy + generated-proof corpora); noted our DV equality supersedes
  `gibbs-variational`; upgraded Chain 3 (flow-sinkhorn + PF PR cluster) and softened
  Chain 4 ("all absent" → immature external efforts exist).
- **Proved `ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost`** (Chain-1
  weak-duality per-coupling kernel; ported from `reference/V4.lean::wdro_lagrangian_bound`,
  generalized to arbitrary cost `c`). `WeakDuality.lean` is no longer a `sorry`.
- Staged `ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean` (Chain 3 top);
  `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` delegates to it (necessary
  `∑pᵢ = ∑qⱼ` hypothesis added — the statement was under-specified).
- Proved & staged `ForMathlib.MeasureTheory.Normalization`; consumed by `exists_worstCase_gibbs`.
- Proved `ChenGeorgiouPavon2021.staticSB_eq_entropicOT` (T0).
