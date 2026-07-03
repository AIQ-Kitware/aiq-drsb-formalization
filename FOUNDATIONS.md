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
        │                                    ├─► Kantorovich (OT) duality ❌ ─► Wasserstein-DRO WEAK duality ❌  ⚑ (ForMathlib/OptimalTransport/WeakDuality, staged)
Sion's minimax theorem ❌ ──────────────────┘                                          │
                                                                                       ▼
   Rockafellar interchange (∫inf = inf∫) 🟡  +  measurable selection (KRN) ❌  ─────► Wasserstein-DRO STRONG duality ❌ (the `≥` seam)
```

| Link | Mathlib | Effort | Search terms (for the survey) |
|---|---|---|---|
| Fenchel–Young inequality / convex conjugate `f*` | ❌ (no `Analysis/Convex/{Conjugate,Fenchel}`) | M | `convex conjugate`, `Legendre transform`, `Fenchel–Young`, `fenchel_young_inequality`, `convexConjugate`, Rockafellar *Convex Analysis* §12 |
| Fenchel–Rockafellar duality | ❌ | L | `Fenchel duality`, `Fenchel–Rockafellar`, `conjugate duality`, `strong duality convex`, Rockafellar Thm 31.1 |
| **Sion's minimax theorem** | ❌ (only substring false-positives) | L | `Sion minimax`, `minimax theorem`, `sInf_iSup_eq_iSup_sInf`, `sup inf = inf sup`, quasiconcave/quasiconvex, Sion 1958 |
| Kantorovich(–Rubinstein) OT duality | ❌ | XL | `Kantorovich duality`, `optimal transport duality`, `Kantorovich–Rubinstein`, `c-transform`, `Villani Optimal Transport Thm 5.10`, `EntropicOT` |
| Rockafellar interchange `∫ inf = inf ∫` | 🟡 (`lintegral` monotone-conv only) | L | `interchange integral infimum`, `Rockafellar–Wets Thm 14.60`, `normal integrand`, `decomposable space` |
| Measurable selection (Kuratowski–Ryll-Nardzewski) | ❌ | XL | `measurable selection`, `Kuratowski Ryll-Nardzewski`, `Jankov von Neumann`, `exists_measurable_selector`, `measurableSet_of_isMinOn` |

> **Payoff shortcut:** the evaluation **cards need only the WEAK-duality node** (the
> `≤`, boxed ⚑). It descends from the per-coupling Lagrangian bound alone — no minimax,
> no Kantorovich, no selection. That bound is **already proved** in `reference/V4.lean`
> (`wdro_lagrangian_bound`); it is staged (statement) at
> `ForMathlib/OptimalTransport/WeakDuality.lean` awaiting the port. The rest of Chain 1
> is only for the STRONG-duality capstones — defer.

---

## Chain 2 — Entropic / Gibbs ⇒ Sinkhorn-DRO duality  (mostly built)

Powers `WangGaoXie2023.strong_duality` (the DRSB "Eq. 47" term).

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
| Donsker–Varadhan variational formula | 🟢 **proved here** (`ForMathlib.MeasureTheory.DonskerVaradhan`) | — | `Donsker–Varadhan`, `Gibbs variational principle`, `Measure.tilted`, `variational formula relative entropy`, Dupuis–Ellis |
| cumulant generating function = log-partition | ✅ (`Probability/Moments/Basic` `cgf`) | S | `cgf`, `mgf`, `cumulant generating function`, `log ∫ exp` |
| Sinkhorn-DRO weak duality (outer `inf_λ`) | ❌ | L | `Sinkhorn distributionally robust`, `entropic DRO dual`, `KL-DRO dual`, Wang–Gao–Xie 2021 (arXiv 2109.11926) |

*This is the healthiest chain: DV + cgf give the engine; only the outer Lagrangian
assembly remains (a T3 analog of Chain 1's weak-duality node).*

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
| Perron–Frobenius (dominant eigenvalue/eigenvector of a positive matrix) | 🟡 (`Matrix/Irreducible/Defs` only) | L | `Perron Frobenius`, `dominant eigenvalue`, `positive matrix eigenvector`, `spectral radius nonneg matrix`, `Collatz–Wielandt` |
| Hilbert projective metric / Birkhoff contraction | ❌ | L | `Hilbert projective metric`, `Birkhoff contraction`, `Garrett Birkhoff`, `cone contraction` |
| **Sinkhorn–Knopp / matrix scaling (DAD)** | ❌ (staged, `sorry`) | L | `Sinkhorn Knopp`, `matrix scaling`, `RAS method`, `DAD theorem`, `Menon Schneider`, `iterative proportional fitting` |

*Purely finite-dimensional and self-contained — a strong **Fable ticket (F2)**, provable
without any measure theory. Perron–Frobenius is the reusable sub-lemma and its own
Mathlib candidate.*

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

> **Do not spend Fable cycles here.** Every link needs a Mathlib *area* that does not
> exist (`SDE`, `Girsanov`); building it is a multi-quarter upstream program. The
> statements are faithful (first pass); pending that area, record them as documented
> `axiom`s with provenance, or keep as `sorry` and treat as out-of-scope for the cards
> (they underlie `V`'s construction, not the robustness bound). Decide with the
> coordinator — needs the DRSB manuscript (AGENTS.md §2).

---

## How to run the survey (pull AI-generated proofs into the pipeline)

Mirror DKPS's `Challenge/MathlibCandidate/<Name>/` harness:

1. **Spec file** `Conformance.lean` — imports ONLY `Mathlib`, states the candidate
   leaf as `sorry` (the ForMathlib statements here ARE these specs; a candidate is
   Mathlib-only iff it needs no `ForMathlib.OT` vocabulary — Chain 3 qualifies; Chain 1's
   weak-duality node uses `ForMathlib.OT`, so port it into a self-contained statement
   first).
2. **Search** with the terms above across: Mathlib master (moving target — re-grep),
   the Lean Zulip `#mathlib4`/`#new members` archives, `leanprover-community/mathlib4`
   PRs and `Mathlib/Sandbox`, Moogle / LeanSearch / `loogle`, and any AI-proof corpora.
3. **Collect** candidate proofs in a `Leaderboard.lean` (imports the project); a proof
   is admissible iff `#print axioms <leaf>` shows no `sorry`/extra axioms.
4. **Golf** the winner to Mathlib style (Opus, `mathlib-quality` rules), stage in
   `ForMathlib/<dest path>.lean`, rewire the paper library to consume it (as
   `sinkhorn_potentials_exist` / `exists_worstCase_gibbs` already do), update
   `formalization.yaml` + `PROOF_PIPELINE.md` §3.

### Priority order for the survey
1. **Sinkhorn–Knopp / matrix scaling** + **Perron–Frobenius** (Chain 3) — self-contained,
   most likely to have existing Lean proofs, no measure theory.
2. **Sion's minimax** + **Fenchel conjugate/duality** (Chain 1 roots) — famous, plausibly
   already attempted upstream; unblock the whole DRO layer.
3. **Kantorovich duality** (Chain 1) — large; check for an in-progress Mathlib OT branch.
4. Chain 4 links — only if surveying a dedicated stochastic-analysis effort.

---

### Change log
- Staged `ForMathlib/OptimalTransport/WeakDuality.lean` (Chain 1 weak node; port from
  `reference/V4.lean`) and `ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean`
  (Chain 3 top; `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` now delegates, with
  the necessary `∑pᵢ = ∑qⱼ` mass-conservation hypothesis added).
