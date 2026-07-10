# AIQ DRSB Formalization

Lean 4 scaffold for the theorems underlying the GaTech **DRSB**
(Distributionally-Robust Schrödinger Bridge) TA1 evaluation cards. Structure mirrors
the sibling [`aiq-dkps-formalization`](../aiq-dkps-formalization): one top-level Lean
library per source paper, a paper-agnostic `ForMathlib` staging library, a
`formalization.yaml`, and prose transcriptions of every source under [`prose/`](prose/).

> 🧭 **New here — especially AI agents — start with [`AGENTS.md`](AGENTS.md).** It
> codifies *why* this exists (formalizing the GaTech MAGNET evaluation-card theorem from
> **published** DRO results), the provenance rule (the team's unpublished DRSB manuscript
> is **not a source** — ~0 weight, §2), the published-theorem chain, the working
> conventions, and the known traps. This README is just the build + library map.

> **Status → [`STATUS.md`](STATUS.md).** Deliberately not duplicated here, because it goes stale.
> In one line: the card-level DRSB inequalities and all four strong-duality equalities are proved
> dependency-clean; the live frontier is Sinkhorn **convergence** via the Birkhoff–Hopf contraction
> (`ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf*`). Two other research seams remain documented:
> the continuum Wiener/SDE path-law transport ([`PLAN_CONTINUUM_CLOSURE.md`](PLAN_CONTINUUM_CLOSURE.md))
> and the Itô/Girsanov wall behind the continuum `hCM` edge ([`ROADMAP_ENERGY_IDENTITY.md`](ROADMAP_ENERGY_IDENTITY.md)).

## What DRSB claims

DRSB certifies a distributionally-robust worst-case cost bound on a
Schrödinger-bridge / stochastic-optimal-control value function
`V(x) = 𝔼[∫₀¹ ½‖u_t‖² dt + ρ·g(X₁) | X₀ = x]`: for a source `μ` within a
Wasserstein-2 ball (`wdrsb_cost_bound.yaml`) or a Sinkhorn-divergence ball
(`sdrsb_cost_bound.yaml`) around the nominal, `𝔼_μ[V] ≤ 𝔼_worst-case[V]`. See
[`prose/README.md`](prose/README.md) for the full published-theorem chain.

## Libraries

| Library | Role | Key declarations |
|---|---|---|
| `ForMathlib` | Paper-agnostic staging: Donsker–Varadhan, shared OT/DRO vocabulary, Gaussian/Sinkhorn/KL infrastructure, and the continuum-closure sequence-model Cameron–Martin/Kakutani layer | `integral_le_klDiv_add_log_integral_exp`, `log_integral_exp_eq_sSup`; `OT.droValue`, `OT.wassersteinBall`, `OT.sinkhornBall`; `stdGaussian`, `stdSeqGaussian`, `prefixFiltration`, `cmDensityProcess`, `klDiv_stdSeqGaussian_map_add_of_summable`, `klDiv_stdSeqGaussian_map_add_eq_top_iff_not_summable` |
| `ChenGeorgiouPavon2021` | SB ⇄ SOC ⇄ entropic-OT; value function + optimal control; CGP-facing sequence-model energy wrappers | `SBData`, `schrodingerBridge_KL_eq_SOC`, `energy_identity_sequenceModel`, `energy_identity_sequenceModel_top_iff_not_summable`, `optimal_control_eq_grad_log`, `optimal_control_eq_neg_grad_value`, `staticSB_eq_entropicOT` |
| `BlanchetMurthy2019` | Wasserstein-DRO strong duality (primary) | `wdro_strong_duality`, `Lc` |
| `GaoKleywegt2023` | Wasserstein-DRO strong duality + worst-case distribution | `weak_duality_prop1`, `strong_duality_thm1`, `worstCase_structure_cor1`, `dataDriven_worstCase_cor2ii` |
| `MohajerinEsfahaniKuhn2018` | Data-driven Wasserstein-DRO reformulation | `worstCaseExpectation_eq_dual`, `worstCase_program`, `worstCase_exists` |
| `WangGaoXie2023` | Sinkhorn-DRO log-partition dual (SDRSB card's bound) | `strong_duality`, `sinkhornDualObjective`, `logPartition`, `exists_worstCase_gibbs` |
| `Drsb` | **Capstone** — the card claims composed from the above | `wdrsb_cost_bound`, `sdrsb_cost_bound`, `sdrsbTerminalBound` |

Each `<Library>/Basic.lean` docstring cites the prose file + printed theorem/equation
number every declaration corresponds to.

## Layout

```text
.
├── ForMathlib.lean / ForMathlib/     # DV + OT/DRO staging (import: Mathlib only)
├── <Paper>.lean / <Paper>/           # one library per source paper (import: Mathlib + ForMathlib)
│   └── ChenGeorgiouPavon2021/        # split into Core, EnergyIdentity, SequenceGaussian,
│       └── Continuum/                # RealPath, IntervalPath, Wiener/*, Closure frontiers
├── Drsb.lean / Drsb/                 # capstone (imports the paper libraries)
├── prose/                            # faithful transcriptions of every source (papers/ = PDFs, git-ignored)
├── reference/                        # ⚠ OLD, trap-laden attempts — reference-only, NOT built
├── formalization.yaml               # project metadata (sources, targets, status, libraries)
├── lakefile.toml / lake-manifest.json / lean-toolchain
```

## Vendored / adapted external proofs

Verified truth does not waive credit — every reused external proof is attributed here,
in its file header, and in `formalization.yaml` (per the vendoring policy at the top of
[`SURVEY_LEADS.md`](SURVEY_LEADS.md)).

| Vendored declaration(s) | Source | Commit | License |
|---|---|---|---|
| `ForMathlib.MeasureTheory.{stdGaussian, klDiv_gaussianReal_shift, klDiv_map_measurableEquiv, klDiv_prod, klDiv_pi, klDiv_pi_fintype, klDiv_stdGaussian_map_add}` (Cameron–Martin relative entropy `KL(N(·+h) ‖ N) = ½‖h‖²`) | Michael R. Douglas, [`mrdouglasny/gibbs-variational`](https://github.com/mrdouglasny/gibbs-variational) · `GibbsVariational/GaussianEntropy.lean` | [`75e08d8`](https://github.com/mrdouglasny/gibbs-variational/blob/75e08d8aaca83bb090fc43855898991fbfc9abf3/GibbsVariational/GaussianEntropy.lean) | Apache-2.0 |

Vendored verbatim (only the enclosing namespace was changed, `GibbsVariational →
ForMathlib.MeasureTheory`), retrieved 2026-07-03, dependency-clean under our Mathlib pin. The
Euler–Maruyama discrete energy identity built on it (`emShift`, `emEnergy`,
`klDiv_emShift_eq_emEnergy`, consumed by `ChenGeorgiouPavon2021.energy_identity_euler_maruyama`)
is original to this repo — it proves the discrete/Gaussian layer of CGP's control-energy
identity (4.19), the quantity the DRSB card actually measures (AGENTS §3).

`reference/` is quarantined (see [reference/README.md](reference/README.md)) and is
not a `lean_lib`, so `lake build` ignores it. It holds the earlier hand-written
attempts — useful for salvage (e.g. the *proved* Donsker–Varadhan / Hoeffding lemmas
in `reference/WellKnown.lean`) but **not canon**; re-derive every statement from
`prose/`, not from `reference/`.

## Build

Toolchain `leanprover/lean4:v4.32.0-rc1`; Mathlib pinned in `lake-manifest.json`.

```bash
lake exe cache get      # download prebuilt Mathlib oleans
lake build              # full project check
```

## Next steps

Follow [`PLAN_CONTINUUM_CLOSURE.md`](PLAN_CONTINUUM_CLOSURE.md). The sequence-coordinate
Cameron–Martin/Kakutani theorem is now complete and should be treated as a checkpointed
milestone:

```bash
# These files are aggregate imports over split theorem modules; build imports first.
lake build ForMathlib
lake env lean ForMathlib/MeasureTheory/GaussianCameronMartin.lean
lake build ChenGeorgiouPavon2021
lake env lean ChenGeorgiouPavon2021/Basic.lean
lake build
```

For the split-module smoke test, the equivalent one-command wrapper is:

```bash
dev/check_cgp_module_split.sh
```

The next mathematical frontier is not more sequence-model KL plumbing. A finite-dimensional
Wiener/dyadic layer is now green: Brownian dyadic increment laws, normalization to iid
standard Gaussians, finite product-law assembly, shifted finite-grid density formulas, and
finite dyadic absolute continuity are all available at the CGP-facing layer.

The remaining bridge is the **continuum path-space closure**: choose a canonical interval
path carrier, prove that the dyadic/projected filtration generates that carrier's path
sigma-algebra, prove KL exhaustion along those projections, and prove Cameron--Martin
path-space quasi-invariance / density closure. Do not revive the overstrong claim that dyadic
increments on `[0,1]` generate all of `RealPath := ℝ → ℝ`; in the current green code those
continuum facts are explicit interfaces (`HasDyadicKLExhaustion` and path-space absolute
continuity), not hidden placeholders.

## Project theorem-target progress bar

The 2026-07-08 theorem-target scaffold collects the remaining DRSB mathematics under:

```lean
import ChenGeorgiouPavon2021.ProjectTheoremTargets
```

Its modules were originally staged with executable placeholders as a project-wide progress bar.
**They have since been converted to hypothesis/structure interfaces and now carry zero open goals** —
so this scaffold is no longer the progress bar. Assembly lemmas consume those interfaces and remain
proof-bearing.

For the live open-goal inventory (and the frontier they belong to), see [`STATUS.md`](STATUS.md), or
just run the grep:

```bash
grep -rn --include=*.lean --exclude-dir=.lake --exclude-dir=.reference-clones --exclude-dir=reference -w sorry .
```

(Lean comments in this repo never contain that word — see `AGENTS.md` §5 — so the match is exact.)
