# AIQ DRSB Formalization

Lean 4 scaffold for the theorems underlying the GaTech **DRSB**
(Distributionally-Robust Schrödinger Bridge) TA1 evaluation cards. Structure mirrors
the sibling [`aiq-dkps-formalization`](../aiq-dkps-formalization): one top-level Lean
library per source paper, a paper-agnostic `ForMathlib` staging library, a
`formalization.yaml`, and prose transcriptions of every source under [`prose/`](prose/).

> 🧭 **New here — especially AI agents — start with [`AGENTS.md`](AGENTS.md).** It
> codifies *why* this exists (formalizing MAGNET evaluation cards), the crucial
> provenance caveats (the DRSB manuscript is unpublished), the published-theorem chain,
> the working conventions, and the known traps. This README is just the build + library
> map.

> **Status: first-pass scaffold — statements, proofs just starting.** Each theorem is
> stated close to its published form; most bodies are still `sorry`, with the
> Donsker–Varadhan family in `ForMathlib` now proved (axiom-clean). The project
> `lake build`s green.

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
| `ForMathlib` | Paper-agnostic staging: Donsker–Varadhan + shared OT/DRO vocabulary | `integral_le_klDiv_add_log_integral_exp`, `log_integral_exp_eq_sSup`; `OT.droValue`, `OT.wassersteinBall`, `OT.sinkhornBall`, `OT.otCost`, `OT.expect`, `OT.klReal` |
| `ChenGeorgiouPavon2021` | SB ⇄ SOC ⇄ entropic-OT; value function + optimal control | `SBData`, `schrodingerBridge_KL_eq_SOC`, `optimal_control_eq_grad_log`, `optimal_control_eq_neg_grad_value`, `staticSB_eq_entropicOT` |
| `BlanchetMurthy2019` | Wasserstein-DRO strong duality (primary) | `wdro_strong_duality`, `Lc` |
| `GaoKleywegt2023` | Wasserstein-DRO strong duality + worst-case distribution | `weak_duality_prop1`, `strong_duality_thm1`, `worstCase_structure_cor1`, `dataDriven_worstCase_cor2ii` |
| `MohajerinEsfahaniKuhn2018` | Data-driven Wasserstein-DRO reformulation | `worstCaseExpectation_eq_dual`, `worstCase_program`, `worstCase_exists` |
| `WangGaoXie2023` | Sinkhorn-DRO log-partition dual (DRSB "Eq. 47") | `strong_duality`, `sinkhornDualObjective`, `logPartition`, `exists_worstCase_gibbs` |
| `Drsb` | **Capstone** — the DRSB claims composed from the above | `wdrsb_cost_bound`, `sdrsb_cost_bound`, `eq47Bound` |

Each `<Library>/Basic.lean` docstring cites the prose file + printed theorem/equation
number every declaration corresponds to.

## Layout

```text
.
├── ForMathlib.lean / ForMathlib/     # DV + OT/DRO staging (import: Mathlib only)
├── <Paper>.lean / <Paper>/           # one library per source paper (import: Mathlib + ForMathlib)
├── Drsb.lean / Drsb/                 # capstone (imports the paper libraries)
├── prose/                            # faithful transcriptions of every source (papers/ = PDFs, git-ignored)
├── reference/                        # ⚠ OLD, trap-laden attempts — reference-only, NOT built
├── formalization.yaml               # project metadata (sources, targets, status, libraries)
├── lakefile.toml / lake-manifest.json / lean-toolchain
```

`reference/` is quarantined (see [reference/README.md](reference/README.md)) and is
not a `lean_lib`, so `lake build` ignores it. It holds the earlier hand-written
attempts — useful for salvage (e.g. the *proved* Donsker–Varadhan / Hoeffding lemmas
in `reference/WellKnown.lean`) but **not canon**; re-derive every statement from
`prose/`, not from `reference/`.

## Build

Toolchain `leanprover/lean4:v4.31.0-rc2`; Mathlib pinned in `lake-manifest.json`.

```bash
lake exe cache get      # download prebuilt Mathlib oleans
lake build              # builds green; every leaf emits one `sorry` warning
```

## Next steps

1. Expert review of the statements against the primary sources (`prose/` + PDFs).
2. Begin proofs, foundational libraries first (DV → Sinkhorn dual → capstone). The
   Donsker–Varadhan family is already ported into `ForMathlib` (proved, axiom-clean).
