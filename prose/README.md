# DRSB prose — the published argument chain

This folder transcribes the **chain of core mathematical arguments** behind the
GaTech **Distributionally-Robust Schrödinger Bridge (DRSB)** evaluation cards, from
the *published* theorems each link rests on. It mirrors the `prose/` convention of
the sibling `aiq-dkps-formalization` repo: one faithful, math-carrying transcription
per source, kept next to the Lean development so a formalizer can check statements
without chasing PDFs.

> **What this chain anchors on.** The **published** theorems each link rests on, plus the
> **MAGNET eval cards** in `ta1/GaTech-DRSBM/magnet_eval/cards/`. The GaTech team's own
> DRSB manuscript (referenced in code as `project: drsbm_paper`, "Eq. 47", "Algorithm 5:
> Relaxed Schrödinger Bridge") is an **unpublished team document that is NOT a source
> here** — it carries ~0 weight and was wrong; do not chase or cite it. Code labels like
> "Eq. 47" are mentioned only to point at the card's bound formula, whose backing is the
> published Wang–Gao–Xie dual.

## What DRSB claims

DRSB trains a Schrödinger-bridge / stochastic-optimal-control (SOC) generative model
and certifies a **distributionally-robust worst-case cost bound** on its value
function
$$
V(x) \;=\; \mathbb E\!\left[\int_0^1 \tfrac12\|u_t\|^2\,dt \;+\; \rho\,g(X_1)\;\middle|\; X_0 = x\right].
$$
The two evaluation cards assert, for perturbations of the source distribution:
$$
\mathbb E_{\mu}[V(x)] \;\le\; \mathbb E_{\text{worst-case}}[V(x)],
$$
where the ambiguity set around the nominal $p_0$ is a **Wasserstein-2 ball**
(`wdrsb_cost_bound.yaml`) or a **Sinkhorn-divergence ball** (`sdrsb_cost_bound.yaml`).
The SDRSB card's bound is
$\;\text{Bound} = \mathbb E_{\text{wc}}[V] - \rho\,\log\mathbb E_\nu[e^{g(X_1)}]\;$ — an
entropic **log-partition** term (backed by Wang–Gao–Xie; the GaTech code labels it "Eq. 47").

## The chain, link by link

Read top-to-bottom: each row is one step of the DRSB reduction, the prose file that
transcribes it, the published theorem(s) it rests on, and the `V4.lean` (namespace
`DRSB`) declaration it grounds.

| # | Link in the DRSB argument | Prose file | Published anchor(s) | `V4.lean` decl |
|---|---|---|---|---|
| 1 | **SB ⇄ SOC ⇄ entropic-OT**, define $V$, optimal control $u^\*=\nabla\log\varphi$ (Hopf–Cole / Fleming) | [schrodinger-bridge-soc-ot.md](schrodinger-bridge-soc-ot.md) | Chen–Georgiou–Pavon (2005.10963) Prob. 4.3 / Thm 5.2; Léonard (1308.0215) Thm 5.2 (Γ→OT) | `schrodingerBridgeValue`, `socObjective`/`socValue`, `V0`, `optimal_control_eq_neg_grad_value` |
| 2 | **Matching estimator** that produces the bridge, $u$, and terminal net $g$ | [sb-matching-generative.md](sb-matching-generative.md) | DSBM (2303.16852) Thm 8 + Alg. 1; GSBM (2310.02233) obj. (3), soft-terminal SOC (16a–b), Alg. 5; Adjoint Matching (2409.08861) Thm 1, loss (37)–(39) | `Dynamics`, `Control`, `Psi` (abstract); code's `AdjointMatcher`, `BridgeMatcher` |
| 3W | **Wasserstein-DRO strong duality**: $\sup_{W_2^2\le\varepsilon}\mathbb E_\mu[\Psi]=\inf_{\lambda\ge0}\{\lambda\varepsilon+\mathbb E_{\hat\mu}[\sup_x(\Psi(x)-\lambda\|x-\hat x\|^2)]\}$ | [wasserstein-dro-duality.md](wasserstein-dro-duality.md) | Blanchet–Murthy (1604.01446) Thm 1 + Rmk 1 eq. (9); Gao–Kleywegt (1604.02199) Thm 1, Cor 1(ii)/Cor 2; Esfahani–Kuhn (1505.05116) Thm 4.2/4.4 | `wassersteinBall`, `W2sq`, `wdro_lagrangian_bound` (✅ proved, `≤`), `wdro_dual` (placeholder, `≥`), `L_wdro`, `wdrsbDualObjective` |
| 3S | **Sinkhorn-DRO strong duality**: `sup_x` becomes the **log-partition** $\lambda\kappa\log\int e^{(\Psi-\lambda\|\cdot\|^2)/(\lambda\kappa)}$; worst case is a **continuous Gibbs tilt** (the SDRSB card's bound term) | [sinkhorn-dro-duality.md](sinkhorn-dro-duality.md) | Wang–Gao–Xie (2109.11926) Def. 1, **Thm 1** (Strong Duality I–IV), Rmk 4 | `sinkhornBall`, `Wkappa`, `sinkhornObjective`, `sdro_dual` (placeholder, outer `≥`), `M_logPartition`, `gibbsUnnormalized`, `exists_worstCase_gibbsKernel`, `drsbValue_SDRO` |
| ★ | **Root under the Sinkhorn dual (3S)** — Donsker–Varadhan / Gibbs variational formula; entropy-constrained worst case is the tilt $\propto e^{f/\lambda}$ | [kl-dro-gibbs-donsker-varadhan.md](kl-dro-gibbs-donsker-varadhan.md) | Donsker–Varadhan; Dupuis–Ellis; Hu–Hong (KL-DRO); Ben-Tal et al. (φ-div DRO) | `WellKnown.integral_le_klDiv_add_log_integral_exp`, `isGreatest_donskerVaradhan`, `log_integral_exp_eq_sSup` (all ✅ proved) |

Steps **1 → 2** build the object $V$ (and $g$); steps **3W / 3S** are the actual
card claim (worst-case cost bound); the **★** root is the single fact under the
Sinkhorn dual.

## What the Lean scaffold already proves vs. assumes

The scaffolds are *old attempts, not canon* (per the coordinator) — but they pin down
exactly which links are the hard ones:

- **Proved (no placeholder, no extra dependencies):** the Donsker–Varadhan family in
  `WellKnown.lean` (`integral_le_klDiv_add_log_integral_exp`,
  `isGreatest_donskerVaradhan`, `log_integral_exp_eq_sSup`) and the WDRO
  **weak-duality** direction `wdro_lagrangian_bound` (the `≤` half that the card's
  inequality actually rests on).
- **Left as placeholder (the genuinely hard seam):** the **strong-duality `≥` direction**
  of both `wdro_dual` and `sdro_dual`. Both require constructing the worst-case
  measure via an optimal-transport measurable-selection / argmax argument
  (Gao–Kleywegt / Blanchet–Murthy for W; the Gibbs tilt for S) — machinery not in
  Mathlib. The prose files ([wasserstein…](wasserstein-dro-duality.md) §worst-case,
  [sinkhorn…](sinkhorn-dro-duality.md) Rmk 4) transcribe exactly the published
  results a formalization of that direction would follow.

## Symbol-convention warning (Sinkhorn)

Wang–Gao–Xie use **$\varepsilon$ = entropic regularizer** and **$\rho$ = ball
radius** — the *reverse* of naming intuition, and both collide with DRSB's own
$\rho$ (terminal-cost weight) and $\varepsilon$ (perturbation budget). The Lean
scaffold uses `kappa` for the regularizer and `eps` for the radius. See the mapping
table in [sinkhorn-dro-duality.md](sinkhorn-dro-duality.md) before porting any
symbol.

## Sources (PDFs in `papers/`, git-ignored — never committed)

Downloaded with `curl https://arxiv.org/pdf/<id>`; `.gitignore` excludes
`prose/papers/*.pdf` and `*.pdf`. To refresh, re-download by arXiv id:

**Schrödinger bridge / SOC / OT**
- Chen, Georgiou, Pavon — *Stochastic control liaisons: Sinkhorn meets Monge on a Schrödinger bridge* — SIAM Review 2021 — [arXiv:2005.10963](https://arxiv.org/abs/2005.10963)
- Léonard — *A survey of the Schrödinger problem and its connections with optimal transport* — 2013 — [arXiv:1308.0215](https://arxiv.org/abs/1308.0215)

**Schrödinger-bridge matching (the estimator)**
- Shi, De Bortoli, Campbell, Doucet — *Diffusion Schrödinger Bridge Matching* (DSBM) — NeurIPS 2023 — [arXiv:2303.16852](https://arxiv.org/abs/2303.16852)
- Liu, Lipman, Nickel, Karrer, Theodorou, Chen — *Generalized Schrödinger Bridge Matching* (GSBM) — ICLR 2024 — [arXiv:2310.02233](https://arxiv.org/abs/2310.02233)
- Domingo-Enrich, Drozdzal, Karrer, Chen — *Adjoint Matching: Fine-tuning … with Memoryless SOC* — ICLR 2025 — [arXiv:2409.08861](https://arxiv.org/abs/2409.08861)

**Distributionally-robust optimization (the worst-case bound)**
- Blanchet, Murthy — *Quantifying Distributional Model Risk via Optimal Transport* — Math. of OR 2019 — [arXiv:1604.01446](https://arxiv.org/abs/1604.01446)
- Gao, Kleywegt — *Distributionally Robust Stochastic Optimization with Wasserstein Distance* — Math. of OR 2023 — [arXiv:1604.02199](https://arxiv.org/abs/1604.02199)
- Mohajerin Esfahani, Kuhn — *Data-driven DRO Using the Wasserstein Metric* — Math. Prog. 2018 — [arXiv:1505.05116](https://arxiv.org/abs/1505.05116)
- Wang, Gao, Xie — *Sinkhorn Distributionally Robust Optimization* — Operations Research 2023 — [arXiv:2109.11926](https://arxiv.org/abs/2109.11926)

**Classical (books / non-arXiv, cited not transcribed):** Donsker–Varadhan (CPAM
1975–83); Dupuis–Ellis, *A Weak Convergence Approach to Large Deviations* (1997);
Ben-Tal et al., *Robust Solutions … Uncertain Probabilities* (Mgmt. Sci. 2013);
Hu–Hong, *KL-Divergence Constrained DRO* (2013).

## Provenance & caveats

- The GaTech team's own DRSB manuscript is **not a source** for this formalization and
  carries **~0 weight** (it was wrong). Its internal "Eq. 47" / "Algorithm 5" labels come
  only from GaTech code comments — never cite them as canonical, and do not treat "confirm
  against the manuscript" as an action item. The anchor is the card + the published papers.
- The card claim text and the "Gaussian worst-case shift" closed form come from
  `ta1/GaTech-DRSBM` code, not from any of the transcribed papers; the papers supply
  the *structure* (transport map / Gibbs tilt) that makes that closed form exact.
- The `V4.lean`/`V1.lean` declaration names are the *current scaffold's*; the
  coordinator has noted these are reference-only old attempts. This prose is intended
  to guide a fresh, canonical formalization, not to bless the scaffold.
