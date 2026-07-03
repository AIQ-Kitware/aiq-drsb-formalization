# Donsker–Varadhan, the Gibbs worst-case measure, and KL/φ-divergence DRO

**Sources (this is connective tissue — the shared root beneath the Sinkhorn-DRO dual).** The
Donsker–Varadhan (DV) variational formula and the Gibbs / exponential-tilting
worst-case measure are classical and appear in books rather than a single arXiv
paper; the KL- and φ-divergence DRO specializations are journal papers. Nothing
here needs a downloaded PDF; the primary references are:

- M. D. Donsker, S. R. S. Varadhan. *Asymptotic evaluation of certain Markov
  process expectations for large time, I–IV.* Comm. Pure Appl. Math. (1975–1983).
  — origin of the variational formula.
- P. Dupuis, R. S. Ellis. *A Weak Convergence Approach to the Theory of Large
  Deviations.* Wiley, 1997. — the DV / Laplace-principle variational formula in the
  form used below (Prop. 1.4.2).
- A. Ben-Tal, D. den Hertog, A. De Waegenaere, B. Melenberg, G. Rennen. *Robust
  Solutions of Optimization Problems Affected by Uncertain Probabilities.*
  Management Science 59(2), 2013. — φ-divergence DRO; the conjugate-duality form.
- Z. Hu, L. J. Hong. *Kullback–Leibler Divergence Constrained Distributionally
  Robust Optimization.* Optimization-Online, 2013. — the KL-ball worst-case is a
  Gibbs (exponential-tilting) measure; the `log E[exp]` dual.

> **Role in the DRSB chain.** DV is the *single mathematical fact* that the
> Sinkhorn-DRO entropic dual / "Eq. 47" log-partition term
> ([sinkhorn-dro-duality.md](sinkhorn-dro-duality.md)) is built on. It also names the
> *shape of the worst-case distribution*: whenever an
> ambiguity set is controlled by relative entropy (a KL ball, or the entropic inner
> layer of a Sinkhorn ball), the worst-case measure is a **Gibbs tilt**
> $dP^\star \propto e^{f/\lambda}\, dP_0$. This is exactly the DRSB
> `GibbsKernel` / `exists_worstCase_gibbsKernel` and the code's Gaussian worst-case
> draw $\tilde X_0 \sim \mathcal N\!\big(x_0 - u_0/(2\lambda),\,(\kappa/2) I\big)$.

---

## 1. The Donsker–Varadhan variational formula

Fix a probability measure $\nu$ (the *reference* / prior) on a measurable space
$\mathcal X$ and a measurable $f:\mathcal X\to\mathbb R$ with $e^{f}$ integrable
under $\nu$. Write $\mathrm{KL}(\mu\Vert\nu)=\int \log\frac{d\mu}{d\nu}\,d\mu$ for
$\mu\ll\nu$.

**DV inequality (change-of-measure / Gibbs inequality form).** For every
probability measure $\mu\ll\nu$ with $f\in L^1(\mu)$,
$$
\int f\,d\mu \;\le\; \mathrm{KL}(\mu\Vert\nu) \;+\; \log\!\int e^{f}\,d\nu.
\tag{DV-ineq}
$$

**DV variational (Gibbs) form.** The bound is tight, and the supremum is attained
at the $f$-*tilted* (Gibbs) measure $\nu_f := \nu.\mathrm{tilted}\,f$, defined by
$\frac{d\nu_f}{d\nu}(x)=\dfrac{e^{f(x)}}{\int e^{f}\,d\nu}$:
$$
\log\!\int e^{f}\,d\nu
\;=\;
\sup_{\mu\ll\nu}\Big(\int f\,d\mu \;-\; \mathrm{KL}(\mu\Vert\nu)\Big),
\qquad\text{attained at }\mu=\nu_f.
\tag{DV-var}
$$

**Proof argument.** Tilt $\nu$ by $f$. Gibbs' inequality gives
$\mathrm{KL}(\mu\Vert\nu_f)\ge 0$. Expanding the log-likelihood ratio,
$\log\frac{d\nu_f}{d\nu}=f-\log Z$ with normalizer $Z=\int e^f d\nu$, so
$\mathrm{KL}(\mu\Vert\nu_f)=\mathrm{KL}(\mu\Vert\nu)-\int f\,d\mu+\log Z\ge 0$,
which is (DV-ineq). Taking $\mu=\nu_f$ makes the KL term vanish and turns the
inequality into the equality (DV-var). $\qquad\blacksquare$

**Formalized in this repo.** These are proved (no `sorry`, no extra axioms) in
[`WellKnown.lean`](../WellKnown.lean):

| Statement | Lean declaration |
|---|---|
| (DV-ineq) | `WellKnown.integral_le_klDiv_add_log_integral_exp` |
| tilt attains the bound | `WellKnown.integral_tilted_sub_klDiv_tilted` |
| (DV-var) as an `IsGreatest` | `WellKnown.isGreatest_donskerVaradhan` |
| (DV-var) as an `sSup` identity | `WellKnown.log_integral_exp_eq_sSup` |

The `V4.lean` `donsker_varadhan` lemma consumes the `sSup` form.

---

## 2. The Gibbs measure is the entropy-constrained worst case

Rewrite (DV-var) by introducing a temperature $\lambda>0$ (apply it to $f/\lambda$
and multiply by $\lambda$):
$$
\lambda\,\log\!\int e^{f/\lambda}\,d\nu
\;=\;
\sup_{\mu\ll\nu}\Big(\int f\,d\mu - \lambda\,\mathrm{KL}(\mu\Vert\nu)\Big).
\tag{2.1}
$$
The right-hand side is the **Lagrangian relaxation** of the entropy-*constrained*
worst-case expectation
$$
\sup_{\mu:\ \mathrm{KL}(\mu\Vert\nu)\le \rho}\ \int f\,d\mu ,
\tag{2.2}
$$
with $\lambda$ the multiplier of the constraint $\mathrm{KL}\le\rho$. Strong duality
(concavity in $\mu$, Slater) gives
$$
\sup_{\mathrm{KL}(\mu\Vert\nu)\le\rho}\int f\,d\mu
=\inf_{\lambda>0}\Big\{\lambda\rho + \lambda\log\!\int e^{f/\lambda}\,d\nu\Big\},
\tag{2.3}
$$
and the maximizer of (2.2) is the Gibbs tilt
$$
\frac{d\mu^\star}{d\nu}(x)\;\propto\;\exp\!\big(f(x)/\lambda^\star\big).
\tag{2.4}
$$
This is the **KL-DRO** worst-case (Hu–Hong 2013; the φ-divergence generalization
is Ben-Tal et al. 2013 with $\varphi=t\log t$). The dual objective is a
**log-partition / soft-max** functional of $f$ — the same shape that reappears, one
transport layer out, as the Sinkhorn-DRO dual and the DRSB "Eq. 47" term.

**Formalized shape in this repo.** The tilted-measure worst case and the
log-partition object are named in [`V4.lean`](../V4.lean):

| Object (this file) | Lean declaration | Note |
|---|---|---|
| Gibbs tilt $\mu^\star\propto e^{f/\lambda}\nu$ | `DRSB.GibbsKernel`, `DRSB.gibbsUnnormalized` | the worst-case conditional |
| existence of the Gibbs worst case | `DRSB.exists_worstCase_gibbsKernel` | — |
| $\lambda\log\int e^{f/\lambda}\,d\nu$ | `DRSB.M_logPartition` | the soft-max / "Eq. 47" term |

---

## 3. Why this sits under the Sinkhorn-DRO result

**Sinkhorn-DRO / Eq. 47.** A Sinkhorn ball is an entropic-OT ball: its inner
layer conditions the transported mass through a reference kernel and penalizes it
by relative entropy. Dualizing that inner layer is exactly (2.3), which is why the
Sinkhorn-DRO dual (Wang–Gao–Xie) carries a
$\lambda\kappa\,\mathbb E_{\hat P}\big[\log \mathbb E_{\zeta}\,e^{f(\zeta)/(\lambda\kappa)}\big]$
term and a **continuous, full-support** Gibbs worst case — in contrast to the
*discrete* worst case of plain Wasserstein DRO
([wasserstein-dro-duality.md](wasserstein-dro-duality.md)). The DRSB "Eq. 47"
bound $\;\mathrm{Bound}=\mathbb E_{\text{wc}}[V]-\rho\log\mathbb E_\nu[e^{g(X_1)}]\;$
is this log-partition term with $f=g$, $\nu$ the terminal reference $\nu$, and
$\lambda$ absorbed into $\rho$. See [sinkhorn-dro-duality.md](sinkhorn-dro-duality.md).

---

## 4. Correspondence summary

| Chain object | Where it is the *worst case* | Lean |
|---|---|---|
| DV inequality $\int f\,d\mu \le \mathrm{KL}+\log\int e^f$ | change of measure in the entropic dual | `integral_le_klDiv_add_log_integral_exp` |
| DV identity $\log\int e^f = \sup_\mu(\int f - \mathrm{KL})$ | entropic dual | `log_integral_exp_eq_sSup`, `isGreatest_donskerVaradhan` |
| Gibbs tilt $\propto e^{f/\lambda}$ | KL- and Sinkhorn-ball worst case | `GibbsKernel`, `exists_worstCase_gibbsKernel` |
| $\lambda\log\int e^{f/\lambda}$ | SDRO dual / DRSB Eq. 47 | `M_logPartition`, `sdro_dual` |

**Caveat.** The classical references (Donsker–Varadhan; Dupuis–Ellis; Ben-Tal et
al.; Hu–Hong) are cited from the standard literature, not transcribed from a
downloaded PDF. The Lean statements in `WellKnown.lean` are the authoritative,
machine-checked forms of (DV-ineq)/(DV-var) as used by the DRSB scaffold.
