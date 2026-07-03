# Sinkhorn DRO: Strong Duality and the Gibbs Worst-Case Distribution

> Prose reference for the Lean 4 formalization in `V4.lean` (namespace `DRSB`).
> This file transcribes the **Sinkhorn-DRO strong-duality theorem** and its
> **log-partition / soft-max dual** together with the **Gibbs (exponential-tilting)
> worst-case distribution**. These are the source facts behind the Sinkhorn
> variant (SDRSB) of the GaTech "Distributionally-Robust Schrödinger Bridge"
> paper — specifically its entropic **"Eq. 47"** worst-case cost bound.

## Sources

- **Paper:** Jie Wang, Rui Gao, Yao Xie, *"Sinkhorn Distributionally Robust
  Optimization,"* Operations Research (2023).
- **arXiv:** [arXiv:2109.11926](https://arxiv.org/abs/2109.11926) (this transcription
  is against **v5**, `[math.OC]`, 26 Mar 2025).
- **Local PDF (not committed):**
  `prose/papers/wang-gao-xie-2023_sinkhorn-distributionally-robust-optimization__arXiv-2109.11926.pdf`
  (text extracted via `pdftotext`).

All quoted equation/theorem numbers below are **as printed in the arXiv v5 PDF**.
Symbols are the paper's own unless a paraphrase is explicitly flagged.

---

## Role in the DRSB chain

This paper is the **source for the SDRSB "Eq. 47" / log-partition term**. The DRSB
worst-case cost bound in its Sinkhorn variant replaces the Wasserstein ambiguity
ball with a **Sinkhorn (entropic-OT) ball**; the entropic regularization turns the
Wasserstein dual's pointwise `sup_x` into an **entropic soft-max / log-sum-exp
(log-partition)** term, and turns the discrete Wasserstein worst-case (a finitely
supported measure) into a **continuous, full-support Gibbs / exponential-tilt
conditional**. Concretely, this paper's dual objective (its Eq. `(1)`/`(Dual)`)

$$V_D=\inf_{\lambda\ge 0}\Big\{\lambda\rho+\lambda\epsilon\,\mathbb E_{x\sim\hat P}\big[\log \mathbb E_{z\sim\nu}\,e^{(f(z)-\lambda c(x,z))/(\lambda\epsilon)}\big]\Big\}$$

is exactly the shape of the DRSB **Eq. 47** worst-case bound
$\ \text{Bound}=\mathbb E_{\text{worst-case}}[V(x)]-\rho\log\mathbb E_\nu[e^{g(X_1)}]$
(the entropic **log-partition** term), and this paper's worst-case density (Remark 4)

$$\frac{\mathrm d\gamma_x^*}{\mathrm d\nu}(z)\ \propto\ \exp\!\big((f(z)-\lambda^* c(x,z))/(\lambda^*\epsilon)\big)$$

is exactly the DRSB code's **Gaussian worst-case tilt**
$\tilde X_0\sim\mathcal N\!\big(x_0-\tfrac{u_0}{2\lambda},\tfrac{\kappa}{2}I\big)$
(see the correspondence section for the completion-of-square that makes the
quadratic-cost Gibbs measure Gaussian). This file therefore underwrites
`M_logPartition`, `sdro_dual`, `GibbsKernel`, `gibbsUnnormalized`,
`exists_worstCase_gibbsKernel`, and `drsbValue_SDRO`, and the
`sdrsb_cost_bound.yaml` card claim.

---

## Setup and notation

Let $\mathcal Z$ be a measurable space; $P,Q\in\mathcal P(\mathcal Z)$ probability
measures; $\mu,\nu\in\mathcal M(\mathcal Z)$ two **reference measures** with
$P\ll\mu$, $Q\ll\nu$. Symbol dictionary (paper $\to$ role):

| Paper symbol | Meaning | Lean / DRSB analogue |
|---|---|---|
| $\epsilon\ge 0$ | **entropic regularization** level of the Sinkhorn distance | `kappa` (κ) in `V4.lean`; κ in DRSB |
| $\rho$ | **Sinkhorn ball radius** (ambiguity radius) | `eps` (ε) in `V4.lean`; the DRSB `ρ` coefficient of Eq. 47 |
| $\lambda\ge 0$ | Lagrange multiplier for the ball constraint | `lam` |
| $\hat P$ | nominal (data / empirical) distribution | `muhat` |
| $\nu$ | reference measure the worst-case is a.c. w.r.t. (Lebesgue/Gaussian/counting) | `base : Measure X` |
| $\mu$ | first reference measure; paper takes $\mu=\hat P$ | (folded into `muhat`) |
| $f$ | loss function on $\mathcal Z$ | `Psi0` (Ψ), i.e. DRSB value $V$ / terminal cost $g$ |
| $c(x,z)$ | transport cost | quadratic $\lVert x-z\rVert^2$ |
| $\Gamma(P,Q)$ | couplings with marginals $P,Q$ | `Couplings mu nu` |
| $H(\gamma\mid\mu\otimes\nu)$ | relative entropy (KL) of $\gamma$ vs $\mu\otimes\nu$ | `KLM (pi) (prodMeasure …)` |

**Note the symbol swap** the reader must keep straight: in the *paper*, $\epsilon$
is the **regularizer** and $\rho$ is the **radius**; in the DRSB/Lean scaffold,
`kappa` is the regularizer and `eps` is the radius. So *paper* $\epsilon\leftrightarrow$
*Lean* `kappa`, and *paper* $\rho\leftrightarrow$ *Lean* `eps`. (Additionally, in
`M_logPartition` the Lean integration variable `x` plays the role of the paper's
worst-case point `z`, while Lean `xhat` plays the paper's nominal point `x`.)

### Definition 1 (Sinkhorn distance) — as printed

> **Definition 1 (Sinkhorn Distance).** For regularization parameter $\epsilon\ge 0$,
> the Sinkhorn distance between $P$ and $Q$ is
> $$W_\epsilon(P,Q)=\inf_{\gamma\in\Gamma(P,Q)}\ \mathbb E_{(x,y)\sim\gamma}[c(x,y)]+\epsilon\,H(\gamma\mid\mu\otimes\nu),$$
> where $H(\gamma\mid\mu\otimes\nu)=\mathbb E_{(x,y)\sim\gamma}\!\big[\log\frac{\mathrm d\gamma(x,y)}{\mathrm d\mu(x)\,\mathrm d\nu(y)}\big]$.

This is entropic-regularized OT: the ordinary transport cost plus $\epsilon$ times the
KL of the coupling against the product of the references. As $\epsilon\to 0$ it recovers
the (squared, for quadratic $c$) Wasserstein distance; $\epsilon>0$ **smooths** it.
(This matches `sinkhornObjective`/`Wkappa` in `V4.lean`, which use $c(x,y)=\lVert x-y\rVert^2$
and $\mu\otimes\nu=$ `prodMeasure`.)

The paper takes $\mu=\hat P$ (Remark 2: any $\mu$ with $\hat P\ll\mu$ gives the same
problem up to a constant) and lets $\nu$ be the reference the worst-case is absolutely
continuous with respect to (Lebesgue, Gaussian, or counting measure).

### The Sinkhorn ambiguity set and the primal

> The **Sinkhorn ball** of radius $\rho$ centered at $\hat P$ is
> $$\mathcal B_{\rho,\epsilon}(\hat P):=\big\{P:\ W_\epsilon(\hat P,P)\le\rho\big\},$$
> and the **primal** worst-case expectation problem is
> $$V:=\sup_{P\in\mathcal B_{\rho,\epsilon}(\hat P)}\ \mathbb E_{z\sim P}[f(z)].\tag{Primal}$$

Because $W_\epsilon(\hat P,\cdot)$ is convex (convexity of entropic OT), the Sinkhorn
ball is convex and `(Primal)` is an infinite-dimensional convex program. (`sinkhornBall`,
`drsbWorstCaseCost_SDRO`, `drsbValue_SDRO` in Lean.)

An equivalent reference-kernel form used throughout the proofs: define the constant
and the **kernel reference distribution**

$$\bar\rho:=\rho+\epsilon\,\mathbb E_{x\sim\hat P}\big[\log\mathbb E_{z\sim\nu}\,e^{-c(x,z)/\epsilon}\big],\tag{2}$$
$$\mathrm dQ_{x,\epsilon}(z):=\frac{e^{-c(x,z)/\epsilon}}{\mathbb E_{u\sim\nu}[e^{-c(x,u)/\epsilon}]}\,\mathrm d\nu(z).\tag{3}$$

Eq. `(3)` is the **Gibbs kernel of the cost alone**: for quadratic $c(x,z)=\lVert x-z\rVert^2$
it is the **Gaussian kernel** $K_\epsilon(x)\propto\exp(-\lVert x\rVert_2^2/\epsilon)$
(the paper states this explicitly for the kernel-density example, its Eq. `(4)`
region). This is the seed of the code's Gaussian worst-case tilt.

---

## Strong duality theorem (the log-partition dual)

The main dual program (its printed Eq. `(1)`, restated as `(Dual)`):

$$V_D:=\inf_{\lambda\ge 0}\ \Big\{\lambda\rho+\lambda\epsilon\,\mathbb E_{x\sim\hat P}\Big[\log\mathbb E_{z\sim\nu}\,e^{(f(z)-\lambda c(x,z))/(\lambda\epsilon)}\Big]\Big\},\tag{1}$$

equivalently, using $\bar\rho$ and $Q_{x,\epsilon}$,

$$V_D=\inf_{\lambda\ge 0}\ \Big\{\lambda\bar\rho+\lambda\epsilon\,\mathbb E_{x\sim\hat P}\Big[\log\mathbb E_{z\sim Q_{x,\epsilon}}\,e^{f(z)/(\lambda\epsilon)}\Big]\Big\}.\tag{Dual}$$

At $\lambda=0$ the objective is defined by convention as the limit $\lambda\downarrow0$,
which equals the $\nu$-essential supremum of the objective.

**Hypotheses (Assumption 1, as printed).**
1. **(I)** $c(x,z)$ is $\hat P\otimes\nu$-measurable and $\nu\{z:0\le c(x,z)<\infty\}=1$ for $\hat P$-a.e. $x$.
2. **(II)** $\mathbb E_{z\sim\nu}[e^{-c(x,z)/\epsilon}]<\infty$ for $\hat P$-a.e. $x$ (makes $K$, $Q_{x,\epsilon}$ well-defined).
3. **(III)** $\mathcal Z$ is measurable and $f:\mathcal Z\to\mathbb R\cup\{\infty\}$ is measurable.
4. **(IV)** every joint $\gamma$ with first marginal $\hat P$ admits a **regular conditional distribution** $\gamma_x$ (holds e.g. on Polish $\mathcal Z$; enables the disintegration $\mathrm d\gamma(x,z)=\mathrm d\hat P(x)\,\mathrm d\gamma_x(z)$).

**Light-tail (Condition 1, as printed).** There exists $\lambda>0$ with
$\mathbb E_{z\sim Q_{x,\epsilon}}[e^{f(z)/(\lambda\epsilon)}]<\infty$ for $\hat P$-a.e. $x$.
This is the finiteness gate distinguishing $V_D<\infty$ from $V_D=\infty$.

> **Theorem 1 (Strong Duality).** Let $\hat P\in\mathcal P(\mathcal Z)$ and assume
> Assumption 1. Then:
> - **(I)** `(Primal)` is feasible iff $\rho\ge 0$.
> - **(II)** Whenever $\rho\ge 0$, $\ V=V_D$.
> - **(III)** If in addition Condition 1 holds and $\rho>0$, then $V=V_D<\infty$;
>   otherwise $V=V_D=\infty$.
> - **(IV)** Under Condition 1 and $\rho>0$, with $A:=\{z:f(z)=\operatorname*{ess\,sup}_\nu f\}$,
>   the dual minimizer $\lambda^*=0$ iff $\operatorname*{ess\,sup}_\nu f<\infty$ and
>   $\rho\ge\epsilon\,\mathbb E_{x\sim\hat P}[\log(1/\mathbb P_{z\sim Q_{x,\epsilon}}\{A\})]$.
>
> (If $\rho<0$ then by convention $V=V_D=-\infty$; so $V=V_D$ holds as long as Assumption 1 holds.)

Part **(II)** is the load-bearing identity `sup_P E_P[f] = inf_λ (…log-partition…)`
that `sdro_dual` encodes. Part **(IV)** gives the exact "when is the ambiguity ball
binding" condition — the DRO analogue of "is the constraint active."

### Proof-argument sketch (how entropy smooths the Wasserstein dual into log-sum-exp)

The paper's Section 3.4 proof runs Lagrangian weak duality, then closes the gap by
constructing the worst-case measure. The pivotal step is the **inner entropic
maximization**, and this is exactly where the log-partition term is born.

1. **Disintegrate + Lagrangian (Lemma 1, weak duality).** Using Assumption 1(IV) to
   write $\mathrm d\gamma(x,z)=\mathrm d\hat P(x)\,\mathrm d\gamma_x(z)$, `(Primal)` becomes a
   sup over conditional families $\{\gamma_x\}$ subject to
   $\mathbb E_{x\sim\hat P}\mathbb E_{z\sim\gamma_x}[c(x,z)+\epsilon\log\tfrac{\mathrm d\gamma_x}{\mathrm d\nu}]\le\rho$.
   Introducing multiplier $\lambda\ge 0$ and swapping $\sup$/$\inf$ (its Eqs. `(6)`–`(7)`):
   $$V\le\inf_{\lambda\ge0}\Big\{\lambda\rho+\mathbb E_{x\sim\hat P}\,v_x(\lambda)\Big\},\quad
   v_x(\lambda):=\sup_{\gamma_x\in\mathcal P(\mathcal Z)}\mathbb E_{z\sim\gamma_x}\Big[f(z)-\lambda c(x,z)-\lambda\epsilon\log\tfrac{\mathrm d\gamma_x(z)}{\mathrm d\nu(z)}\Big].\tag{8}$$

2. **The inner problem is a Gibbs variational problem (Lemma EC.2).** Eq. `(8)` is
   precisely a maximization of an expected reward *minus* a relative-entropy penalty:
   with $A(z)=f(z)-\lambda c(x,z)$ and $\tau=\lambda\epsilon$,
   $v_x(\lambda)=\sup_{\gamma_x}\{\mathbb E_{\gamma_x}[A]-\tau\,\mathbb E_{\gamma_x}[\log\tfrac{\mathrm d\gamma_x}{\mathrm d\nu}]\}$.
   The paper's **Lemma EC.2** (cited to entropic-dual literature) evaluates this in closed form:
   > **Lemma EC.2.** For $v(\tau)=\sup_{P\in\mathcal P(\mathcal Z)}\mathbb E_{z\sim P}\big[f(z)-\tau\log\tfrac{\mathrm dP(z)}{\mathrm d\nu(z)}\big]$:
   > (I) $\tau=0$: $v(0)=\operatorname*{ess\,sup}_\nu f$.
   > (II) $\tau>0$ and $\mathbb E_{z\sim\nu}[e^{f/\tau}]<\infty$: $\ v(\tau)=\tau\log\mathbb E_{z\sim\nu}[e^{f(z)/\tau}]$,
   >    with optimal $\ \mathrm dP(z)=\dfrac{e^{f(z)/\tau}}{\mathbb E_{u\sim\nu}[e^{f(u)/\tau}]}\,\mathrm d\nu(z)$; and $\lim_{\tau\downarrow0}v(\tau)=v(0)$.
   > (III) $\tau>0$ and $\mathbb E_{z\sim\nu}[e^{f/\tau}]=\infty$: $\ v(\tau)=\infty$.

   Applying it with $A=f-\lambda c$, $\tau=\lambda\epsilon$ gives
   $$v_x(\lambda)=\lambda\epsilon\,\log\mathbb E_{z\sim\nu}\big[e^{(f(z)-\lambda c(x,z))/(\lambda\epsilon)}\big],$$
   which substituted into the outer inf is precisely dual `(1)`. **This is the
   entropy-smoothing:** where Wasserstein DRO ($\epsilon\to0$) has the hard
   $v_x(0)=\sup_z\{f(z)-\lambda c(x,z)\}$ (a pointwise max), the entropy term $\tau>0$
   replaces it by the **soft-max / log-sum-exp** $\lambda\epsilon\log\int e^{(f-\lambda c)/(\lambda\epsilon)}$.
   The paper states this collapse explicitly (Remark 3):
   > as $\epsilon\to0$ the dual objective converges to
   > $\lambda\rho+\mathbb E_{x\sim\hat P}[\sup_{z\in\operatorname{supp}\nu}f(z)-\lambda c(x,z)]$,
   > "which essentially follows from the fact that the log-sum-exp function is a smooth
   > approximation of the supremum," recovering the Wasserstein-DRO dual [Mohajerin
   > Esfahani–Kuhn / Gao–Kleywegt Thm 1].

3. **Close the gap (strong duality).** Lemma 2 reformulates `(Primal)` as a KL-DRO
   problem (worst-case over $\{\gamma_x\}$ with $\epsilon\,\mathbb E_{\hat P}\mathrm{KL}(\gamma_x\Vert Q_{x,\epsilon})\le\rho$),
   giving feasibility (I) via nonnegativity of KL. Lemma 3 gives the first-order
   optimality condition for $\lambda^*>0$ (its Eq. `(9)`), and the worst-case measure
   built from that $\lambda^*$ attains $V$, so $V=V_D$ (no duality gap).

### Donsker–Varadhan / Gibbs variational identity (the engine of step 2)

When $\nu$ is a probability measure, $\mathbb E_P[\log\tfrac{\mathrm dP}{\mathrm d\nu}]=\mathrm{KL}(P\Vert\nu)$
and Lemma EC.2(II) *is* the **Donsker–Varadhan / Gibbs variational principle**:
$$\log\mathbb E_{z\sim\nu}\big[e^{f(z)}\big]=\sup_{P\ll\nu}\Big\{\mathbb E_{z\sim P}[f(z)]-\mathrm{KL}(P\Vert\nu)\Big\},$$
with the supremum attained by the **Gibbs tilt** $\mathrm dP^\star\propto e^{f}\,\mathrm d\nu$.
(Scaling by $\tau$ gives the $\tau\log\int e^{f/\tau}$ form used above.) This is the exact
identity already formalized in this development as `DRSB.donsker_varadhan` /
`WellKnown.log_integral_exp_eq_sSup` — it converts `M_logPartition` into a supremum
over posteriors whose maximizer is the Gibbs kernel.

---

## Worst-case distribution: a continuous Gibbs / exponential tilt

> **Remark 4 (Worst-case Distribution).** Assume $\rho>0$, Condition 1, and an optimal
> $\lambda^*>0$ (unique by Lemma 3). The worst-case distribution maps every
> $x\in\operatorname{supp}\hat P$ to a conditional $\gamma_x^*$ solving the strictly convex
> program `(8)`, whose density w.r.t. $\nu$ is
> $$\frac{\mathrm d\gamma_x^*}{\mathrm d\nu}(z)=\alpha_x\cdot\exp\!\big((f(z)-\lambda^* c(x,z))/(\lambda^*\epsilon)\big),\qquad
> \alpha_x:=\Big(\mathbb E_{z\sim\nu}\big[e^{(f(z)-\lambda^* c(x,z))/(\lambda^*\epsilon)}\big]\Big)^{-1},$$
> and the worst-case marginal $P^*$ has density
> $$\frac{\mathrm dP^*(z)}{\mathrm d\nu(z)}=\mathbb E_{x\sim\hat P}\big[\alpha_x\cdot\exp\big((f(z)-\lambda^* c(x,z))/(\lambda^*\epsilon)\big)\big].$$
> Hence $P^*$ shares the same support as $\nu$.

Key qualitative fact for DRSB (Remarks 3–4, as printed): with $\hat P=\frac1n\sum_i\delta_{x_i}$
empirical and $\nu$ a continuous distribution on $\mathbb R^d$, the Sinkhorn worst-case
$P^*$ is **supported on all of $\mathbb R^d$** — a smooth, full-support mixture of Gibbs
tilts — *whereas* the Wasserstein-DRO worst-case is supported on at most $n+1$ points.
The Wasserstein support points are exactly the **modes** of the continuous Sinkhorn
worst-case. This continuity/full-support is the property DRSB exploits to draw a
smooth Gaussian worst-case source.

This $\gamma_x^*$ is the **Gibbs kernel**: an exponential tilt of the reference $\nu$ by
the tilted reward $(f-\lambda^* c)/(\lambda^*\epsilon)$, normalized by the log-partition
$\alpha_x^{-1}$. It is the maximizer identified by Lemma EC.2(II) / Donsker–Varadhan.
(`gibbsUnnormalized`, `GibbsKernel`, `exists_worstCase_gibbsKernel` in Lean.)

---

## DRSB / Lean scaffold correspondence

Mapping to the `V4.lean` (`namespace DRSB`) declarations, to DRSB **Eq. 47**, and to
the `sdrsb_cost_bound.yaml` card. Recall the symbol dictionary: paper $\epsilon\to$
`kappa`, paper $\rho\to$ `eps`, paper $\lambda\to$ `lam`, paper $f\to$ `Psi0`,
paper $\nu\to$ `base`, paper $\hat P\to$ `muhat`, paper $c(x,z)\to\lVert x-z\rVert^2$.

- **`sinkhornObjective` / `Wkappa` / `sinkhornBall`** $\leftrightarrow$ **Definition 1** and
  the Sinkhorn ball $\mathcal B_{\rho,\epsilon}(\hat P)$.
  > ⚠️ **AUDIT CORRECTION (2026-07).** An earlier version of this bullet and the Lean
  > scaffold defined `Wkappa κ μ μ̂ = inf_π E_π[c] + κ·KL(π ‖ μ⊗μ̂)` — the entropic
  > reference being **the product of the two coupling marginals** `μ⊗μ̂`. **That is the
  > wrong Sinkhorn distance for this paper.** Definition 1 uses `H(γ | μ⊗ν)` with `μ = P̂`
  > (nominal) and **`ν` an EXTERNAL reference** (Lebesgue/Gaussian/counting — the measure
  > the worst-case is a.c. wrt), so the entropic reference is `P̂ ⊗ ν`, and that same
  > external `ν` is what the dual's log-partition integrates over
  > (`𝔼_{z∼ν}[e^{(f−λc)/(λε)}]`). With the product-of-marginals reference, the ball and
  > the dual reference *different* measures, so `strong_duality`, `sdrsb_*`, and
  > `primal_feasible_iff` were internally inconsistent. **Fixed:** `Wkappa`/`sinkhornBall`
  > now carry the external reference — `Wkappa κ ν μ̂ μ = inf_{γ∈Π(μ̂,μ)} E_γ[c] + κ·KL(γ ‖ μ̂⊗ν)`,
  > `sinkhornBall μ̂ ν κ ε = {μ : Wkappa κ ν μ̂ μ ≤ ε}`. So `sinkhornBall p₀ ν κ ε` is
  > $\mathcal B_{\rho,\epsilon}(\hat P)$ with the paper's external $\nu$.

- **`M_logPartition base Ψ₀ λ κ x̂`** $\;=\;\lambda\kappa\,\log\int_x\exp\!\big(\tfrac{\Psi_0(x)-\lambda\lVert x-\hat x\rVert^2}{\lambda\kappa}\big)\,\mathrm d\text{base}$
  $\ \leftrightarrow\ $ the inner term $v_x(\lambda)=\lambda\epsilon\log\mathbb E_{z\sim\nu}[e^{(f(z)-\lambda c(x,z))/(\lambda\epsilon)}]$
  of dual `(1)`. This **is** the object $M(\Psi_0,\lambda,\kappa,\hat x)$ = the
  log-partition / soft-max term. (Lean's integration variable `x` = paper's worst-case
  point `z`; Lean's `xhat` = paper's nominal `x`.)

- **`sdro_dual`** $\leftrightarrow$ **Theorem 1(II)**, $V=V_D$:
  $$\sup_{\mu\in\text{sinkhornBall}}\mathbb E_\mu[\Psi_0]=\inf_{\lambda\ge0}\Big\{\lambda\cdot\text{eps}+\mathbb E_{\hat x\sim\hat\mu}\big[M(\Psi_0,\lambda,\kappa,\hat x)\big]\Big\},$$
  i.e. exactly dual `(1)` with $\rho=$ `eps`, $\epsilon=$ `kappa`. The Lean file leaves
  only the **outer** strong-duality direction as `sorry`; the **inner** soft-max
  ($v_x(\lambda)$ = log-partition) is the Donsker–Varadhan identity already proved as
  `WellKnown.log_integral_exp_eq_sSup` / `DRSB.donsker_varadhan` (this file's step 2).

- **`gibbsUnnormalized base Ψ₀ λ κ x̂`** $=\ \exp\!\big(\tfrac{\Psi_0(x)-\lambda\lVert x-\hat x\rVert^2}{\lambda\kappa}\big)\,\mathrm d\text{base}$
  $\ \leftrightarrow\ $ the **unnormalized** Remark-4 density $\exp((f-\lambda^*c)/(\lambda^*\epsilon))\,\mathrm d\nu$.
  **`GibbsKernel` / `exists_worstCase_gibbsKernel`** $\leftrightarrow$ its normalization by
  $\alpha_x=(\int\dots)^{-1}$ into the worst-case conditional $\gamma_x^*$ (Remark 4). The
  Lean existence proof's hypotheses `hpos`/`hfin` (total mass $\ne 0,\ne\infty$) are the
  measure-theoretic form of **Assumption 1(II) + Condition 1** (finite, positive
  normalizer), i.e. the conditions under which $\alpha_x$ is well-defined.

- **DRSB "Eq. 47"** $\ \text{Bound}=\mathbb E_{\text{worst-case}}[V(x)]-\rho\log\mathbb E_\nu[e^{g(X_1)}]$:
  the $-\rho\log\mathbb E_\nu[e^{g}]$ term is the **log-partition** term of dual `(1)`
  instantiated with loss $f=V$/terminal cost $g$, reference $\nu$, and the DRSB
  coefficient $\rho$ standing for the paper's $\lambda\epsilon$ (or a fixed multiplier).
  *(Paraphrase / flagged: the DRSB paper's Eq. 47 is not in this PDF; the identification
  is by shape. The sign is a convention artifact — this paper's `(Primal)` is a `sup`
  (worst-case reward), so the log-partition enters with `+` inside an `inf_λ`; a DRSB
  worst-case **cost** bound writes the same entropic term with the opposite sign. The
  load-bearing content — an entropic/soft-max $\log\mathbb E_\nu[e^{(\cdot)}]$ replacing a
  Wasserstein pointwise `sup`, with a full-support Gibbs worst-case — is identical.)*

- **`drsbValue_SDRO` / `drsbWorstCaseCost_SDRO`** $\leftrightarrow$ the outer robust
  problem: `sInf_u sup_{μ∈sinkhornBall} J(u;μ)`, i.e. `(Primal)`'s worst-case expectation
  wrapped in the control minimization, evaluated via `sdro_dual`. Its Sinkhorn worst-case
  being **continuous/full-support** (Remark 3/4) is what lets the DRSB code draw the
  worst-case *source* as a continuous Gaussian rather than a discrete atom set.

- **Gaussian worst-case tilt $\tilde X_0\sim\mathcal N\big(x_0-\tfrac{u_0}{2\lambda},\tfrac{\kappa}{2}I\big)$
  in DRSB code** $\leftrightarrow$ Remark 4's Gibbs density with quadratic cost. Take
  $\nu=$ Lebesgue, $c(x,z)=\lVert z-x\rVert^2$, and a locally linear loss
  $f(z)\approx f(x_0)+\langle u_0,z-x_0\rangle$ (value-function gradient $u_0$). The
  exponent of $\gamma_x^*$ is $\tfrac{1}{\lambda\kappa}\big(\langle u_0,z\rangle-\lambda\lVert z-x_0\rVert^2\big)$;
  completing the square in $z$,
  $-\lambda\lVert z-x_0\rVert^2+\langle u_0,z\rangle=-\lambda\big\lVert z-(x_0+\tfrac{u_0}{2\lambda})\big\rVert^2+\text{const}$,
  so $\gamma_x^*\propto\exp\!\big(-\tfrac{1}{\kappa}\lVert z-(x_0+\tfrac{u_0}{2\lambda})\rVert^2\big)$
  — a Gaussian with mean $x_0\pm\tfrac{u_0}{2\lambda}$ and covariance $\tfrac{\kappa}{2}I$
  (since $\exp(-\lVert z-m\rVert^2/\kappa)$ is $\mathcal N(m,\tfrac{\kappa}{2}I)$). This
  **exactly reproduces the code's tilt** (the mean sign depends on the ascent/descent
  convention for $u_0$). The Gibbs worst-case conditional and the code's Gaussian source
  are the same object.

- **`sdrsb_cost_bound.yaml` card claim** — the card asserts the SDRSB worst-case cost
  bound of DRSB "Eq. 47" shape (entropic log-partition term + Gibbs/Gaussian worst-case
  source). Its mathematical backing is **Theorem 1 (Strong Duality)** — dual `(1)`/`(Dual)`
  supplying the $\rho\log\mathbb E_\nu[e^{g}]$ log-partition term — together with **Remark 4**
  (worst-case Gibbs tilt) and **Remark 3** (full-support continuity / $\epsilon\to0$
  recovery of the Wasserstein `sup`), all under **Assumption 1** + **Condition 1**.
