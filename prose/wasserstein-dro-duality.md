# Wasserstein Distributionally-Robust Optimization: Strong-Duality Reference

Prose transcription of the WDRO strong-duality theorems that make the DRSB
worst-case cost $\mathbb{E}_{\text{worst-case}}[V]$ a tractable, attainable quantity.
Statements are transcribed from the PDFs (extracted with `pdftotext`); printed
theorem/equation numbers are quoted verbatim, and every paraphrase is marked
**(paraphrase)**. Notation is kept close to each source, with a bridging note where
it differs from the DRSB Lean scaffold.

## Sources

1. **Blanchet, Murthy — "Quantifying Distributional Model Risk via Optimal Transport"**,
   *Mathematics of Operations Research* (2019), arXiv:1604.01446.
   <https://arxiv.org/abs/1604.01446>. **Primary strong-duality result.**
2. **Gao, Kleywegt — "Distributionally Robust Stochastic Optimization with Wasserstein
   Distance"**, *Mathematics of Operations Research* (2023), arXiv:1604.02199.
   <https://arxiv.org/abs/1604.02199>. Strong duality + worst-case-distribution structure.
3. **Mohajerin Esfahani, Kuhn — "Data-driven Distributionally Robust Optimization Using
   the Wasserstein Metric"**, *Mathematical Programming* (2018), arXiv:1505.05116.
   <https://arxiv.org/abs/1505.05116>. Data-driven (empirical nominal) duality +
   finite convex reformulation + extremal distributions.

PDFs live in `prose/papers/` (not committed to the repo).

## Role in the DRSB chain

The GaTech **Distributionally-Robust Schrödinger Bridge (DRSB)** paper proves a
worst-case cost bound on a value function $V(x)$: for any source distribution $\mu$
in a Wasserstein-2 ball of radius $\varepsilon$ around the nominal $\hat\mu$ (equivalently
$p_0$), $\mathbb{E}_\mu[V] \le \mathbb{E}_{\text{worst-case}}[V]$, and the right-hand
side equals a *tractable* quantity. The eval card `wdrsb_cost_bound.yaml` asserts exactly
this: it checks that under every perturbation lying inside the $W_2$ ball, the measured
cost does not exceed the computed bound $\mathbb{E}_{\text{wc}}[V]$. The three papers
below supply the theorem that turns the infinite-dimensional inner supremum
$\sup_{\mu:\,W_2^2(\mu,\hat\mu)\le\varepsilon}\mathbb{E}_\mu[V]$ into the one-dimensional
convex dual
$$\inf_{\lambda\ge 0}\Big\{\lambda\varepsilon + \mathbb{E}_{\hat x\sim\hat\mu}\big[\textstyle\sup_x\big(V(x)-\lambda\|x-\hat x\|^2\big)\big]\Big\},$$
and characterize the worst-case distribution as a *transport* of the nominal mass along
the cost-optimal direction (which, for a Gaussian nominal, is a closed-form shift). Both
directions matter: the **easy $\le$ (weak-duality) direction** is the mathematical content
of the card's bound (and of the proven Lean lemma `wdro_lagrangian_bound`); the **strong
$=$ direction** (Blanchet–Murthy / Gao–Kleywegt) certifies that the tractable dual is not
loose, i.e. the bound is actually attained by some $\mu$ in the ball.

---

## 1. Blanchet–Murthy (2019): strong duality for optimal-transport DRO

### 1.1 Setup and notation

Work over a Polish space $S$ with baseline probability measure $\mu\in P(S)$. For
$\mu_1,\mu_2\in P(S)$, $\Pi(\mu_1,\mu_2)$ is the set of couplings (joint laws with the
prescribed marginals). The **optimal transport cost** is
$$d_c(\mu_1,\mu_2) := \inf\Big\{\textstyle\int c\,d\pi : \pi\in\Pi(\mu_1,\mu_2)\Big\},\qquad(\text{eq. 2})$$
under two standing assumptions:

- **Assumption (A1).** $c:S\times S\to\mathbb{R}_+$ is a nonnegative lower semicontinuous
  function with $c(x,y)=0$ **iff** $x=y$.
- **Assumption (A2).** $f\in L^1(d\mu)$ is **upper semicontinuous**.

Taking $c(x,y)=d(x,y)$ recovers the first-order Wasserstein distance; taking
$c(x,y)=\|x-y\|^2$ recovers $W_2^2$ — the cost used by DRSB. **(paraphrase)** The
constraint is the *hard* transport-distance ball $d_c(\mu,\nu)\le\delta$, not a penalized
divergence.

**Primal.** For radius $\delta>0$,
$$I := \sup\Big\{\textstyle\int f\,d\nu : d_c(\mu,\nu)\le\delta\Big\}
   = \sup\{\,I(\pi):\pi\in\Phi_{\mu,\delta}\,\},\qquad(\text{eq. 3})$$
where $I(\pi)=\int f(y)\,d\pi(x,y)$ and
$\Phi_{\mu,\delta}=\{\pi\in\bigcup_\nu\Pi(\mu,\nu):\int c\,d\pi\le\delta\}$ (eq. 6a).

**Dual.** Let $\Lambda_{c,f}$ be the pairs $(\lambda,\varphi)$ with $\lambda\ge 0$,
$\varphi\in m\mathcal{U}(S;\overline{\mathbb{R}})$ and
$$\varphi(x)+\lambda c(x,y)\ge f(y)\quad\text{for all }x,y,\qquad(\text{eq. 4, 6b})$$
and set $J(\lambda,\varphi)=\lambda\delta+\int\varphi\,d\mu$, $J=\inf\{J(\lambda,\varphi):(\lambda,\varphi)\in\Lambda_{c,f}\}$.

**Weak duality (eq. 5).** For every feasible $\pi$ and $(\lambda,\varphi)$, a one-line
Lagrangian computation gives $J(\lambda,\varphi)\ge I(\pi)$, hence
$$J = \inf\{J(\lambda,\varphi):(\lambda,\varphi)\in\Lambda_{c,f}\} \;\ge\; I. \qquad(\text{eq. 5})$$
This "$J\ge I$" is the always-true half; it is the abstract shape of the DRSB card's bound.

### 1.2 The strong-duality theorem

**Theorem 1.** *Under Assumptions (A1) and (A2),*

*(a)* $I=J$*, i.e.*
$$\sup\{I(\pi):\pi\in\Phi_{\mu,\delta}\}=\inf\{J(\lambda,\varphi):(\lambda,\varphi)\in\Lambda_{c,f}\}.$$

*(b) For any $\lambda\ge0$ define $\varphi_\lambda:S\to\mathbb{R}\cup\{\infty\}$ by*
$$\varphi_\lambda(x):=\sup_{y\in S}\big(f(y)-\lambda c(x,y)\big).$$
*There exists a dual optimizer of the form $(\lambda,\varphi_\lambda)$ for some $\lambda\ge0$.
Moreover a feasible $\pi^*$ and $(\lambda^*,\varphi_{\lambda^*})$ are jointly optimal
($I(\pi^*)=J(\lambda^*,\varphi_{\lambda^*})$) if and only if the complementary-slackness
conditions hold:*
$$f(y)-\lambda^* c(x,y)=\sup_{z\in S}\big(f(z)-\lambda^* c(x,z)\big),\quad \pi^*\text{-a.s.},\qquad(\text{eq. 8a})$$
$$\lambda^*\Big(\textstyle\int c(x,y)\,d\pi^*(x,y)-\delta\Big)=0.\qquad(\text{eq. 8b})$$

**The load-bearing identity (Remark 1, eq. 9).** As a consequence of Theorem 1 (using
$J(\lambda,\varphi_\lambda)\le J(\lambda,\varphi)$ for all feasible $\varphi$), the value $I$
has the **univariate reformulation**
$$\boxed{\,I=\inf_{\lambda\ge0}\Big\{\lambda\delta+\mathbb{E}_\mu\big[\textstyle\sup_{y\in S}\big(f(y)-\lambda c(X,y)\big)\big]\Big\}\,}\qquad(\text{eq. 9})$$
where $X\sim\mu$. The only measure on the right is the baseline $\mu$, "which is completely
characterized, and is usually chosen in a way that it is easy to work with (or) draw samples
from." **This is exactly the object `wdro_dual` / `wdro_lagrangian_bound` in the Lean
scaffold**, with $\mu\mapsto\hat\mu$, $\delta\mapsto\varepsilon$, $f\mapsto V$, and
$c(x,y)=\|x-y\|^2$ (note $c(X,y)=\|X-y\|^2=\|y-X\|^2$, so the paper's $c(X,\cdot)$ and the
scaffold's $\|x-\hat x\|^2$ coincide by symmetry of the quadratic cost). The inner
$\sup_y(f(y)-\lambda c(X,y))=\varphi_\lambda(X)$ is `L_wdro`.

### 1.3 Worst-case distribution

**Remark 2 (structure of the primal optimal plan).** From (b), if a worst-case coupling
$\pi^*$ exists it is concentrated on
$$\{(x,y)\in S\times S : y\in\arg\max_{z\in S}\big(f(z)-\lambda^* c(x,z)\big)\}.$$
**(paraphrase)** So $\pi^*$ transports each baseline atom $x$ to a maximizer $y$ of the
local problem $\sup_z(f(z)-\lambda^* c(x,z))$; the worst-case source $\nu$ is the pushforward
of $\mu$ under that transport map. Complementary slackness splits into: **Case $\lambda^*>0$**
— the plan saturates the constraint, $\int c\,d\pi^*=\delta$; **Case $\lambda^*=0$** — $f(y)$
equals its global sup $\pi^*$-a.s. and the constraint is slack.

### 1.4 Proof-argument sketch

The paper's proof (Section 4) establishes strong duality in stages. **(paraphrase)** (i)
In *compact* Polish spaces (Prop. 5–6) it applies the **Fenchel duality theorem** (Luenberger,
Ch. 7) to the concave primal over $C_b(S)$; a monotone-convergence step extends from continuous
to lower-semicontinuous costs $c$. (ii) A Prokhorov/tightness argument (Prop. 6) passes to
the limit of costs $c_n\uparrow c$. (iii) Since any Borel measure on a Polish space is
concentrated on a $\sigma$-compact set (Prop. 7), duality is lifted from compact to noncompact
$S$ by restricting to $\mathrm{Spt}(\pi_X)\times\mathrm{Spt}(\pi_Y)$. Measurability of the
value function $\varphi_\lambda$ (as a $\mathcal U(S)$-measurable map) is handled via
analytic-set / measurable-selection results (Bertsekas–Shreve Prop. 7.50).

---

## 2. Gao–Kleywegt (2023): strong duality and worst-case structure

### 2.1 Setup and notation

Nominal $\nu\in P(\Xi)$ on a Polish space $(\Xi,d)$; $\Psi:\Xi\to\mathbb{R}$ is the objective
(the paper suppresses a decision variable $x$: results are pointwise in $x$). The
**Wasserstein distance** (Definition 2) of order $p$ is
$$W_p^p(\mu,\nu):=\min_{\gamma\in P(\Xi\times\Xi)}\Big\{\textstyle\int d^p(\xi,\zeta)\,\gamma(d\xi,d\zeta):\pi^1_\#\gamma=\mu,\ \pi^2_\#\gamma=\nu\Big\}.\qquad(\text{eq. 1})$$
The ambiguity set is $M:=\{\mu\in P(\Xi):W_p(\mu,\nu)\le\theta\}$ and the DRSO inner problem is

$$v_P := \sup_{\mu\in M}\int_\Xi\Psi\,d\mu=\sup\Big\{\textstyle\int\Psi\,d\mu:W_p(\mu,\nu)\le\theta\Big\}.\qquad(\text{Primal})$$

The proposed dual is
$$v_D := \inf_{\lambda\ge0}\Big\{\lambda\theta^p-\int_\Xi\inf_{\xi\in\Xi}\big[\lambda d^p(\xi,\zeta)-\Psi(\xi)\big]\,\nu(d\zeta)\Big\}.\qquad(\text{Dual})$$
Because $-\inf_\xi[\lambda d^p(\xi,\zeta)-\Psi(\xi)]=\sup_\xi[\Psi(\xi)-\lambda d^p(\xi,\zeta)]$,
this is *identical in form* to Blanchet–Murthy (9) with $\delta=\theta^p$. The inner map is the
**Moreau–Yosida regularization** of $-\Psi$:
$$\Phi(\lambda,\zeta):=\inf_{\xi\in\Xi}\big[\lambda d^p(\xi,\zeta)-\Psi(\xi)\big].\qquad(\text{Definition 3})$$

**Growth rate (Definition 4).**
$$\kappa:=\inf\Big\{\lambda\ge0:\int_\Xi\Phi(\lambda,\zeta)\,\nu(d\zeta)>-\infty\Big\},$$
with $\kappa=\infty$ if the integral is $-\infty$ for all $\lambda$. When $\Xi$ is unbounded
and $\kappa<\infty$, $\kappa=\lim\sup_{d(\xi,\zeta)\to\infty}\max\{0,\Psi(\xi)-\Psi(\zeta)\}/d^p(\xi,\zeta)$
**(paraphrase — the "growth rate of $\Psi$")**. This finiteness of $\kappa$ is what separates a
finite from an infinite robust value.

### 2.2 The strong-duality theorems

**Proposition 1 (Weak duality).** *Consider any $\nu\in P(\Xi)$ and $\Psi\in L^1(\nu)$. Then
for any $p\in[1,\infty)$ and $\theta>0$, it holds that $v_P\le v_D$.* (Lagrangian weak duality —
the always-true direction.)

**Proposition 2 (Strong duality with infinite optimal value).** *Consider any $p\in[1,\infty)$,
$\nu\in P(\Xi)$, and $\Psi\in L^1(\nu)$. Suppose $\theta>0$ and $\kappa=\infty$. Then
$v_P=v_D=\infty$.*

**Theorem 1 (Strong duality with finite optimal value).** *Consider any $p\in[1,\infty)$, any
$\nu\in P(\Xi)$, any $\theta>0$, and any $\Psi\in L^1(\nu)$ such that $\kappa<\infty$. Then
$v_P=v_D<\infty$.*

**Remark 2.** All the Section-3.1 results (except one lemma) continue to hold if $d^p(\cdot,\cdot)$
is replaced by any measurable nonnegative cost $c(\cdot,\cdot)$ with $c(\xi,\zeta)=0$ when
$\xi=\zeta$ — so the theorem covers the general OT cost, and in particular the DRSB $W_2^2$
cost ($p=2$, $d$ Euclidean, $c=\|\cdot\|^2$, $\theta^2=\varepsilon$).

**(paraphrase — proof idea.)** Unlike Blanchet–Murthy, the proof is elementary and constructive:
it does *not* go through Hahn–Banach / Fenchel. For $\varepsilon>0$ one builds a near-optimal
$\mu^\varepsilon$ by measurably selecting, for each $\zeta$, a point $\xi$ near the argmin of
$\lambda d^p(\xi,\zeta)-\Psi(\xi)$ (Lemmas 6–7), showing
$v_P\ge\int\Psi\,d\mu^\varepsilon\ge\lambda^*\theta^p-\int\Phi(\lambda^*,\zeta)\nu(d\zeta)-\varepsilon=v_D-\varepsilon$;
letting $\varepsilon\downarrow0$ and combining with Proposition 1 gives $v_P=v_D$.

### 2.3 Worst-case distribution

**Corollary 1 (Worst-case distribution).** *Under $\kappa<\infty$, $\Psi$ upper semicontinuous,
and bounded subsets of $(\Xi,d)$ totally bounded:*

- *(i) [Existence]* a worst-case distribution exists iff one of three explicit conditions on the
  dual minimizer $\lambda^*$ vs $\kappa$ holds (**(a)** $\lambda^*>\kappa$; **(b)**
  $\lambda^*=\kappa>0$ unique with a distance-integral sandwich
  $\int\underline D_0(\kappa,\zeta)\nu(d\zeta)\le\theta^p\le\int\overline D_0(\kappa,\zeta)\nu(d\zeta)$;
  **(c)** $\lambda^*=\kappa=0$ unique with $\arg\max\Psi\ne\emptyset$).
- *(ii) [Structure]* whenever a worst-case distribution exists, there is one of the form
  $$\mu^*=p^*\,\overline T_{\#}\nu+(1-p^*)\,\underline T^{*}_{\#}\nu,\qquad p^*\in[0,1],\qquad(\text{eq. 27})$$
  *where $\overline T,\underline T^*:\Xi\to\Xi$ push $\nu$ forward and satisfy*
  $\nu\{\zeta:\overline T(\zeta),\underline T^*(\zeta)\notin\arg\min_\xi\{\lambda^* d^p(\xi,\zeta)-\Psi(\xi)\}\}=0$.
  *If $\lambda^*>0$, the induced $\gamma^T$ is an optimal coupling in the definition of
  $W_p^p(\mu^*,\nu)$.*

**(paraphrase — the DRSB link.)** The worst-case law is thus a *transport of the nominal*: it
moves each nominal point $\zeta$ to a maximizer of $\Psi(\xi)-\lambda^* d^p(\xi,\zeta)$, i.e.
along the cost-optimal direction, splitting mass at most between two maps. This is exactly why
DRSB can compute a **closed-form Gaussian worst-case shift**: with a Gaussian nominal and a
suitable objective, the optimal transport map is an affine/shift map, so $\mu^*$ is a shifted
(re-scaled) Gaussian. The paper's own Gaussian instance is **Example 10 (Worst-case VaR with
Gaussian nominal distribution)**, $\nu=\mathcal N(\bar\mu,\Sigma)$, where the worst-case VaR
reduces to a one-dimensional root-finding problem (eq. 41) — a tractable, essentially
closed-form perturbation of the nominal Gaussian.

**Corollary 2 (Data-Driven DRSO).** *For $\nu=\tfrac1N\sum_{i=1}^N\delta_{\hat\xi_i}$,
$p\in[1,\infty)$, $\theta>0$:*

- *(i) [Strong duality]* the primal has strong dual
  $$v_P=v_D=\inf_{\lambda\ge0}\Big\{\lambda\theta^p-\frac1N\sum_{i=1}^N\inf_{\xi\in\Xi}\big[\lambda d^p(\xi,\hat\xi_i)-\Psi(\xi)\big]\Big\}.\qquad(\text{eq. 28})$$
- *(ii) [Structure]* whenever a worst-case distribution exists, there is one supported on at
  most $N+1$ points,
  $$\mu^*=\frac1N\sum_{i\ne i_0}\delta_{\xi_*^i}+\frac{p_0}{N}\delta_{\xi_*^{i_0}}+\frac{1-p_0}{N}\delta_{\overline\xi_*^{i_0}},\qquad(\text{eq. 29})$$
  *with $\xi_*^i\in\arg\min_\xi\{\lambda^* d^p(\xi,\hat\xi_i)-\Psi(\xi)\}$: every data point is moved
  to an associated maximizer, and at most one point $\hat\xi_{i_0}$ is split between two maximizers.*

Equation (28) is precisely the empirical dual objective `wdrsbDualObjective` (with $\theta^p=\varepsilon$),
and its per-sample term is `L_wdro`.

---

## 3. Mohajerin Esfahani–Kuhn (2018): data-driven duality and convex reformulation

### 3.1 Setup and notation

Uncertainty $\xi\in\Xi\subseteq\mathbb{R}^m$; empirical nominal
$\hat P_N=\tfrac1N\sum_{i=1}^N\delta_{\hat\xi_i}$. **This paper uses the 1-Wasserstein
metric only.**

**Definition 3.1 (Wasserstein metric).**
$$d_W(Q_1,Q_2):=\inf\Big\{\textstyle\int_{\Xi^2}\|\xi_1-\xi_2\|\,\Pi(d\xi_1,d\xi_2):\Pi\text{ has marginals }Q_1,Q_2\Big\},$$
for an arbitrary norm $\|\cdot\|$ on $\mathbb{R}^m$ (a $p$-Wasserstein version uses cost
$\|\xi_1-\xi_2\|^p$, but the paper focuses on $p=1$). **Theorem 3.2 (Kantorovich–Rubinstein)**
gives the Lipschitz dual $d_W(Q_1,Q_2)=\sup_{\|f\|_{\text{Lip}}\le1}(\int f\,dQ_1-\int f\,dQ_2)$.

**Ambiguity set (eq. 6).** $B_\varepsilon(\hat P_N):=\{Q\in M(\Xi):d_W(\hat P_N,Q)\le\varepsilon\}$
— the Wasserstein ball of radius $\varepsilon$ around $\hat P_N$. (Theorems 3.4–3.6 give
measure-concentration, finite-sample, and asymptotic-consistency guarantees that motivate the
ball radius; not needed for the duality below.)

**Worst-case expectation problem (eq. 10).**
$$\sup_{Q\in B_\varepsilon(\hat P_N)}\mathbb{E}_Q[\ell(\xi)],\qquad \ell(\xi):=\max_{k\le K}\ell_k(\xi),$$
with **Assumption 4.1 (Convexity)**: $\Xi$ convex closed and each $-\ell_k$ proper, convex, lower
semicontinuous (so $\ell$ is a max of concave functions).

### 3.2 Data-driven strong duality and the finite convex reformulation

**Theorem 4.2 (Convex reduction).** *If the convexity Assumption 4.1 holds, then for any
$\varepsilon\ge0$ the worst-case expectation (10) equals the optimal value of the finite convex program*
$$\begin{aligned}
\inf_{\lambda,s_i,z_{ik},\nu_{ik}}\quad & \lambda\varepsilon+\frac1N\sum_{i=1}^N s_i\\
\text{s.t.}\quad & [-\ell_k]^*(z_{ik}-\nu_{ik})+\sigma_\Xi(\nu_{ik})-\langle z_{ik},\hat\xi_i\rangle\le s_i && \forall i\le N,\ \forall k\le K,\\
& \|z_{ik}\|_*\le\lambda && \forall i\le N,\ \forall k\le K,
\end{aligned}\qquad(\text{eq. 11})$$
*where $[-\ell_k]^*$ is the convex conjugate of $-\ell_k$, $\|\cdot\|_*$ the dual norm, and
$\sigma_\Xi$ the support function of $\Xi$.*

**The dual-over-$\lambda$ that matters for DRSB (proof of Thm 4.2, eqs. 12a–12b).** The proof
first uses the law of total probability to write $\Pi=\tfrac1N\sum_i\delta_{\hat\xi_i}\otimes Q_i$,
then Lagrangian duality on the $\int\|\xi-\hat\xi_i\|Q_i\le\varepsilon$ constraint, then optimizes
each conditional $Q_i$ pointwise over Dirac masses, yielding
$$\sup_{Q\in B_\varepsilon(\hat P_N)}\mathbb{E}_Q[\ell(\xi)]
=\inf_{\lambda\ge0}\;\lambda\varepsilon+\frac1N\sum_{i=1}^N\sup_{\xi\in\Xi}\big(\ell(\xi)-\lambda\|\xi-\hat\xi_i\|\big).\qquad(\text{eq. 12b})$$
This is the **data-driven strong dual**: a one-dimensional convex minimization over $\lambda\ge0$
whose per-sample term is a pointwise $\sup$ ("$\ell$ minus $\lambda\cdot$distance"). It is
`wdrsbDualObjective` / `empAvg` / `L_wdro` in the scaffold — with the caveat that the DRSB code
uses the **squared** cost $\|\xi-\hat\xi_i\|^2$ (a $W_2^2$ ball), whereas Esfahani–Kuhn use the
**unsquared** $\|\xi-\hat\xi_i\|$ ($W_1$). Introducing epigraph variables $s_i$ (eq. 12c) and
dualizing each $\sup_\xi$ via convex conjugacy (eqs. 12d–12f) produces the finite program (11).

**Corollary 4.3 (Approximate convex reduction).** For any $\varepsilon\ge0$, even without
Assumption 4.1, (10) is *upper bounded* by the optimal value of the finite convex program — i.e.
the dual is always a valid (conservative) upper bound. This is the always-true $\le$ half again.

### 3.3 Extremal / worst-case distributions

**Theorem 4.4 (Worst-case distributions).** *Under Assumption 4.1, (10) coincides with the
optimal value of the finite convex program*
$$\begin{aligned}
\sup_{\alpha_{ik},q_{ik}}\quad & \frac1N\sum_{i=1}^N\sum_{k=1}^K\alpha_{ik}\,\ell_k\!\Big(\hat\xi_i-\frac{q_{ik}}{\alpha_{ik}}\Big)\\
\text{s.t.}\quad & \frac1N\sum_{i,k}\|q_{ik}\|\le\varepsilon,\quad \sum_{k=1}^K\alpha_{ik}=1,\quad \alpha_{ik}\ge0,\quad \hat\xi_i-\frac{q_{ik}}{\alpha_{ik}}\in\Xi.
\end{aligned}\qquad(\text{eq. 13})$$
*For a sequence $\{\alpha_{ik}(r),q_{ik}(r)\}$ of feasible points whose objective converges to the
supremum, the discrete laws*
$$Q_r:=\frac1N\sum_{i=1}^N\sum_{k=1}^K\alpha_{ik}(r)\,\delta_{\xi_{ik}(r)},\qquad \xi_{ik}(r):=\hat\xi_i-\frac{q_{ik}(r)}{\alpha_{ik}(r)},$$
*lie in $B_\varepsilon(\hat P_N)$ and attain the supremum of (10) asymptotically.*

So the worst-case law's atoms $\xi_{ik}=\hat\xi_i-q_{ik}/\alpha_{ik}$ are **perturbations of the
data points along transport vectors $q_{ik}$**, with total transport budget
$\frac1N\sum_{i,k}\alpha_{ik}\|\xi_{ik}-\hat\xi_i\|=\frac1N\sum_{i,k}\|q_{ik}\|\le\varepsilon$ —
matching Gao–Kleywegt Corollary 2(ii).

**Corollary 4.6 (Existence of a worst-case distribution).** *Under Assumption 4.1, if $\Xi$ is
compact or the loss is concave ($K=1$), the sequence above has an accumulation point
$\{\alpha^*_{ik},\xi^*_{ik}\}$ and $Q^*=\tfrac1N\sum_{i,k}\alpha^*_{ik}\delta_{\xi^*_{ik}}$ is a
worst-case distribution attaining the supremum in (10).* Its atoms $\xi^*_{ik}$ sit in a
neighborhood of the data points $\hat\xi_i$, with cumulative displacement $\le\varepsilon$; the
worst case may be supported *outside* the support of $\hat P_N$ — a feature distinguishing
Wasserstein balls from KL/total-variation balls. (Example 2 in §4 exhibits a case with **no**
worst-case distribution, showing why existence needs a hypothesis.)

---

## DRSB / Lean scaffold correspondence

The scaffold is `V4.lean`, namespace `DRSB`. The DRSB card claim is
$\mathbb{E}_\mu[V]\le\mathbb{E}_{\text{worst-case}}[V]$ for every $\mu$ inside the $W_2$ ball;
`wdrsb_cost_bound.yaml` verifies "$\text{cost}\le\text{bound}$" whenever `in_ball` is true.

| Lean object (`DRSB.…`) | Mathematical meaning | Paper anchor |
|---|---|---|
| `Couplings mu nu` | $\Pi(\mu,\nu)$, joint laws with marginals $\mu,\nu$ | B–M §2.1; G–K Def. 2; E–K Def. 3.1 |
| `couplingCost2 pi` | $\mathbb{E}_\pi\|x-y\|^2$ | G–K Def. 2 ($p=2$) |
| `W2sq mu nu` | $\inf_{\pi\in\Pi(\mu,\nu)}\mathbb{E}_\pi\|x-y\|^2=W_2^2$ (Kantorovich primal) | G–K Def. 2 / eq. 1 |
| `wassersteinBall muhat eps` | $\{\mu:W_2^2(\mu,\hat\mu)\le\varepsilon\}$ (radius $\varepsilon=\theta^2$) | G–K $M$; E–K eq. 6 |
| `L_wdro V lam xhat` $=\sup_x(V(x)-\lambda\|x-\hat x\|^2)$ | inner dual objective $\varphi_\lambda(\hat x)$ / $-\Phi(\lambda,\hat x)$ | B–M Thm 1(b), eq. 9; G–K Def. 3 (Moreau–Yosida); E–K eq. 12b |
| `empAvg xhat f` $=\frac1N\sum_i f(\hat x_i)$ | empirical average over nominal atoms | G–K Cor. 2 / eq. 28; E–K eq. 12b |
| `wdrsbDualObjective` $=\inf_{\lambda\ge0}\{\lambda\varepsilon+\frac1N\sum_i L_{\text{wdro}}(V,\lambda,\hat x_i)\}$ | empirical WDRO strong dual | G–K eq. 28; E–K eq. 12b |
| `wdro_dual` (equality of `sSup` primal and `sInf` dual) | **strong duality** $\sup_{\mu\in\text{ball}}\mathbb{E}_\mu[V]=\inf_{\lambda\ge0}\{\lambda\varepsilon+\mathbb{E}_{\hat\mu}[\sup_x(V(x)-\lambda\|x-\hat x\|^2)]\}$ | **B–M Thm 1 + eq. 9**; **G–K Thm 1 + (Dual)** |
| `wdro_lagrangian_bound` (proven, no `sorry`) | the **easy $\le$ / weak-duality** direction: $\mathbb{E}_\mu[V]\le\mathbb{E}_{\hat\mu}[\sup_x(\cdots)]+\lambda\,\mathbb{E}_\pi\|x-\hat x\|^2$ | B–M eq. 5; G–K Prop. 1; E–K Cor. 4.3 |

**Mapping the card claim.** For any $\mu$ with $W_2^2(\mu,\hat\mu)\le\varepsilon$,
$$\mathbb{E}_\mu[V]\ \le\ \sup_{\mu':\,W_2^2(\mu',\hat\mu)\le\varepsilon}\mathbb{E}_{\mu'}[V]\ =\ \mathbb{E}_{\text{worst-case}}[V]\ =\ \inf_{\lambda\ge0}\Big\{\lambda\varepsilon+\mathbb{E}_{\hat\mu}\big[\sup_x(V(x)-\lambda\|x-\hat x\|^2)\big]\Big\}.$$
The first inequality is definitional (membership in the ball); the equality is `wdro_dual`
(Blanchet–Murthy Thm 1 / Gao–Kleywegt Thm 1). The card's *verification* (cost $\le$ bound for
in-ball perturbations) needs only the first inequality together with the **weak-duality upper
bound**, which is the fully proven `wdro_lagrangian_bound` (B–M eq. 5, G–K Prop. 1, E–K Cor. 4.3).

**Worst-case shift / Gaussian closed form.** The DRSB code's closed-form Gaussian worst-case is
justified by the worst-case-distribution characterizations: the optimizer transports nominal mass
along the cost-optimal direction $x\in\arg\max_z(V(z)-\lambda^*\|z-\hat x\|^2)$
(**B–M Remark 2**), realized as a pushforward $\mu^*=p^*\overline T_\#\nu+(1-p^*)\underline T^*_\#\nu$
(**G–K Corollary 1(ii)**, and the Gaussian instance **G–K Example 10 / §4.3**), i.e. discrete
atoms $\hat\xi_i-q_{ik}/\alpha_{ik}$ in the empirical case (**E–K Theorem 4.4 / Corollary 4.6**).
For a Gaussian nominal the optimal transport map is affine, so $\mu^*$ is a shifted Gaussian —
the DRSB code's closed form. **(paraphrase — the "shifted-Gaussian" phrasing is the DRSB
paper's; the papers above supply the transport-map structure that makes it exact, not a literal
"shifted Gaussian" statement.)**

**SDRO note (out of scope for these three papers).** The Sinkhorn/entropic variant `sdro_dual` /
`M_logPartition` replaces the inner $\sup_x$ by a log-partition (soft-max) via the
Donsker–Varadhan / Gibbs variational principle; that comes from the entropic-OT literature, not
from these three Wasserstein-DRO sources, and is documented separately in the scaffold's
`WellKnown` lemmas.
