# Schrödinger Bridge ⇄ Stochastic Optimal Control ⇄ Entropic Optimal Transport

Faithful prose transcription of the two backbone references for the DRSB
formalization. The subject of this file is the *Schrödinger-bridge / stochastic
optimal-control / entropic-OT* chain that defines the DRSB value function

$$
V(x) \;=\; \mathbb{E}\!\left[\int_0^1 \tfrac12\|u_t\|^2\,dt \;+\; \rho\, g(X_1)\;\middle|\; X_0 = x\right],
$$

its optimal control $u^\* = -\nabla V$ (Hopf–Cole / Fleming logarithmic
transform), and the reference (prior) dynamics.

## Sources

1. **Chen, Georgiou, Pavon (2020/2021)** — *"Stochastic control liaisons:
   Richard Sinkhorn meets Gaspard Monge on a Schrödinger bridge."*
   arXiv:[2005.10963](https://arxiv.org/abs/2005.10963) (v3, 26 Nov 2020; published in *SIAM Review* 63(2), 2021).
   Local PDF: `prose/papers/chen-georgiou-pavon-2020_stochastic-control-liaisons-schrodinger-bridge__arXiv-2005.10963.pdf` (not committed).
   Cited below as **CGP**. Equation/Problem/Theorem numbers below are those printed in the arXiv v3 text.
2. **Léonard (2013)** — *"A survey of the Schrödinger problem and some of its
   connections with optimal transport."*
   arXiv:[1308.0215](https://arxiv.org/abs/1308.0215) (v1, 1 Aug 2013; *Discrete Contin. Dyn. Syst. A* 34(4), 2014).
   Local PDF: `prose/papers/leonard-2013_survey-schrodinger-problem-optimal-transport__arXiv-1308.0215.pdf` (not committed).
   Cited below as **Léonard**. Numbers below are those printed in the arXiv v1 text.

> **Transcription conventions.** Displayed equations quote the papers'
> statements; where I paraphrase or compress an argument I say so explicitly.
> Equation labels of the form `(4.20)` are the papers' *own* printed numbers,
> reproduced (not invented). A short **Proof sketch** follows each core result.
> Sign conventions: both papers write the optimal drift as $u^\* = +\nabla(\log\varphi)$
> with $\log\varphi$ a *co-state / space-time-harmonic potential*; the DRSB scaffold
> writes $u^\* = -\nabla V$ with $V$ a *minimized cost-to-go*. These reconcile via
> $V = -\log\varphi$ (equivalently $V=-\lambda=-\psi$ in the notation below); see the
> final correspondence section.

## Role in the DRSB chain

DRSB trains a Schrödinger-bridge / SOC generative model and proves a
distributionally-robust worst-case bound on its value function $V(x)$. The two
papers supply the *non-robust backbone* that gives $V$ meaning: CGP establishes
the exact equivalence **Schrödinger bridge (KL minimization over path measures)
⇄ stochastic optimal control (minimize $\mathbb{E}\!\int \tfrac12\|u\|^2$)
⇄ fluid-dynamic / Benamou–Brenier problem**, together with the Hopf–Cole
logarithmic transform giving the optimal feedback control $u^\* = \nabla\log\varphi$
and the Sinkhorn / entropic-OT reading of the *static* bridge. Léonard supplies
the rigorous large-deviations foundation for the KL formulation, the
$h$-transform (Markov) structure of the bridge solution, and the
$\Gamma$-convergence / small-noise ("slowing down") limit in which entropic
transport degenerates to Monge–Kantorovich OT. Everything the Lean scaffold
names — `schrodingerBridgeValue`, `energy`, `sbObjective`, `socObjective`/`socValue`,
`V0`, `Dynamics`, `optimal_control_eq_neg_grad_value` — is a specialization of an
object transcribed below.

---

## Part I — Chen, Georgiou, Pavon (arXiv:2005.10963)

### I.0 Setup and notation

Let $\Omega = C([0,1];\mathbb{R}^n)$ be path space, $\mathcal{D}$ the probability
measures on $\Omega$, and $W_x$ Wiener measure started at $x$. The **stationary
Wiener measure** $W := \int W_x\,dx$ is an unbounded nonnegative "uniformizing"
reference on $\Omega$ (Lebesgue marginals at every time); $W^\epsilon$ denotes
Wiener measure of variance $\epsilon$ with heat kernel

$$
p^\epsilon(0,x,1,y) = [2\pi\epsilon]^{-n/2}\exp\!\Big(-\tfrac{\|x-y\|^2}{2\epsilon}\Big).\tag{4.1'}
$$

Relative entropy (KL divergence) between nonnegative measures is
$D(P\|Q) = \mathbb{E}_P[\log \tfrac{dP}{dQ}]$ if $P \ll Q$, $+\infty$ otherwise
(CGP, unnumbered display before eq. (4.6)). $\mathcal{D}(\rho_0,\rho_1)$ is the
set of path laws with marginals $\rho_0$ at $t=0$ and $\rho_1$ at $t=1$;
$\Pi(\rho_0,\rho_1)$ the couplings (joint endpoint laws with those two marginals).

### I.1 The Schrödinger Bridge Problem as KL minimization (Problem 4.1)

CGP arrive at the bridge as the *most likely* random evolution consistent with
two observed marginals. By Sanov's theorem the probability of observing empirical
path-distribution $\mu_N$ near $\mathcal{D}(\rho_0,\rho_1)$ decays like
$e^{-N\inf\{D(P\|W_\rho)\,|\,P\in\mathcal{D}(\rho_0,\rho_1)\}}$, and Gibbs
conditioning selects the KL-closest law. Using
$D(P\|W_\rho) = D(P\|W) - D(\rho_0\|\rho)$ this reduces to:

> **Problem 4.1 (Schrödinger Bridge Problem).**
> $$
> P_{\mathrm{SBP}} := \arg\min\{\, D(P\|W) \;\mid\; P \in \mathcal{D}(\rho_0,\rho_1)\,\}.\tag{4.3}
> $$

The minimizer's time-marginal flow $\{\rho(t,\cdot)\}$ is the **entropic
interpolation** between $\rho_0$ and $\rho_1$.

### I.2 Reduction to a static problem (Problem 4.2)

For a finite-energy diffusion $P$ with Itô differential $dX_t = \beta_t\,dt + dW_t$
and $\mathbb{E}_P\!\int_0^1\|\beta_t\|^2 dt<\infty$ (CGP (4.4)–(4.5)), the relative
entropy disintegrates over endpoints as

$$
D(P\|W) = \iint \log\!\frac{\rho^P_{01}(x,y)}{\rho^W_{01}(x,y)}\,\rho^P_{01}(x,y)\,dx\,dy
\;+\; \iiint \log\!\frac{dP_{xy}}{dW_{xy}}\,dP_{xy}\,\rho^P_{01}(x,y)\,dx\,dy.\tag{4.6}
$$

The second term is minimized (to $0$) by choosing the *bridges* $P_{xy}=W_{xy}$,
so Problem 4.1 reduces to a static coupling problem:

> **Problem 4.2 (static Schrödinger problem).** Minimize
> $$
> D(\rho_{01}\|\rho^W_{01}) = \iint \log\!\Big(\tfrac{\rho_{01}(x,y)}{\rho^W_{01}(x,y)}\Big)\rho_{01}(x,y)\,dx\,dy \tag{4.7}
> $$
> over couplings $\rho_{01} \in \Pi(\rho_0,\rho_1)$.

If $\rho^\*_{01}$ solves (4.7) then $P^\*(\cdot)=\int W_{xy}(\cdot)\,\rho^\*_{01}(dx\,dy)$
solves (4.3) (CGP (4.8)); $P^\*$ lies in the same *reciprocal class* as the prior.

**Proof sketch.** Endpoint disintegration (4.6) splits $D(P\|W)$ into a coupling
term plus a nonnegative bridge term; the bridge term vanishes iff $P$ shares $W$'s
bridges, and the coupling term is exactly (4.7). Hence the infimum over path
measures equals the infimum over couplings, attained by gluing $W$'s bridges onto
the optimal coupling.

### I.3 Entropic regularization of Optimal Mass Transport (eqs (4.9)–(4.10))

With prior of variance $\epsilon$, using $\rho^{W^\epsilon}_{01}(x,y)=\rho_0(x)\,p^\epsilon(0,x,1,y)$,
(4.7) becomes (CGP (4.9)–(4.10)):

$$
\min_{\rho_{01}\in\Pi(\rho_0,\rho_1)} \;\int\!\!\int \tfrac{\|x-y\|^2}{2}\,\rho_{01}(x,y)\,dx\,dy
\;+\;\epsilon\int\!\!\int \rho_{01}(x,y)\log\rho_{01}(x,y)\,dx\,dy.\tag{4.10}
$$

As $\epsilon\to 0$ the cost reduces to the Kantorovich functional $\tfrac12\|x-y\|^2$:
**the Schrödinger bridge is an entropic regularization of quadratic OMT**, obtained
by subtracting an entropy term. (This is the "temperature $\to 0$" statement.)

### I.4 The Schrödinger system (Section 4.3, eqs (4.11)–(4.14))

Setting the first variation of the Lagrangian of Problem 4.2 to zero forces the
optimal coupling to *factor*:

$$
\rho^\*_{01}(x,y) = \hat\varphi(x)\,p(0,x,1,y)\,\varphi(y),\tag{4.11}
$$

with $(\hat\varphi,\varphi)$ solving the **Schrödinger system**

$$
\hat\varphi(x)\!\int p(0,x,1,y)\varphi(y)\,dy = \rho_0(x),\qquad
\varphi(y)\!\int p(0,x,1,y)\hat\varphi(x)\,dx = \rho_1(y),\tag{4.12–4.13}
$$

equivalently the coupled forward/backward integral system (4.14a)–(4.14b) with the
nonlinear boundary coupling $\varphi(0,x)\hat\varphi(0,x)=\rho_0(x)$,
$\varphi(1,y)\hat\varphi(1,y)=\rho_1(y)$ (4.14c). The marginal factors as
$\rho(t,x)=\varphi(t,x)\hat\varphi(t,x)$ (4.15) — a Euclidean analogue of Born's
rule. Existence/uniqueness (up to $\varphi\mapsto c\varphi$, $\hat\varphi\mapsto \hat\varphi/c$)
is the Fortet–Beurling–Jamison theory.

**Proof sketch.** The multiplier stationarity condition
$1+\log\rho^\*_{01}-\log p -\log\rho^W_0 + \lambda(x)+\mu(y)=0$ makes
$\rho^\*_{01}/p$ a product of a function of $x$ and a function of $y$; naming these
$\hat\varphi,\varphi$ gives (4.11), and the marginal constraints give (4.12)–(4.13).

### I.5 Stochastic control formulation (Section 4.4, Problem 4.3) — defines `energy`, `schrodingerBridgeValue`

By Girsanov's theorem, for a finite-energy diffusion the martingale term has zero
expectation, yielding the **energy identity**

$$
D(P\|W) = D(\rho_0\|\rho^W_0) + \mathbb{E}_P\!\left[\int_0^1 \tfrac12\|\beta_t\|^2\,dt\right],\tag{4.19}
$$

with the first term constant over $\mathcal{D}(\rho_0,\rho_1)$. Minimizing KL is
therefore *equivalent* to minimizing control energy:

> **Problem 4.3 (SB as stochastic optimal control).**
> $$
> \min_{u\in\mathcal{U}}\; J(u) = \mathbb{E}\!\left[\int_0^1 \tfrac12\|u_t\|^2\,dt\right],\qquad
> dX_t = u_t\,dt + \sqrt{\epsilon}\,dW_t,\ \ X_0\sim\rho_0,\ X_1\sim\rho_1.\tag{4.20}
> $$
> The optimal control is the feedback
> $$
> u^\*(t,x) = \nabla\log\varphi(t,x),\tag{4.21}
> $$
> where $(\varphi,\hat\varphi)$ solve the PDE Schrödinger system
> $$
> \tfrac{\partial\varphi}{\partial t} + \tfrac{\epsilon}{2}\Delta\varphi = 0,\qquad
> \tfrac{\partial\hat\varphi}{\partial t} - \tfrac{\epsilon}{2}\Delta\hat\varphi = 0,\tag{4.22a–b}
> $$
> $$
> \varphi(0,x)\hat\varphi(0,x)=\rho_0(x),\qquad \varphi(1,y)\hat\varphi(1,y)=\rho_1(y).\tag{4.22c–d}
> $$

Equation (4.21) is the **Hopf–Cole / Fleming logarithmic transform**: the optimal
drift is the gradient of $\log$ of the forward potential $\varphi$, which itself
solves the *backward heat equation* (4.22a). This is exactly the "$u^\* = \nabla(\text{value})$"
relationship — see §I.7 for the HJB / value-function form and the sign.

**Proof sketch.** Girsanov gives $\log\frac{dP}{dW}$ as a stochastic integral plus
$\int_0^1\tfrac12\|\beta_t\|^2dt$; the finite-energy condition kills the martingale
term in expectation, giving (4.19). Since the endpoint term is constant on the
feasible set, minimizing $D(P\|W)$ is minimizing $\mathbb{E}\!\int\tfrac12\|\beta\|^2$.
The Doob/$h$-transform representation $p^\*(0,x,1,y)=\varphi(x)^{-1}p(0,x,1,y)\varphi(y)$
(from (4.11), CGP (4.16)) with $\varphi$ space-time harmonic
($\partial_t\varphi+\tfrac{\epsilon}2\Delta\varphi=0$, CGP (4.17)) identifies the
optimal drift as $\nabla\log\varphi$.

### I.6 Fluid-dynamic / Benamou–Brenier formulation (Section 4.5, Problem 4.4)

> **Problem 4.4 (fluid-dynamic SB).**
> $$
> \inf_{(\rho,u)} \int_{\mathbb{R}^n}\!\!\int_0^1 \tfrac12\|u(t,x)\|^2\,\rho(t,x)\,dt\,dx \tag{4.23a}
> $$
> subject to the Fokker–Planck constraint
> $$
> \tfrac{\partial\rho}{\partial t} + \nabla\!\cdot(u\rho) - \tfrac{\epsilon}{2}\Delta\rho = 0,\qquad
> \rho(0,\cdot)=\rho_0,\ \rho(1,\cdot)=\rho_1.\tag{4.23b–c}
> $$

As $\epsilon\downarrow 0$ this converges to the **Benamou–Brenier** characterization
of OMT (the dynamic $W_2^2$ problem, CGP (3.5)). *Caveat* (CGP Remark 4.5): Problem
4.4 reproduces only the optimal marginal flow $\{\rho^\*(t,\cdot)\}$, not the full
path law $P^\*$. A time-symmetric variant (Problem 4.6, (4.25)) differs by a scaled
Fisher-information functional.

### I.7 OMT / SB as HJB control; the value-gradient control (Props 3.2, 3.4, 5.1; Thm 5.2) — defines `socObjective`, `V0`, `optimal_control_eq_neg_grad_value`

The variational analysis of the Benamou–Brenier problem introduces a $C^1$
multiplier $\lambda(t,x)$ (the **value function / co-state**). Pointwise
minimization of the Lagrangian integrand over the control gives the optimal
feedback as a *value gradient*, and $\lambda$ solves a Hamilton–Jacobi(–Bellman)
equation:

> **Proposition 3.2 (OMT via HJB).** If $\rho^\*$ solves the continuity equation
> $\partial_t\rho^\* + \nabla\!\cdot(\rho^\*\nabla\lambda)=0$, $\rho^\*(0,\cdot)=\rho_0$
> (3.19), with $\lambda$ a solution of the Hamilton–Jacobi equation
> $$
> \tfrac{\partial\lambda}{\partial t} + \tfrac12\|\nabla\lambda\|^2 = 0,\tag{3.20}
> $$
> and $\rho^\*(1,\cdot)=\rho_1$, then $(\rho^\*, v^\*)$ with $v^\*(t,x)=\nabla\lambda(t,x)$ (3.16) solves the OMT problem (3.5).

> **Proposition 3.4 (OMT with a prior drift $f$).** With HJB
> $\partial_t\lambda + f\!\cdot\!\nabla\lambda + \tfrac12\|\nabla\lambda\|^2=0$ (3.26)
> and continuity $\partial_t\rho^\* + \nabla\!\cdot[(f+\nabla\lambda)\rho^\*]=0$ (3.27),
> the pair $v^\*=f+\nabla\lambda$ solves the prior-anchored transport (3.23).

> **Proposition 5.1 / Theorem 5.2 (general controlled diffusion, log transform).**
> For the general problem (5.3) $\inf_{(\rho,u)}\int(\tfrac12\|u\|^2+V)\rho$ subject to
> $\partial_t\rho+\nabla\!\cdot((f+\sigma u)\rho)=\tfrac12\sum\partial^2_{ij}(a_{ij}\rho)$,
> the pointwise-optimal control is
> $$
> u^\*_\rho(t,x) = \sigma'\nabla\lambda(t,x),\tag{5.5}
> $$
> with $\lambda$ solving the HJB-type equation
> $$
> \tfrac{\partial\lambda}{\partial t} + f\!\cdot\!\nabla\lambda
> + \tfrac12\!\sum_{i,j} a_{ij}\tfrac{\partial^2\lambda}{\partial x_i\partial x_j}
> + \tfrac12\nabla\lambda\!\cdot\! a\nabla\lambda - V = 0.\tag{5.8}
> $$
> **Logarithmic (Hopf–Cole) transform:** setting $\varphi = \exp[\lambda]$ *linearizes*
> (5.8) into the linear (backward Feynman–Kac / heat) equation
> $\partial_t\varphi + f\!\cdot\!\nabla\varphi + \tfrac12\sum a_{ij}\partial^2_{ij}\varphi = V\varphi$
> (5.9), and $\hat\varphi=\rho/\varphi$ solves the adjoint (forward) equation, giving the
> **generalized Schrödinger system** (5.10a)–(5.10c). Then **(Theorem 5.2)** the optimal
> pair $(\rho^\*,u^\*)$ has
> $$
> \boxed{\,u^\*(t,x) = \sigma'\nabla\log\varphi(t,x)\,}\tag{5.11a}
> $$
> When $a=\sigma\sigma'=\sigma^2 I$ this is $u^\*=\sigma^2\nabla\log\varphi=\sigma^2\nabla\lambda$,
> the "$u^\*=\sigma^2\nabla(\text{value})$" form.

**Proof sketch (5.1 / 5.2).** Integrate the Lagrangian by parts; the endpoint term
is constant on the feasible flow set and is discarded. The integrand is quadratic
in $u$, $\tfrac12\|u\|^2 + \sigma'\!\nabla\lambda\!\cdot\!u + (\text{$u$-free})$, so
completing the square gives minimizer $u^\* = \sigma'\nabla\lambda$ (5.5).
Substituting back leaves the HJB residual (5.8) as the coefficient of $\rho$; forcing
it to vanish makes the reduced functional identically zero, so any feasible flow is
optimal. The exponential change of variables $\varphi=e^{\lambda}$ turns the quadratic
HJB into the *linear* PDE (5.9) — this is the Hopf–Cole linearization — whence
$u^\*=\sigma'\nabla\lambda=\sigma'\nabla\log\varphi$. **Remark 5.3:** the change of
variables $m=\rho u$ renders (5.3) *jointly convex* in $(\rho,m)$ (eq. (5.12)).

> **Sign note (load-bearing for the Lean scaffold).** In CGP the completed square is
> $\tfrac12\|u\|^2 + \langle u, p\rangle = \tfrac12\|u+p\|^2 - \tfrac12\|p\|^2$ with
> co-state $p = -\sigma'\nabla\lambda$, so $u^\* = -p = +\sigma'\nabla\lambda$. The DRSB
> value function $V$ is the *minimized cost-to-go*, related to the co-state potential by
> $V = -\lambda = -\log\varphi$ (up to additive/scaling constants), giving
> $u^\* = -\nabla V$. This is exactly the completing-the-square argument reproduced in
> `V4.lean`'s comment for `optimal_control_eq_neg_grad_value`.

### I.8 Sinkhorn / entropic-OT connection (Section 7) and Fortet–IPF–Sinkhorn (Section 8)

**Static SB = entropic OT = free-energy minimization.** In the discrete setting, the
entropically-regularized transport problem
$\inf_{\pi\in\Pi(p,q)}\{\sum c_{ij}\pi_{ij} - \epsilon S(\pi)\}$ (CGP (7.2)–(7.3),
$S(\pi)=-\sum\pi_{ij}\log\pi_{ij}$) coincides with minimizing the **Helmholtz free
energy** $F(\pi,T)=U(\pi)-T S_G(\pi)$ (7.9) with $\epsilon=kT$, whose unconstrained
minimizer is the **Boltzmann/Gibbs distribution**
$\pi_B(i,j)=Z(T)^{-1}\exp(-c_{ij}/kT)$ (7.10, 7.14). Because
$F(\pi,T)=T\,D(\pi\|\pi_B) - T\log Z(T)$ (7.11), the constrained problem is

$$
\min_{\pi\in\Pi(p,q)} D(\pi\|\pi_B),\tag{7.13}
$$

a **discrete counterpart of Problem 4.2** (static SB). The optimizer factors as
$\pi^\*_{ij}=\hat\varphi(i)\,p_B(i,j)\,\varphi(j)$ (7.17), i.e.
$P^\* = \operatorname{diag}(1/\varphi(0,\cdot))\,P_B\,\operatorname{diag}(\varphi(1,\cdot))$
(7.22) — the **matrix-scaling (Sinkhorn) form** of the Schrödinger system
(7.20a)–(7.20d).

> **Theorem 8.1 (Fortet–IPF–Sinkhorn convergence).** Let $p,q\in\mathcal{D}(\mathcal{X})$
> and $G=(g_{ij})$ have all-positive entries. Then there exist positive vectors
> $\varphi(0,\cdot),\hat\varphi(1,\cdot)$ solving the Schrödinger system (8.4a)–(8.4d)
> ($\varphi(0,i)=\sum_j g_{ij}\varphi(1,j)$, $\hat\varphi(1,j)=\sum_i g_{ij}\hat\varphi(0,i)$,
> $\varphi(0,i)\hat\varphi(0,i)=p_i$, $\varphi(1,j)\hat\varphi(1,j)=q_j$), unique up to the
> scaling $\varphi\mapsto\alpha\varphi$, $\hat\varphi\mapsto\hat\varphi/\alpha$.

**Proof sketch.** The Fortet/Sinkhorn iteration $\varphi^{k+1}(0)=C(\varphi^k(0))$ with
$C=E\circ D_1\circ E^{\dagger}\circ D_0$ (composition of the two linear kernels $E,E^\dagger$
and the two componentwise divisions $D_0:x\mapsto p/x$, $D_1:x\mapsto q/x$, eqs (8.5)–(8.6))
maps the open positive orthant into itself. Convergence to a fixed point (hence a solution of
(8.4)) follows from contraction of $C$ on the space of *rays* under **Hilbert's projective
metric** (Birkhoff–Bushell); uniqueness is uniqueness of rays. The continuous analogue is
Fortet's 1940 fixed-point map (8.3), the discrete case is classical IPF/Sinkhorn.

---

## Part II — Léonard (arXiv:1308.0215)

### II.0 Setup and notation

$X=\mathbb{R}^n$ or a complete connected Riemannian manifold; $\Omega=C([0,1],X)$;
$(X_t)$ the canonical process. $R\in M_+(\Omega)$ is the **reference path measure**,
typically the **reversible Brownian motion** (generator $L=\Delta/2$, initial law =
volume/Lebesgue measure), which is an *unbounded* measure. Relative entropy
$H(P|R)=\int\log(dP/dR)\,dP\in(-\infty,\infty]$ (eq. (2.1)). Marginals
$P_t=(X_t)_\#P$, endpoint law $R_{01}=(X_0,X_1)_\#R$, bridge $R^{xy}=R(\cdot\mid X_0=x,X_1=y)$.

### II.1 Dynamic and static Schrödinger problems (Definitions 2.1, 2.2)

> **Definition 2.1 (dynamic Schrödinger problem).**
> $$
> H(P|R) \to \min;\qquad P\in\mathcal{P}(\Omega):\ P_0=\mu_0,\ P_1=\mu_1.\tag{$S_{\mathrm{dyn}}$}
> $$

> **Definition 2.2 (static Schrödinger problem).** With $R_{01}=(X_0,X_1)_\#R$,
> $$
> H(\pi|R_{01}) \to \min;\qquad \pi\in\mathcal{P}(X^2):\ \pi_0=\mu_0,\ \pi_1=\mu_1.\tag{$S$}
> $$

Both are strictly convex, hence have at most one solution. For reversible Brownian
motion the endpoint reference is $R_{01}(dx\,dy)\propto \exp(-d(x,y)^2/2)\,\mathrm{vol}(dx)\,\mathrm{vol}(dy)$
(eq. (1.2)), i.e. a Gibbs kernel with quadratic cost $c(x,y)=d^2(x,y)/2$. This is the
measure-theoretic form of CGP's Problem 4.1 (dynamic) and Problem 4.2 (static).

### II.2 Equivalence and disintegration (Proposition 2.3, Föllmer)

> **Proposition 2.3 (Föllmer).** $(S_{\mathrm{dyn}})$ and $(S)$ each have at most one
> solution. If $\widehat P$ solves $(S_{\mathrm{dyn}})$ then $\widehat\pi=\widehat P_{01}$
> solves $(S)$; conversely if $\widehat\pi$ solves $(S)$ then
> $$
> \widehat P(\cdot) = \int_{X^2} R^{xy}(\cdot)\,\widehat\pi(dx\,dy)\tag{2.2}
> $$
> solves $(S_{\mathrm{dyn}})$, with $\widehat P_{01}=\widehat\pi$ and
> $\widehat P^{xy}=R^{xy}$ for $\widehat\pi$-a.e. $(x,y)$. In particular
> $\inf(S_{\mathrm{dyn}})=\inf(S)$.

**Proof sketch.** The additive/tensorization property of relative entropy under
endpoint disintegration gives $H(P|R)=H(P_{01}|R_{01})+\int H(P^{xy}|R^{xy})\,P_{01}(dx\,dy)$,
so $H(P_{01}|R_{01})\le H(P|R)$ with equality iff $P^{xy}=R^{xy}$ $P_{01}$-a.e. Hence
the dynamic optimizer shares $R$'s bridges and is obtained by gluing them onto the
static optimizer. (Measure-theoretic version of CGP's (4.6) argument.)

### II.3 Product-form solution and the Schrödinger system (Theorems 2.8, 2.9)

> **Theorem 2.8 (static, product form).** Under the stated regularity/integrability
> hypotheses (i)–(vii) on $R$ and $(\mu_0,\mu_1)$, $(S)$ has a unique solution
> $$
> \widehat\pi(dx\,dy) = f_0(x)\,g_1(y)\,R_{01}(dx\,dy),
> $$
> where the positive functions $f_0,g_1$ solve the **Schrödinger system**
> $$
> f_0(x)\,\mathbb{E}_R[g_1(X_1)\mid X_0=x] = \tfrac{d\mu_0}{dm}(x),\qquad
> g_1(y)\,\mathbb{E}_R[f_0(X_0)\mid X_1=y] = \tfrac{d\mu_1}{dm}(y).\tag{2.11}
> $$

> **Theorem 2.9 (dynamic).** Under the same hypotheses, $(S_{\mathrm{dyn}})$ has the
> unique solution $\widehat P = f_0(X_0)\,g_1(X_1)\,R\in\mathcal{P}(\Omega)$ (eq. (2.12)),
> with $f_0,g_1$ solving (2.11).

**Proof sketch.** In restriction to the (compact, tight) constraint set
$\Pi(\mu_0,\mu_1)$, $H(\cdot|R_{01})$ is lower-bounded and lower-semicontinuous
(via a tilt by $e^{-B\oplus B}$, eq. (2.6)), so a minimizer exists when the value is
finite (Prop 2.5). First-order optimality forces the Radon–Nikodym derivative
$d\widehat\pi/dR_{01}$ to factor as $f_0(x)g_1(y)$, whose marginal constraints are
(2.11). Theorem 2.9 then follows from Proposition 2.3 by gluing bridges.

### II.4 Markov / $h$-transform structure (Proposition 2.10, Theorem 2.12, Definition 3.2, Theorems 3.3–3.4)

> **Proposition 2.10.** If the reference $R$ is Markov, then the solution $\widehat P$ of
> $(S_{\mathrm{dyn}})$ is Markov.

> **Theorem 2.12 (Markov case).** If $R$ is Markov (plus (ii)–(vii)), the unique
> solution is $\widehat P=f_0(X_0)g_1(X_1)R$, Markov, with $f_0,g_1$ solving (2.11)
> — now allowed to *vanish* on some sets. Conversely any such product measure solves
> $(S_{\mathrm{dyn}})$.

> **Definition 3.2 ($(f,g)$-transform).** For nonnegative measurable $f_0,g_1$ with
> $\mathbb{E}_R[f_0(X_0)g_1(X_1)]=1$, the law $P:=f_0(X_0)\,g_1(X_1)\,R$ is the
> **$(f,g)$-transform** of $R$ — a *time-symmetric version of Doob's $h$-transform*.

> **Theorem 3.4 (Euclidean analogue of Born's formula).** $P=f_0(X_0)g_1(X_1)R$ is
> Markov and its time marginal is
> $$
> P_t = f_t\,g_t\,m,\qquad f_t(z)=\mathbb{E}_R[f_0(X_0)\mid X_t=z],\ \ g_t(z)=\mathbb{E}_R[g_1(X_1)\mid X_t=z].\tag{3.4}
> $$

**Proof sketch (2.10).** If $\widehat P$ were non-Markov at some $t$, replacing its
conditional past/future by their independent product (Claim 2.11) strictly lowers
$H(\cdot|R)$ while preserving all time-marginals, contradicting optimality; convexity
of relative entropy + Jensen gives the strict inequality. **(3.4):** the product shape
of the density plus the Markov property give the multiplicative structure
$P_t=f_tg_t\,m$; the factor $\varphi_t=g_t$ is space-time harmonic, $\hat\varphi_t=f_t$
solves the adjoint equation (the measure-theoretic Born factorization $\rho=\varphi\hat\varphi$).

### II.5 Entropic HJB and the Benamou–Brenier representation (Section 4, Proposition 4.1) — the $u^\*=\nabla\log g$ transform

For reversible Brownian motion ($L=\Delta/2$), the $(f,g)$-transform has forward and
backward generators (eq. (4.2))
$\overrightarrow{A}_t=\Delta/2+\nabla\psi_t\!\cdot\!\nabla$,
$\overleftarrow{A}_t=\Delta/2+\nabla\varphi_t\!\cdot\!\nabla$, and the forward potential
$\psi_t=\log g_t$ solves the **Hamilton–Jacobi–Bellman equation**

$$
(\partial_t + \tfrac12\Delta)\psi_t(x) + \tfrac12\|\nabla\psi_t(x)\|^2 = 0,\quad (t,x)\in[0,1)\times X,\qquad \psi_1=\log g_1.\tag{4.3}
$$

with time-reversal identity $\nabla\psi_t+\nabla\varphi_t=\nabla\log\mu_t$. The optimal
forward drift of the bridge is $\nabla\psi_t=\nabla\log g_t$ — Léonard's form of the
Hopf–Cole / Fleming logarithmic transform (CGP (4.21)/(5.11a)).

> **Proposition 4.1 (Benamou–Brenier representation of the entropic problem).** For
> $\mu_0,\mu_1\in\mathcal{P}_2(\mathbb{R}^n)$ with finite entropy, $(S_{\mathrm{dyn}})$
> has a unique solution $\widehat P$, and the minimal-action problem
> $\inf_{(\nu,v)}\int \tfrac12|v_t(x)|^2\,\nu_t(dx)\,dt$ (subject to the
> Fokker–Planck constraint (4.5)) is solved by $((\mu_t),\nabla\psi)$ with
> $$
> \mu_t=\widehat P_t,\qquad \psi_t(x)=\log \mathbb{E}_R[g_1(X_1)\mid X_t=x],
> $$
> $\psi$ the unique classical solution of the HJB equation (4.3), and (eq. (4.6))
> $$
> \inf(S_{\mathrm{dyn}}) - H(\mu_0|m)
> = \int_{[0,1]\times\mathbb{R}^n}\tfrac12\|\nabla\psi_t(x)\|^2\,\mu_t(dx)\,dt
> = \inf_{(\nu,v)}\int \tfrac12\|v_t\|^2\,\nu_t(dx)\,dt.
> $$

**Proof sketch.** By Girsanov, any finite-entropy $Q$ has a drift $\beta$ with
$H(Q|R)=H(Q_0|m)+\mathbb{E}_Q\!\int\tfrac12|\beta_t|^2dt$ (eq. (4.7)) — the exact
analogue of CGP's energy identity (4.19). Conversely any admissible $(\nu,v)$ lifts to
a path measure of that entropy. Minimizing over drifts subject to the marginal flow
matches the kinetic action, whose optimizer is the gradient field $\nabla\psi$; the
$L^2(\mu_t\,dt)$-projection argument shows $\nabla\psi$ is the *unique* optimal field.

### II.6 Small-noise / $\Gamma$-convergence limit to OMT (Section 5) — entropic OT $\to$ OT as temperature $\to 0$

Slow the reference down: $R^k$ has generator $L_k=L/k$ and satisfies a large-deviation
principle with speed $\alpha_k$ and rate function $C$ (eq. (5.1)). Consider the
renormalized problems

$$
H(P|R^k)/\alpha_k \to \min\ \ (S^k_{\mathrm{dyn}}),\qquad H(\pi|R^k_{01})/\alpha_k \to \min\ \ (S^k).
$$

> **Informal Statement 5.1 / Theorem 5.2 ($\Gamma$-convergence).** Under the LDP (5.1),
> $$
> \Gamma\text{-}\lim_{k\to\infty}(S^k_{\mathrm{dyn}}) = (\mathrm{MK}_{\mathrm{dyn}}),\qquad
> \Gamma\text{-}\lim_{k\to\infty}(S^k) = (\mathrm{MK}),
> $$
> where $(\mathrm{MK})$ is Monge–Kantorovich with cost
> $c(x,y)=\inf\{C(\omega):\omega_0=x,\omega_1=y\}$ (eq. (5.3)). The sequences of
> functionals are *equi-coercive*, so $\lim_k \inf(S^k)=\inf(\mathrm{MK})$ and every
> limit point of the minimizers $\widehat P^k$ (resp. $\widehat\pi^k$) solves
> $(\mathrm{MK}_{\mathrm{dyn}})$ (resp. $(\mathrm{MK})$). For reversible Brownian
> motion: $\alpha_k=k$, $C(\omega)=\int_0^1\tfrac12|\dot\omega_t|^2\,dt$,
> $c(x,y)=\tfrac12|y-x|^2$, recovering the entropic $\to$ quadratic-OT limit (1.11)–(1.12);
> the bridges collapse $R^{k,xy}\to\delta_{\gamma^{xy}}$ onto the constant-speed geodesic.

For each finite $k$ the entropic minimizer $\widehat P^k$ is a *smooth, positive* Markov
diffusion with generator $A^k_t=\nabla\psi^k_t\!\cdot\!\nabla+\Delta/(2k)$ and
$\psi^k$ solving the viscous HJB
$\partial_t\psi^k+\tfrac12|\nabla\psi^k|^2+\Delta\psi^k/(2k)=0$; as $k\to\infty$ this
degenerates to the inviscid Hamilton–Jacobi equation (1.8b) with Hopf–Lax solution
(1.9). **Thus the Schrödinger problem is a smooth (regularizing) approximation of OMT,
converging to it in the zero-noise / zero-temperature limit.**

**Proof sketch.** $\Gamma$-convergence is shown via the dual problems. The dual of
$(S^k)$ is (eq. (D)) $\sup_{\varphi_0,\psi_1}\{\int\varphi_0 d\mu_0+\int\psi_1 d\mu_1
-\alpha_k^{-1}\log\int e^{\alpha_k(\varphi_0\oplus\psi_1)}dR^k\}$. By the LDP (5.1) and
the Laplace–Varadhan lemma, $\alpha_k^{-1}\log\int e^{\alpha_k(\cdots)}dR^k \to
\sup_\Omega\{\varphi_0(X_0)+\psi_1(X_1)-C\}$, whose vanishing (after normalization) is
exactly the Kantorovich constraint $\varphi_0\oplus\psi_1\le c$. So the dual objectives
converge pointwise to the Kantorovich dual $(D_\infty)$; equi-coercivity upgrades this to
$\Gamma$-convergence with convergence of minimizers.

---

## DRSB / Lean scaffold correspondence

The DRSB value function is
$V(x)=\mathbb{E}\big[\int_0^1\tfrac12\|u_t\|^2 dt + \rho\,g(X_1)\mid X_0=x\big]$; the
non-robust backbone below is what the two papers pin down. Declarations are in
`V4.lean`, namespace `DRSB`.

| `V4.lean` declaration | Mathematical object | CGP source | Léonard source |
|---|---|---|---|
| `Dynamics` (fields `Q`, `P`) | Reference/prior path law and controlled path law $P^{u,\mu}$ of the SDE $dX=(f+\sigma u)dt+\sigma dW$ | Prior $W$ / $W^\epsilon$ (§I.0); controlled diffusion (4.4), (5.2) | Reference $R$ = reversible Brownian motion, $L=\Delta/2$ (4.1); controlled law $Q$ (Prop 4.1) |
| `energy u P` $=\int\!\int_0^1\tfrac12\|u_t\|^2 dt\,dP$ | Quadratic control energy $\mathbb{E}[\int_0^1\tfrac12\|u\|^2 dt]$ | $J(u)$ in Problem 4.3 (4.20); energy term of (4.19) | kinetic action $C$ (1.3); Girsanov energy (4.7) |
| `sbObjective u μ ρ ν` $=$ `energy` $+\,\rho\,\mathrm{KL}(P_1\|\nu)$ | Energy + soft terminal-marginal penalty; relaxation of the hard endpoint constraint via KL against reference $\nu$ | KL form $D(P\|W)$ (Problem 4.1, eq. (4.3)); energy split (4.19) | $H(P|R)$ with endpoint constraint ($S_{\mathrm{dyn}}$, Def 2.1) |
| `schrodingerBridgeValue μ0 ν` $=\inf_u\{$`energy`$: \mathrm{terminal}=\nu\}$ | SB value: minimal control energy steering $\mu_0\!\to\!\nu$ | value of Problem 4.3 (4.20); $=\inf$ of Problem 4.1 via (4.19) | $\inf(S_{\mathrm{dyn}})=\inf(S)$ (Prop 2.3); action value (4.6) |
| `socObjective`/`socValue` $=$ `energy` $+\,\rho\,\mathbb{E}[g(X_1)]$ | SOC with *terminal cost* $g$ (running $\tfrac12\|u\|^2$ + terminal $\rho g$) | HJB control problem (5.3) with terminal data; Prop 5.1 / Thm 5.2 | HJB (4.3) with terminal condition $\psi_1=\log g_1$ |
| `V0 ρ ν x` $=\inf_u J(u;\delta_x)$ | Pointwise value function $V(x)$ | value function / co-state $\lambda$ of (5.8); $V=-\lambda=-\log\varphi$ | HJB potential $\psi$ of (4.3); $V=-\psi$ (sign) |
| `optimal_control_eq_neg_grad_value`: $u^\*(0,x)=-\nabla V(x)$ | Optimal feedback = negative value-gradient (Hopf–Cole / Fleming log transform) | $u^\*=\nabla\log\varphi$ (4.21); $u^\*=\sigma'\nabla\log\varphi=\sigma'\nabla\lambda$ (5.11a); complete-the-square co-state $p=-\nabla\lambda$ | $u^\*=\nabla\psi=\nabla\log g_t$ (4.2)–(4.3), Prop 4.1 |

**Key reconciliations.**

- **`optimal_control_eq_neg_grad_value` (u\* = −∇V).** Both papers derive the optimal
  drift as the gradient of a *log-potential*: $u^\*=\nabla\log\varphi$ (CGP (4.21),
  Thm 5.2 (5.11a)) $=\nabla\psi$ (Léonard (4.3), $\psi=\log g$). The scaffold's
  `V0` is a *minimized cost* $V$, related to the potential by $V=-\log\varphi=-\psi$,
  so $u^\*=+\nabla\log\varphi=-\nabla V$. The `V4.lean` proof reproduces exactly the
  completing-the-square Hamiltonian argument
  $\tfrac12\|u\|^2+\langle u,p\rangle=\tfrac12\|u+p\|^2-\tfrac12\|p\|^2\Rightarrow u^\*=-p$
  with $p=\nabla V$ — i.e. CGP Prop 5.1 / Remark 5.3 specialized. The $\sigma^2$ scaling
  in the task's "$u^\*=\sigma^2\nabla\log\varphi$" is the isotropic case $a=\sigma\sigma'=\sigma^2 I$
  of CGP (5.11a).
- **`sbObjective` KL penalty vs. hard endpoint constraint.** CGP Problem 4.1 / Léonard
  $(S_{\mathrm{dyn}})$ impose $P_1=\nu$ *exactly*; the scaffold's $\rho\,\mathrm{KL}(P_1\|\nu)$
  is the Lagrangian/penalized relaxation of that constraint (recovered as $\rho\to\infty$),
  which is also the natural form for the DRSB robust wrapper.
- **Entropic-OT / Sinkhorn leg.** The scaffold's SDRO (Sinkhorn) ambiguity set and its
  soft-max/log-partition dual mirror CGP §7 (static SB $=\min D(\pi\|\pi_B)$ = entropic OT,
  Gibbs kernel $\pi_B\propto e^{-c/\epsilon}$) and the Fortet–IPF–Sinkhorn fixed point
  (Thm 8.1). Léonard §5 supplies the temperature $\to 0$ ($\Gamma$-convergence) degeneration
  entropic-OT $\to$ Monge–Kantorovich that justifies treating the bridge as a *regularized*
  transport.

---

### Unverified / paraphrased items (flagged)

- **All displayed equation, Problem, Proposition, and Theorem numbers above are as
  printed in the arXiv PDFs** (CGP v3 2005.10963; Léonard v1 1308.0215) and were read
  directly from the extracted text — none are invented.
- CGP eq. **(4.1')** (variance-$\epsilon$ heat kernel) is my label for the unnumbered
  displayed kernel appearing in CGP §4.2 just before eq. (4.9); the paper prints it
  without a number. Its zero-variance sibling (4.1) *is* numbered.
- The **table's "$V=-\lambda=-\psi$" sign identifications** are my interpretation
  reconciling the papers' co-state/potential convention with the scaffold's cost-to-go
  convention; the papers themselves write $u^\*=+\nabla\log\varphi$ and do not use the
  symbol $V$. Flagged as a paraphrase, not a quoted equation.
- CGP's SOC-with-terminal-cost `socObjective` correspondence uses the *general* HJB of
  Prop 5.1 / Thm 5.2 (which carries a potential term $V(t,x)$); the paper does not state
  a standalone "$\tfrac12\|u\|^2+\rho g(X_1)$" free-endpoint problem verbatim — that exact
  running-plus-terminal form is the scaffold's, matched here to (5.3)/(4.3) by the
  terminal boundary condition $\psi_1=\log g_1$.
