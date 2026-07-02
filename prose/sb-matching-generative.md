# Schrödinger-Bridge Matching & Generative Algorithms — Prose Reference

Provenance notes for the *generative / matching* machinery that the GaTech
**Distributionally-Robust Schrödinger Bridge (DRSB)** paper uses to actually
produce its bridge, its control $u$, and its terminal-cost network $g$. This
file documents the algorithmic ancestry of the DRSB estimator; it is not a full
transcription. Statements are quoted with the equation / theorem numbers as
**printed** in each source. Paraphrases are marked "(paraphrase)".

## Sources

1. Y. Shi, V. De Bortoli, A. Campbell, A. Doucet, **"Diffusion Schrödinger
   Bridge Matching" (DSBM)**, NeurIPS 2023. arXiv:2303.16852 —
   <https://arxiv.org/abs/2303.16852>
2. G.-H. Liu, Y. Lipman, M. Nickel, B. Karrer, E. A. Theodorou, R. T. Q. Chen,
   **"Generalized Schrödinger Bridge Matching" (GSBM)**, ICLR 2024.
   arXiv:2310.02233 — <https://arxiv.org/abs/2310.02233>
3. C. Domingo-Enrich, M. Drozdzal, B. Karrer, R. T. Q. Chen, **"Adjoint
   Matching: Fine-tuning Flow and Diffusion Generative Models with Memoryless
   Stochastic Optimal Control"**, ICLR 2025. arXiv:2409.08861 —
   <https://arxiv.org/abs/2409.08861>

The source PDFs are kept locally in `prose/papers/` for reference but are **not
committed** (see `.gitignore`: `prose/papers/*.pdf`).

## Role in the DRSB chain

DRSB proves a distributionally-robust worst-case bound on the value function
$V(x) = \mathbb{E}\!\left[\int_0^1 \tfrac12\|u_t\|^2\,dt + \rho\,g(X_1)\mid X_0=x\right]$
of a trained Schrödinger-bridge generative model. The three papers here supply
the *generative side*: **DSBM** gives the Iterative Markovian Fitting (IMF)
procedure whose fixed point is the Schrödinger bridge and the bridge-matching
regression that DRSB's `BridgeMatcher` (DSBM-style) implements; **GSBM**
generalizes the bridge objective with a running **state cost** $V_t$ and shows
the hard terminal constraint is equivalent to a **soft terminal cost**
$\phi(X_1)$ — the structural origin of DRSB's $\rho\,g(X_1)$ terminal term; and
**Adjoint Matching** casts reward fine-tuning as a control-affine SOC with cost
$\tfrac12\|u\|^2$ and terminal cost $g$, and derives the least-squares
**Adjoint Matching loss** $\tfrac12\int_0^1\|u(X_t,t)+\sigma(t)^\top\tilde a(t;X)\|^2dt$
with lean adjoint $\tilde a(1;X)=\nabla g(X_1)$ — the direct template for DRSB's
`AdjointMatcher` loss $\mathbb{E}\,\|u^\theta + \nabla g^\phi\|^2$ ("Algorithm 5:
Relaxed Schrödinger Bridge").

---

## 1. DSBM — Iterative Markovian Fitting (arXiv:2303.16852)

### Setup

A reference path measure $Q\in\mathcal M$ is the law of the SDE
$dX_t = f_t(X_t)dt + \sigma_t dB_t$, $X_0\sim Q_0$ (their eq. (1)). The
**Schrödinger Bridge** is (their eq. (6))

$$P^{\mathrm{SB}} = \arg\min_P \{ \mathrm{KL}(P\,|\,Q) : P_0=\pi_0,\ P_T=\pi_T \},$$

the path measure closest in KL to $Q$ that matches the two boundary marginals
$\pi_0,\pi_T$. Equivalently $P^{\mathrm{SB}}=\Pi^{\mathrm{SB}}_{0,T}Q_{|0,T}$ is a
mixture of $Q$-bridges over the static entropic-OT coupling.

A **mixture of bridges** is $\Pi=\Pi_{0,T}Q_{|0,T}$: sample endpoints
$(X_0,X_T)\sim\Pi_{0,T}$ and fill in the diffusion bridge $Q_{|0,T}(\cdot|x_0,x_T)$.
The **bridge-matching** regression that learns the marginal-matching drift is
(their eq. (3))

$$\mathbb{E}_{\Pi_{t,T}}\big[\,\|\sigma_t^2\nabla\log Q_{T|t}(X_T|X_t) - v_\theta(t,X_t)\|^2\,\big],$$

which for the Brownian bridge ($f_t=0,\sigma_t=\sigma$) reduces to the linear
target (their eq. (5))
$\mathbb{E}_{\Pi_{t,T}}[\|(X_T-X_t)/(T-t) - v_\theta(t,X_t)\|^2]$.

### Two projections

**Definition 1 (Markovian projection).** $M^\star=\mathrm{proj}_{\mathcal M}(\Pi)$
is the Markov SDE $dX_t^\star=\{f_t(X_t^\star)+v_t^\star(X_t^\star)\}dt+\sigma_t dB_t$
with $v_t^\star(x_t)=\sigma_t^2\,\mathbb{E}_{\Pi_{T|t}}[\nabla\log Q_{T|t}(X_T|X_t)\mid X_t=x_t]$.

**Proposition 2.** For $\sigma_t>0$, $M^\star=\arg\min_M\{\mathrm{KL}(\Pi\,|\,M):M\in\mathcal M\}$
(reverse-KL projection), and it preserves all marginals: $M_t^\star=\Pi_t$ for
every $t$ (in particular $M_T^\star=\Pi_T$). The learned version minimizes
(their eq. (10))
$\int_0^T\mathbb{E}_{\Pi_{t,T}}[\|\sigma_t^2\nabla\log Q_{T|t}(X_T|X_t)-v_\theta(t,X_t)\|^2]/\sigma_t^2\,dt$.

**Definition 3 (reciprocal class / projection).** $\Pi\in\mathcal R(Q)$ iff
$\Pi=\Pi_{0,T}Q_{|0,T}$; the reciprocal projection of $P$ is
$\mathrm{proj}_{\mathcal R(Q)}(P)=P_{0,T}Q_{|0,T}$ (re-attach $Q$'s bridge to $P$'s
endpoint coupling).

**Proposition 4.** $\mathrm{proj}_{\mathcal R(Q)}(P)=\arg\min_\Pi\{\mathrm{KL}(P\,|\,\Pi):\Pi\in\mathcal R(Q)\}$.

**Proposition 5.** A Markov measure in $\mathcal R(Q)$ with $P_0=\pi_0,P_T=\pi_T$
is unique and equals $P^{\mathrm{SB}}$. (This is the fixed-point characterization
the whole method targets: SB $=$ Markov $\cap$ reciprocal $\cap$ boundary.)

### IMF and its convergence

**Iterative Markovian Fitting** alternates the two projections (their eq. (8)):

$$P^{2n+1}=\mathrm{proj}_{\mathcal M}(P^{2n}),\qquad P^{2n+2}=\mathrm{proj}_{\mathcal R(Q)}(P^{2n+1}),$$

started from any $P^0\in\mathcal R(Q)$ with $P^0_0=\pi_0,P^0_T=\pi_T$. Because
each projection preserves marginals, $P^n_0=\pi_0$ and $P^n_T=\pi_T$ for all $n$
(the contrast with IPF, which does *not* preserve them, is the paper's Table 1).

**Lemma 6 (Pythagorean identities).** For $M\in\mathcal M$, $\Pi\in\mathcal R(Q)$:
$\mathrm{KL}(\Pi|M)=\mathrm{KL}(\Pi|\mathrm{proj}_{\mathcal M}(\Pi))+\mathrm{KL}(\mathrm{proj}_{\mathcal M}(\Pi)|M)$,
and symmetrically for $\mathrm{proj}_{\mathcal R(Q)}$.

**Proposition 7.** $\mathrm{KL}(P^{n+1}|P^{\mathrm{SB}})\le\mathrm{KL}(P^n|P^{\mathrm{SB}})<\infty$
and $\lim_{n\to\infty}\mathrm{KL}(P^n|P^{n+1})=0$ — i.e. the KL to the SB is
monotone non-increasing and consecutive iterates collapse together.

**Theorem 8 (IMF converges to SB).** *Under mild assumptions, the IMF sequence
$(P^n)_{n\in\mathbb N}$ admits a unique fixed point $P^\star=P^{\mathrm{SB}}$, and
$\lim_{n\to\infty}\mathrm{KL}(P^n|P^\star)=0$.*

*Argument sketch.* Each projection is an orthogonal (KL-Pythagorean) projection
onto $\mathcal M$ resp. $\mathcal R(Q)$ (Prop. 2, 4). Lemma 6 turns this into the
monotone descent of Prop. 7; the limit lies in $\mathcal M\cap\mathcal R(Q)$ with
the right boundary marginals, which by Prop. 5 is uniquely $P^{\mathrm{SB}}$.
(The same limit was shown concurrently in Peluchetti 2023, Thm. 2; DSBM gives a
simpler proof in App. C.6.)

### Algorithm

**Algorithm 1 (Diffusion Schrödinger Bridge Matching).** Practical IMF: from
$\Pi^0=\Pi^0_{0,T}Q_{|0,T}$, for each outer iteration $n$: (i) learn the
*backward* Markovian projection drift $v_\phi^\star$ by the regression (their
eq. (14)) and form $M^{2n+1}$ (eq. (13)); (ii) reciprocally project
$\Pi^{2n+1}=M^{2n+1}_{0,T}Q_{|0,T}$; (iii) learn the *forward* projection drift
$v_\theta^\star$ by (their eq. (10)) and form $M^{2n+2}$ (eq. (9)); (iv)
reciprocally project again. Alternating a forward and a backward Markovian
projection (justified by **Proposition 9**, which represents $M^\star$ both as a
forward SDE and as a time-reversal) cancels the terminal-marginal bias that a
one-sided scheme accumulates. **Proposition 10** shows that initializing with the
reference forward coupling $\Pi^0_{0,T}=Q_{0,T}$ makes DSBM reproduce the IPF /
DSB iterates (DSBM-IPF), while an independent coupling $\pi_0\otimes\pi_T$ gives
DSBM-IMF. Output: the learned drifts $v_\theta^\star,v_\phi^\star$.

---

## 2. GSBM — Generalized SB with a state / terminal cost (arXiv:2310.02233)

### Setup and objective

GSBM matches $\mu\to\nu$ with a diffusion $dX_t=u_t^\theta(X_t)dt+\sigma dW_t$,
$X_0\sim\mu,X_1\sim\nu$ (their eq. (1)), whose marginals obey the Fokker–Planck
constraint (their eq. (2)). Unlike plain SB, the **Generalized Schrödinger
Bridge** objective carries an extra running **state cost** $V_t$ (their eq. (3)):

$$\min_\theta\ \int_0^1 \mathbb{E}_{p_t}\!\left[\tfrac12\|u_t^\theta(X_t)\|^2 + V_t(X_t)\right]dt
\quad\text{subject to (1)/(2).}$$

$V_t$ acts as a task-specific penalty/reward (obstacle costs, mean-field
interaction, geometric priors, …). Plain SB is the $V_t\equiv0$ special case.

**Soft-terminal-cost reformulation (source of DRSB's $\rho\,g(X_1)$).** The paper
(Appendix A) states that the same GSB solution solves the SOC problem in which
the *hard* boundary constraint $X_1\sim\nu$ is relaxed to a *soft* **terminal
cost** $\phi(\cdot):\mathbb{R}^d\to\mathbb{R}$ (their eq. (16a)–(16b)):

$$\min_{u_t(\cdot)}\ \int_0^1\mathbb{E}_{p_t}\!\left[\tfrac12\|u_t(X_t)\|^2 + V_t(X_t)\right]dt + \mathbb{E}_{p_1}[\phi(X_1)],\qquad dX_t=u_t(X_t)dt+\sigma dW_t,\ X_0\sim\mu.$$

This is exactly the value-function shape DRSB uses, with $V(x)$ the running
control energy $\tfrac12\|u\|^2$ plus a terminal cost; DRSB weights the terminal
term by $\rho$, i.e. $\phi=\rho\,g$.

### Alternating scheme and CondSOC characterization

GSBM alternates two stages. **Proposition 1 (Stage 1).** With $p_{t\in[0,1]}$
fixed, the unique minimizer of the drift subproblem is the gradient field
$\nabla s_t^\star(X_t)$ — once $p_t$ is fixed, $V_t$ drops out and the minimal-
kinetic-energy drift matching $p_t$ is the gradient field (recovers a matching /
bridge-matching loss, as in Sec. 2 / DSBM).

**Proposition 2 (Stage 2; Conditional Stochastic Optimal Control, CondSOC).**
Factorize $p_t(X_t)=\int p_t(X_t|x_0,x_1)\,p_{0,1}^\theta(x_0,x_1)\,dx_0dx_1$.
Then the conditional path $p_{t|0,1}$ solves the endpoint-pinned SOC (their
eq. (6a)–(6b)):

$$\min_{u_{t|0,1}}\ J:=\int_0^1\mathbb{E}_{p_t(X_t|x_0,x_1)}\!\left[\tfrac12\|u_t(X_t|x_0,x_1)\|^2+V_t(X_t)\right]dt,\qquad dX_t=u_t(X_t|x_0,x_1)dt+\sigma dW_t,\ X_0=x_0,X_1=x_1.$$

CondSOC differs from (3) only in replacing the distributional boundaries
$\mu,\nu$ by endpoints $(x_0,x_1)$ drawn from the current coupling. Its optimal
control is $u_t^\star(X_t|x_0,x_1)=\sigma^2\nabla\log\Psi_t(X_t|x_1)$ where $\Psi$
solves the HJB PDE (their eq. (18))
$\partial_t\Psi_t=-\tfrac12\sigma^2\Delta\Psi_t+V_t\Psi_t$, $\Psi_1=\delta_{x_1}$.
**Lemma 3** gives the closed-form Gaussian-path solution for quadratic
$V(x)=\alpha\|\sigma x\|^2$; as $\alpha\to0$ it collapses to the Brownian bridge —
recovering exactly DSBM's bridge, so CondSOC generalizes DSBM to nontrivial
$V_t$. **Proposition 4** gives a path-integral (importance-weighted) solution for
general nonlinear $V_t$.

### Algorithm and convergence

**Algorithm 5 (Generalized Schrödinger Bridge Matching, GSBM).** Initialize
$u_t^\theta$ and $p_t$ from the independent coupling $\mu\otimes\nu$; then repeat:
(Stage 1) $u_t^\theta\leftarrow\mathrm{match}(p_t)$; (Stage 2) sample
$X_0,X_1,\{X_{t_k}\}$ from $u_t^\theta$, run `SplineOpt` (Alg. 3) to optimize the
conditional Gaussian path $p_{t|0,1}$ (mean $\mu_t$, width $\gamma_t$), optionally
resample via path integral (`ImptSample`, Alg. 4); until convergence.

**Theorem 5 (Local convergence).** *Let $\theta_n$ be the result after $n$
Stage-1/Stage-2 rounds. Then the GSB objective value is monotonically
non-increasing:* $L(\theta_n)\ge L(\theta_{n+1})$.

**Theorem 6.** *The optimal solution to the GSB problem (3) is a fixed point of
GSBM (Alg. 5).*

*Argument sketch.* The two stages are alternating minimizations of the single
objective (3): Stage 1 minimizes over drifts at fixed marginals (Prop. 1), Stage
2 minimizes over conditional marginals at fixed coupling via CondSOC (Prop. 2).
Each stage cannot increase (3), giving monotonicity (Thm. 5); a GSB optimum is
invariant under both minimizations, hence a fixed point (Thm. 6).

---

## 3. Adjoint Matching — reward fine-tuning as memoryless SOC (arXiv:2409.08861)

### Setup: reward fine-tuning as control-affine SOC

Goal: fine-tune a base generative model so its samples follow the tilted /
reward-weighted distribution $p^\ast(x)\propto p_{\mathrm{base}}(x)\exp(r(x))$
(their eq. (1)). This is cast as the **quadratic-cost, control-affine SOC**
problem (their eq. (12)–(13)):

$$\min_{u\in\mathcal U}\ \mathbb{E}\!\left[\int_0^1\left(\tfrac12\|u(X_t^u,t)\|^2+f(X_t^u,t)\right)dt+g(X_1^u)\right],\qquad dX_t^u=\big(b(X_t^u,t)+\sigma(t)u(X_t^u,t)\big)dt+\sigma(t)dB_t,\ X_0^u\sim p_0,$$

with affine control cost $\tfrac12\|u\|^2$, running state cost $f$, and terminal
state cost $g$. The **cost functional** (their eq. (14)) is
$J(u;x,t)=\mathbb{E}[\int_t^1(\tfrac12\|u\|^2+f)ds+g(X_1)\mid X_t=x]$ and the
**value function** (eq. (15)) is $V(x,t)=\min_u J(u;x,t)$. Two facts drive the
method: the value function has the Feynman–Kac form
$V(x,t)=-\log\mathbb{E}_{p_{\mathrm{base}}}[\exp(-\int_t^1 f\,ds-g(X_1))\mid X_t=x]$
(eq. (16)), and the **optimal control is the negative gradient of the value**
(their eq. (17)):

$$u^\ast(x,t)=-\sigma(t)^\top\nabla_x V(x,t)=-\sigma(t)^\top\nabla_x J(u^\ast;x,t).$$

Via Girsanov (their eq. (18)) the control cost equals
$\mathrm{KL}(p^u(X|X_0)\,\|\,p_{\mathrm{base}}(X|X_0))$, giving the
KL-regularized-RL reading (eq. (19)) in which $-f,-g$ are intermediate/terminal
rewards. (With $f=0,g=-r$ this recovers the tilted target.)

### The memoryless noise schedule (necessity)

**Definition 1 (memoryless generative process).** $X_0,X_1$ are independent,
$p_{\mathrm{base}}(X_0,X_1)=p_{\mathrm{base}}(X_0)p_{\mathrm{base}}(X_1)$.

**Proposition 1 (memoryless noise schedules).** Within the generative family, a
process is memoryless iff $\sigma(t)^2=2\eta_t+\chi(t)$ with $\chi$ satisfying the
stated vanishing condition (their eq. (25)); in particular
$\sigma(t)=\sqrt{2\eta_t}$ is called *the* memoryless noise schedule.

**Theorem 1 (fine-tuning recipe).** *To fine-tune (with arbitrary sampling noise
schedule) and still generate the tilted distribution (1), the SOC problem
(12)–(13) with $f=0$ and $g=-r$ must be solved with the memoryless noise
schedule $\sigma(t)=\sqrt{2\eta_t}$.* (Any other/constant $\sigma$ leaves a
statistical "initial value function" bias.) This memoryless requirement is what
makes the reward-only terminal cost $g=-r$ the correct SOC target.

### Adjoint state and the Adjoint Matching loss

The **continuous adjoint state** (their eq. (29)) is
$a(t;X,u)=\nabla_{X_t}\big[\int_t^1(\tfrac12\|u\|^2+f)dt'+g(X_1)\big]$, satisfying
$\mathbb{E}[a(t;X,u)\mid X_t=x]=\nabla_x J(u;x,t)$ and the backward **adjoint ODE**
(their eq. (30)–(31)):

$$\tfrac{d}{dt}a(t;X,u)=-\Big[a(t;X,u)^\top\nabla_X\big(b(X_t,t)+\sigma(t)u(X_t,t)\big)+\nabla_X f(X_t,t)+\tfrac12\nabla_X\|u(X_t,t)\|^2\Big],\qquad a(1;X,u)=\nabla g(X_1).$$

**Proposition 2 (basic Adjoint Matching objective).** With $\bar u=\mathrm{stopgrad}(u)$
(their eq. (34)):

$$L_{\mathrm{Basic\text{-}Adj\text{-}Match}}(u;X):=\tfrac12\int_0^1\big\|u(X_t,t)+\sigma(t)^\top a(t;X,\bar u)\big\|^2\,dt,\qquad X\sim p_{\bar u}.$$

Its $\theta$-gradient equals the continuous-adjoint gradient (eq. (32)), and its
*only* critical point is the optimal control $u^\ast$. Intuitively it is a
consistency loss enforcing the fixed-point relation
$u(x,t)=-\sigma(t)^\top\nabla_x J(u;x,t)$: match the control to the *negative
adjoint*.

**The "Lean" adjoint and the final objective.** At the optimum
$u^\ast(x,t)=\mathbb{E}_{p^\ast}[-\sigma(t)^\top a(t;X,u^\ast)\mid X_t=x]$
(eq. (35)); several terms of the adjoint ODE have expectation zero there
(eq. (36)) and are dropped, giving the **lean adjoint** $\tilde a$ and the final
**Adjoint Matching objective** (their eq. (37)–(39)):

$$L_{\mathrm{Adj\text{-}Match}}(u;X):=\tfrac12\int_0^1\big\|u(X_t,t)+\sigma(t)^\top\tilde a(t;X)\big\|^2\,dt,\qquad X\sim p_{\bar u},\ \bar u=\mathrm{stopgrad}(u),$$

$$\tfrac{d}{dt}\tilde a(t;X)=-\big(\tilde a(t;X)^\top\nabla_x b(X_t,t)+\nabla_x f(X_t,t)\big),\qquad \tilde a(1;X)=\nabla_x g(X_1).$$

So the regression target is $-\sigma^\top\tilde a$ where the lean adjoint is
integrated backward from the **terminal gradient $\nabla_x g(X_1)$** — for
reward fine-tuning $g=-r$, i.e. $\tilde a(1;X)=-\nabla r(X_1)$. The unique
critical point of $\mathbb{E}[L_{\mathrm{Adj\text{-}Match}}]$ is $u^\ast$
(Prop. 7, App. E.3).

**Algorithm 1 (Adjoint Matching for fine-tuning Flow Matching models).** For each
iteration: sample $m$ trajectories with the memoryless schedule
$\sigma(t)=\sqrt{2\eta_t}$ (their eqs. (40)); solve the lean adjoint ODE backward
from $\tilde a_1=-\nabla_{X_1} r(X_1)$ (eq. (41)); with $X_t,\tilde a_t$ treated as
`stopgrad`, minimize the discretized objective (their eq. (42))
$\sum_t\tfrac{2}{\sigma(t)}\big\|v_\theta^{\mathrm{finetune}}(X_t,t)-v^{\mathrm{base}}(X_t,t)+\sigma(t)\tilde a_t\big\|^2$;
gradient-step $\theta$. Output: fine-tuned velocity $v^{\mathrm{finetune}}$.

*Argument sketch.* Regress the control onto $-\sigma^\top\tilde a$ (the negative
lean adjoint). The basic version reproduces the continuous-adjoint gradient
exactly (Prop. 2); dropping the mean-zero adjoint terms yields the lean version,
which keeps the same unique optimum $u^\ast$ but lowers variance and cost (no
Jacobian $\nabla_x u$). It is a plain least-squares objective — no importance
weighting — hence scalable, unlike SOCM (eq. (33)).

---

## DRSB correspondence

| DRSB object | Source in these papers |
|---|---|
| `AdjointMatcher` loss $\mathbb{E}\,\|u^\theta(t,X_t)+\nabla g^\phi(X_1)\|^2$ | **Adjoint Matching objective**, eq. (37): $\tfrac12\int_0^1\|u(X_t,t)+\sigma(t)^\top\tilde a(t;X)\|^2dt$ with lean adjoint terminal $\tilde a(1;X)=\nabla_x g(X_1)$. When $b$ is constant/$f=0$ the lean adjoint is (approximately) constant in $t$ and equals the terminal gradient $\nabla g^\phi(X_1)$, so matching $u^\theta$ to $-\tilde a$ becomes matching $u^\theta$ to $-\nabla g^\phi(X_1)$, i.e. $\mathbb{E}\|u^\theta+\nabla g^\phi\|^2$. The DRSB docstring "loss $\mathbb{E}[\|u^\theta(t,X_t)+\nabla g^\phi(X_1)\|^2]$" is this lean-adjoint regression. |
| "Algorithm 5: Relaxed Schrödinger Bridge" (`AdjointMatcher`) | Structurally: the *relaxed* / soft-terminal-cost SOC of **GSBM eq. (16a)–(16b)** (hard $X_1\sim\nu$ relaxed to soft $\phi(X_1)$) solved by the **Adjoint Matching** regression (Alg. 1). "Relaxed" = the terminal marginal constraint is replaced by the terminal cost $\rho\,g$. Note the DRSB "Algorithm 5" label is the DRSB code's own numbering; do **not** confuse it with GSBM's Alg. 5 (GSBM) — the correspondence is conceptual, not a shared number. |
| `BridgeMatcher` (DSBM-style) | **DSBM** bridge-matching regression, eqs. (3)/(5), inside the **IMF** loop (eq. (8)) whose fixed point is the Schrödinger bridge (**Theorem 8**). Provides the base bridge / control that Adjoint Matching then reward-tunes. |
| Value-function terminal cost $\rho\,g(X_1)$ in $V(x)=\mathbb{E}[\int_0^1\tfrac12\|u_t\|^2dt+\rho\,g(X_1)\mid X_0=x]$ | The **terminal state cost $g$** of the SOC objective **Adjoint Matching eq. (12)** ($\ldots+g(X_1^u)$), equivalently the **soft terminal cost $\phi$** of **GSBM eq. (16a)** ($+\mathbb{E}_{p_1}[\phi(X_1)]$), with DRSB's robustness weight $\rho$ (i.e. $\phi=\rho\,g$). The running term $\tfrac12\|u_t\|^2$ is the shared affine control cost of all three papers. |

The abstract Lean scaffold (`Dynamics`, `Control`, `Psi`, `energy`,
`terminalMarginal`, `SBFeasible`) matches these one-to-one: `Control` is the
drift $u$; `energy` is $\int\tfrac12\|u\|^2$ (the affine control cost);
`terminalMarginal` is the law of $X_1$ against which the terminal cost / feasibility
is measured; `Psi` / the terminal-cost object is $g$ (SOC terminal cost $g$ =
GSBM soft cost $\phi$ = DRSB $g$ weighted by $\rho$).
