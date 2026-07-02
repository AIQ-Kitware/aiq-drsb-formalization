# PAC-Bayes generalization bound for the clipped terminal-cost network

Prose reference for the Lean 4 formalization of the DRSB "TwoPager" **Theorem 4**
(a PAC-Bayes generalization bound for the clipped terminal-cost network
$g_\vartheta$ used in Schrödinger-bridge training).

## Sources

- **Published foundation.** Pierre Alquier, *"User-friendly introduction to
  PAC-Bayes bounds"*, Foundations and Trends in Machine Learning, 2024.
  arXiv:2110.11216 — <https://arxiv.org/abs/2110.11216>.
  Local copy: `prose/papers/alquier-2024_user-friendly-introduction-to-pac-bayes__arXiv-2110.11216.pdf`
  (not committed). All lemma / theorem / equation numbers below are transcribed
  from that PDF via `pdftotext`, **not** from memory.

- **The result being supported ("TwoPager").** The GaTech companion note is an
  **unpublished internal document**; there is no PDF of it in this repo. Its
  **Theorem 4** and its proof chain, **Eqs. (116)–(126)**, are reproduced here
  **as summarized by the coordinator** who assigned this transcription. Those
  parts are explicitly labeled *reconstructed* below and should not be read as
  quotations from a published source.

The coordinator's statement of TwoPager Theorem 4 (its Eq. (116)/(126)):

> Let $Q$ be a reference path measure on trajectories $(X_t)_{t\in[0,1]}$ and $P$
> any controlled path measure with terminal marginal $P_1$. Draw i.i.d.
> $S=\{X_1^{(i)}\}_{i=1}^n$ from $P_1$. If $g_\vartheta$ is clipped to $[-C,C]$,
> then for $\varepsilon>0$ and $\varsigma\in(0,1)$, with probability $\ge 1-\varsigma$:
> $$
> \mathbb{E}_{X_1\sim P_1}\!\big[g_\vartheta(X_1)\big]
> \;\le\;
> \frac1n\sum_{i=1}^n g_\vartheta\!\big(X_1^{(i)}\big)
> \;+\;\frac{\mathrm{KL}(P\Vert Q)+\log(1/\varsigma)}{\varepsilon}
> \;+\;\frac{\varepsilon C^2}{2n}.
> $$

## Role in the DRSB chain

DRSB trains a Schrödinger-bridge terminal cost by an adversarial / matching
objective whose population quantity is $\mathbb{E}_{X_1\sim P_1}[g_\vartheta(X_1)]$,
but only the empirical average over a finite sample of terminal states is
observed during training. TwoPager Theorem 4 certifies that the population
terminal cost cannot exceed the empirical one by more than a complexity term
$\mathrm{KL}(P\Vert Q)/\varepsilon$ (the path-space regularization already paid by
the bridge) plus a Hoeffding fluctuation term $\varepsilon C^2/(2n)$ controlled by
the clipping level $C$ — i.e. it is a generalization guarantee for the learned
terminal network. Mathematically this is a textbook single-posterior PAC-Bayes
bound instantiated on path space: it is the specialization of Alquier's
Catoni-style bound (his Theorem 2.1) to one fixed change of measure $P\ll Q$,
with the clipped cost playing the role of the bounded loss.

## Published foundations (Alquier)

Throughout, $\pi\in\mathcal P(\Theta)$ is a fixed **prior** on a parameter space
$\Theta$, $\rho$ ranges over **posteriors** in $\mathcal P(\Theta)$,
$\mathrm{KL}(\rho\Vert\pi)$ is the Kullback–Leibler divergence, the loss
$\ell$ is bounded, the sample is i.i.d., and (Alquier §1.1, around p. 179)
$$
R(\theta)=\mathbb{E}_{(X,Y)\sim P}[\ell(f_\theta(X),Y)]
\quad\text{(risk / population risk)},\qquad
r(\theta)=\frac1n\sum_{i=1}^n \ell(f_\theta(X_i),Y_i)
\quad\text{(empirical risk)},
$$
with $\mathbb{E}_S[r(\theta)]=R(\theta)$. The two ingredients the DRSB chain
instantiates are a bounded-variable MGF bound and a change-of-measure inequality;
they are combined by a Chernoff/Markov tail argument.

### Bounded-variable MGF control (Hoeffding)

**Lemma 1.1 (Hoeffding's inequality).** *Let $U_1,\dots,U_n$ be independent
random variables taking values in an interval $[a,b]$. Then, for any $t>0$,*
$$
\mathbb{E}\!\left[e^{\,t\sum_{i=1}^n (U_i-\mathbb E U_i)}\right]
\;\le\;
e^{\,\frac{n t^2 (b-a)^2}{8}}.
$$

Applied (Alquier's Proposition 1.1, p. 179, with loss in $[0,C]$) to
$U_i=\mathbb E[\ell_i(\theta)]-\ell_i(\theta)$ and $t\mapsto t$, this gives the
single-hypothesis MGF bound $\mathbb E_S[e^{tn(R(\theta)-r(\theta))}]\le e^{nt^2C^2/8}$.

### Donsker–Varadhan / Gibbs variational formula

**Lemma 2.2 (Donsker and Varadhan's variational formula).** *For any measurable,
bounded function $h:\Theta\to\mathbb R$ we have*
$$
\log \mathbb E_{\theta\sim\pi}\!\left[e^{h(\theta)}\right]
\;=\;
\sup_{\rho\in\mathcal P(\Theta)}\Big(\,\mathbb E_{\theta\sim\rho}[h(\theta)]-\mathrm{KL}(\rho\Vert\pi)\,\Big).
$$
*Moreover the supremum is reached at the Gibbs measure $\pi_h$ with density,
w.r.t. $\pi$,*
$$
\frac{d\pi_h}{d\pi}(\theta)=\frac{e^{h(\theta)}}{\mathbb E_{\vartheta\sim\pi}[e^{h(\vartheta)}]}
\qquad\text{(Alquier Eq. (2.1)).}
$$
(Attribution in the text: known for finite $\Theta$ since Kullback, 1959,
Ex. 8.28; the general case is Donsker and Varadhan, 1976.)

The proof rearranges $\mathrm{KL}(\rho\Vert\pi_h)=-\mathbb E_\rho[h]+\mathrm{KL}(\rho\Vert\pi)+\log\mathbb E_\pi[e^h]$
and uses **Proposition 1.2** ($\mathrm{KL}(\mu\Vert\nu)\ge 0$, equality iff
$\mu=\nu$ — the Gibbs inequality, provable by Jensen). Dropping the supremum and
keeping a single posterior $\rho$ yields the **change-of-measure inequality** that
the DRSB chain actually uses:
$$
\boxed{\;\mathbb E_{\theta\sim\rho}[h(\theta)]\;\le\;\mathrm{KL}(\rho\Vert\pi)+\log\mathbb E_{\theta\sim\pi}[e^{h(\theta)}]\;}
$$
with equality at $\rho=\pi_h\propto e^{h}\,d\pi$. This is the inequality form
listed in the coordinator's brief; it is Lemma 2.2 specialized, not a separately
numbered result in Alquier.

### The generic (Catoni-style) PAC-Bayes bound

**Theorem 2.1 (Catoni's bound, Catoni 2003).** *[The loss function is bounded and
takes values in $[0,C]$.] For any $\lambda>0$, for any $\delta\in(0,1)$,*
$$
\mathbb P_S\!\left(\forall\rho\in\mathcal P(\Theta),\;
\mathbb E_{\theta\sim\rho}[R(\theta)]
\;\le\;
\mathbb E_{\theta\sim\rho}[r(\theta)]
+\frac{\lambda C^2}{8n}
+\frac{\mathrm{KL}(\rho\Vert\pi)+\log\frac1\delta}{\lambda}\right)\;\ge\;1-\delta.
$$

This is the "for all posteriors $\rho$ simultaneously" high-probability bound; its
minimization over $\rho$ produces the **Gibbs posterior**
$\hat\rho_\lambda=\pi_{-\lambda r}$, i.e. $\hat\rho_\lambda(d\theta)=e^{-\lambda r(\theta)}\pi(d\theta)/\mathbb E_\pi[e^{-\lambda r}]$
(Alquier Definition 2.1, Eq. (2.4)), which is the exact minimizer of the RHS by
**Corollary 2.3** — again a direct application of Lemma 2.2.

**Proof argument sketch (Alquier's proof of Theorem 2.1, p. 191–193).** The five
steps are exactly the ingredient chain Hoeffding $\to$ Donsker–Varadhan $\to$
Chernoff/Markov:
1. Fix $\theta$; Hoeffding (Lemma 1.1) on $U_i=\mathbb E[\ell_i(\theta)]-\ell_i(\theta)$,
   then set $t=\lambda/n$:
   $\mathbb E_S[e^{\lambda(R(\theta)-r(\theta))}]\le e^{\lambda^2C^2/(8n)}$.
2. Integrate this over the prior $\pi$ and swap the two integrations by **Tonelli**
   (Alquier Eq. (2.2)):
   $\mathbb E_S\,\mathbb E_{\theta\sim\pi}[e^{\lambda(R-r)}]\le e^{\lambda^2C^2/(8n)}$.
3. Apply **Donsker–Varadhan** (Lemma 2.2) to
   $\mathbb E_{\theta\sim\pi}[e^{\lambda(R-r)}]=e^{\sup_\rho(\lambda\mathbb E_\rho[R-r]-\mathrm{KL}(\rho\Vert\pi))}$,
   then rearrange to the **exponential-moment $\le 1$** inequality (Alquier Eq. (2.3)):
   $\mathbb E_S\!\left[e^{\sup_\rho \lambda\mathbb E_\rho[R-r]-\mathrm{KL}(\rho\Vert\pi)-\lambda^2C^2/(8n)}\right]\le 1$.
4. **Chernoff bound**: for $s>0$,
   $\mathbb P_S(\sup_\rho\{\lambda\mathbb E_\rho[R-r]-\mathrm{KL}(\rho\Vert\pi)-\lambda^2C^2/(8n)\}>s)\le e^{-s}\cdot(\le 1)\le e^{-s}$.
5. Solve $e^{-s}=\delta$, i.e. $s=\log(1/\delta)$, and rearrange the complement to
   the stated event.

**Beyond bounded losses.** Alquier §5.1 ("'Almost' Bounded Losses (Sub-Gaussian
and Sub-gamma)", p. 254 ff.) relaxes the boundedness hypothesis: the same
Hoeffding $\to$ DV $\to$ Markov skeleton goes through whenever the per-sample
deviation is **sub-Gaussian**, with the MGF term $\lambda C^2/(8n)$ replaced by the
sub-Gaussian variance proxy. (No specific theorem number is quoted here — the
bounded case, Theorem 2.1, is the exact template for TwoPager.)

### Exact correspondence to the TwoPager constants

| TwoPager (Theorem 4) | Alquier (Theorem 2.1) | note |
|---|---|---|
| terminal cost $g_\vartheta$ clipped to $[-C,C]$ | loss $\ell$ in $[0,C]$ | ranges: TwoPager $2C$, Alquier $C$ |
| controlled path measure $P$ | posterior $\rho$ | single fixed $P$, not $\forall\rho$ |
| reference path measure $Q$ | prior $\pi$ | |
| $\mathrm{KL}(P\Vert Q)$ | $\mathrm{KL}(\rho\Vert\pi)$ | PAC-Bayes complexity term |
| $\varepsilon$ | $\lambda$ | inverse-temperature |
| $\varsigma$ | $\delta$ | tail level |
| $\varepsilon C^2/(2n)$ | $\lambda C^2/(8n)$ | see range check below |
| $(\mathrm{KL}+\log(1/\varsigma))/\varepsilon$ | $(\mathrm{KL}+\log(1/\delta))/\lambda$ | identical form |

**Hoeffding constant check.** Alquier's $[0,C]$ has range length $C$, giving
$\lambda C^2/(8n)$. The clipped cost lives in $[-C,C]$, range length $b-a=2C$.
Substituting $b-a=2C$ into Lemma 1.1's $(b-a)^2/8$ term gives
$\lambda\,(2C)^2/(8n)=\lambda\,4C^2/(8n)=\lambda C^2/(2n)$, which is exactly
TwoPager's $\varepsilon C^2/(2n)$ with $\lambda=\varepsilon$. The two Hoeffding
terms agree once the interval length is matched. (This is also why the Lean
scaffold's MGF bound is stated as $\exp(t^2C^2/(2n))$ for $[-C,C]$ — the same
$4/8=1/2$ collapse.)

**Fixed-posterior specialization (honest caveat).** TwoPager fixes a single
controlled measure $P$ rather than quantifying over all $\rho$. In that
degenerate "single $\rho$" case the Donsker–Varadhan step is not load-bearing:
the change-of-measure inequality is applied to one $P$, and $\mathrm{KL}(P\Vert Q)$
enters only as nonnegative slack ($e^{-\mathrm{KL}}\le 1$); the bound is then
really a Hoeffding concentration statement for the mean of the fixed $g_\vartheta$.
DV becomes essential only in the genuine $\forall\rho$ form (Alquier's Theorem 2.1
as printed, and the Lean `pacBayes_supervised` / `pacBayes_of_expMoment`, where the
functional is integrated against a parameter-dependent posterior). This distinction
is flagged explicitly in the Lean scaffold (see `pacBayes_exp_moment_le_one_eq122`
below).

## The TwoPager Theorem 4 chain

> **Reconstructed, not transcribed.** The equation numbers and per-step content in
> this section come from the coordinator's summary of the unpublished TwoPager note
> together with the Lean scaffold. They are presented as the mapping of TwoPager's
> Eqs. (117)–(126) onto the published Alquier ingredients above, not as quotations.

Writing $R:=\mathbb E_{X_1\sim P_1}[g_\vartheta]$ (population terminal cost),
$r(S):=\frac1n\sum_i g_\vartheta(X_1^{(i)})$ (empirical), $\varepsilon,\varsigma,C,n$
as in Theorem 4, and $\mathrm{KL}:=\mathrm{KL}(P\Vert Q)$:

| TwoPager step | Content (reconstructed) | Alquier analogue |
|---|---|---|
| (117) | per-sample losses; population risk $R$, empirical risk $r(S)$ | §1.1 definitions of $R,r$ |
| (118) | Hoeffding MGF bound for the bounded ($[-C,C]$) per-sample deviation | Lemma 1.1 |
| (119) | integrate the MGF bound w.r.t. $Q$ (set up the change of measure) | integrate over prior $\pi$ |
| (120) | Fubini/Tonelli swap; choose the Hoeffding parameter $t=\varepsilon/n$ | Eq. (2.2), $t=\lambda/n$ |
| (121) | apply **Donsker–Varadhan** (their Lemma 5) to introduce $\mathrm{KL}(P\Vert Q)$ under a sup | Lemma 2.2 |
| (122) | rearranged **exponential-moment inequality** $\mathbb E_S[e^{Z}]\le 1$ | Eq. (2.3) |
| (123)–(125) | **Chernoff/Markov** tail: $\mathbb P_S(Z\ge\log(1/\varsigma))\le\varsigma$ | Chernoff step, $s=\log(1/\delta)$ |
| (126) | rearrange the complement to the final high-probability event (Eq. (116)) | complement of Eq. (2.3) tail → Theorem 2.1 |

Here the exponent that is Markov-tested is
$$
Z(S)=\varepsilon\big(R-r(S)\big)-\mathrm{KL}(P\Vert Q)-\frac{\varepsilon^2 C^2}{2n},
$$
step (122) is $\mathbb E_S[e^{Z}]\le 1$ (Hoeffding gives
$\mathbb E_S[e^{\varepsilon(R-r)}]\le e^{\varepsilon^2C^2/(2n)}$, which cancels the
last two terms up to the $e^{-\mathrm{KL}}\le 1$ slack), and steps (123)–(126)
turn $\mathbb E_S[e^Z]\le 1$ into $Z(S)\le\log(1/\varsigma)$ with probability
$\ge 1-\varsigma$, i.e. after dividing by $\varepsilon$,
$$
R\le r(S)+\frac{\mathrm{KL}(P\Vert Q)+\log(1/\varsigma)}{\varepsilon}+\frac{\varepsilon C^2}{2n}.
$$

## Lean scaffold correspondence

Files: `WellKnown.lean` (canonical, Mathlib-shaped statements) and `V4.lean`
(DRSB-specific wrappers and the top-level theorem). The correspondence:

| Ingredient | `WellKnown.lean` | `V4.lean` |
|---|---|---|
| Hoeffding MGF (Lemma 1.1 / (118)) | `hoeffding_iid_mgf_le`, `hoeffding_param` — $\int e^{t(\bar g-\mathbb E g)}\,d\mu^n\le e^{t^2C^2/(2n)}$ for $g\in[-C,C]$ | `hoeffding_mgf_bound` (thin adapter over `hoeffding_iid_mgf_le`; adds `n≠0`, `Measurable g`) |
| Donsker–Varadhan inequality ((121)) | `integral_le_klDiv_add_log_integral_exp` — $\int f\,d\mu\le \mathrm{KL}(\mu\Vert\nu)+\log\int e^f d\nu$, via tilting + Gibbs inequality | `donsker_varadhan_inequality_no_sSup_form` (adapter; adds $\ll$ + integrability hyps) |
| DV variational (Gibbs) equality | `isGreatest_donskerVaradhan`, `log_integral_exp_eq_sSup`, `integral_tilted_sub_klDiv_tilted` — sup attained at `ν.tilted f` | `donsker_varadhan` (sSup form over `ProbabilityMeasure`) |
| Markov/Chernoff tail ((123)–(125)) | `markov_exp` — $\mu\{a\le Z\}\le \mathrm{ofReal}((\int Z)/a)$ (needs `Integrable Z`) | `markov_inequality_exp` (adapter over `markov_exp`) |
| Exp-moment $\le 1$ ((122)) | inside `pacBayes_of_expMoment` (hypothesis `hmoment`) | `pacBayes_exp_moment_le_one_eq122` — proves $\mathbb E_S[e^{Z}]\le1$ for **fixed** clipped $g$; carries the honest scope note that DV is *not* load-bearing here (KL enters as slack) |
| Tail from moment | — | `exp_tail_of_moment_le_one` — $\mathbb E[e^Z]\le1\Rightarrow \mu\{Z\ge\log(1/\delta)\}\le\delta$ (adds `Integrable (exp∘Z)`) |
| Clipping to $[-C,C]$ | boundedness helpers `abs_avg_le`, `abs_integral_le` | `clip x C = max (-C) (min x C)`, `clip_bounds`, `gClip gtilde C = fun x ↦ clip (gtilde x) C`; also `BCE` (binary cross-entropy loss) |
| Genuine $\forall\rho$ PAC-Bayes (Theorem 2.1) | `pacBayes_of_expMoment` (master bound, DV load-bearing), `pacBayes_supervised` (end-to-end, prior→posterior, term $\lambda C^2/(2n)$) | — |
| Top-level TwoPager Theorem 4 (Eq. (116)/(126)) | — | `pac_bayes_generalization_bound` — fixed-$g$, single-$P$ high-probability bound on `sampleMeasure P1`, matching Theorem 4 verbatim |

Notes for the formalizer:
- The Lean MGF constant is $C^2/(2n)$ (not $C^2/(8n)$) precisely because the clip
  interval $[-C,C]$ has half-length $C$, i.e. the sub-Gaussian parameter is
  $((C-(-C))/2)^2=C^2$; see `hoeffding_iid_mgf_le`'s proof note.
- `pac_bayes_generalization_bound` (V4) is the fixed-posterior specialization and is
  what literally proves Theorem 4; `pacBayes_supervised` (WellKnown) is the strictly
  stronger $\forall\rho$ Alquier-Theorem-2.1 form where Donsker–Varadhan is
  essential. Both are proved in the scaffold.
