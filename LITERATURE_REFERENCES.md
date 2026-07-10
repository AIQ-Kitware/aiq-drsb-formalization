# Literature references for the formalization

This file is the central bibliography/proof-source ledger for the DRSB formalization.
It complements `prose/README.md`: the prose files explain the arguments, while this
file records which original literature reference is supposed to justify each Lean
library, declaration family, and remaining proof obligation.

Status values:

- `primary`: source whose proof should be distilled and compared against Lean.
- `secondary`: background, survey, or alternate proof route.
- `provenance`: explains why a model/evaluation-card object appears here, but is not
  itself a theorem source for this formalization pass.
- `needs-distillation`: source/anchor is known, but the repo does not yet contain a
  formalization-ready LaTeX distillation of the proof.
- `exact-anchor-needed`: the source is plausible, but page/theorem/equation anchors
  still need to be verified from the PDF.

PDF convention: put downloaded PDFs under `prose/papers/` (git-ignored). Do not
commit source PDFs unless the project policy changes.

## 1. Primary theorem-bearing sources

| Key | Reference | Lean scope | Repo prose / notes | Exact anchors currently used | Coverage status | Next PDF/distillation task |
|---|---|---|---|---|---|---|
| `CGP2021` | Yongxin Chen, Tryphon T. Georgiou, Michele Pavon, *Stochastic control liaisons: Richard Sinkhorn meets Gaspard Monge on a Schrödinger bridge*, SIAM Review 2021; arXiv:2005.10963 | `ChenGeorgiouPavon2021/*`, especially SB/SOC/entropic-OT and finite Sinkhorn convergence | `prose/schrodinger-bridge-soc-ot.md` | Repo prose cites Problem 4.3 / Theorem 5.2 for SB/SOC/entropic-OT; finite Sinkhorn convergence is currently being formalized under `SocOt/Sinkhorn/Convergence/*` | `primary`, `needs-distillation` for the remaining projective-lag convergence seam | Download PDF; distill the finite/discrete Sinkhorn convergence argument, especially the no-projective-2-cycle / asymptotic-regularity step now isolated in `ProjectiveLag.lean` |
| `Leonard2013` | Christian Léonard, *A survey of the Schrödinger problem and some of its connections with optimal transport*, arXiv:1308.0215 | Dynamic/static Schrödinger bridge background; `ChenGeorgiouPavon2021.dynamic_eq_static_SB` provenance | `prose/schrodinger-bridge-soc-ot.md` | Repo prose cites Theorem 5.2 for the dynamic/static link / Gamma-to-OT connection | `secondary` / possibly `primary` for dynamic-static SB if that statement is kept | Download PDF; distill only the theorem(s) actually consumed by Lean, not the whole survey |
| `BlanchetMurthy2019` | Jose Blanchet, Karthyek R. A. Murthy, *Quantifying Distributional Model Risk via Optimal Transport*, Mathematics of Operations Research 2019; arXiv:1604.01446 | `BlanchetMurthy2019/Basic.lean`, `Drsb.wdrsb_*` | `prose/wasserstein-dro-duality.md` | Theorem 1(a),(b), collapsed via Remark 1 and equation (9) | `primary`; Lean has the WDRO strong-duality interfaces and dual-function wrapper | Download PDF; distill Theorem 1(a),(b), Remark 1, equation (9), including assumptions A1/A2 and the exact cost-ball orientation |
| `GaoKleywegt2023` | Rui Gao, Anton J. Kleywegt, *Distributionally Robust Stochastic Optimization with Wasserstein Distance*, Mathematics of Operations Research 2023; arXiv:1604.02199 | `GaoKleywegt2023/Basic.lean`, WDRSB capstone support | `prose/wasserstein-dro-duality.md` | Proposition 1; Theorem 1; Corollary 1(ii), eq. (27); Corollary 2(i), eq. (28); Corollary 2(ii), eq. (29) | `primary`; declared proved in current repo, with some attainment/selection edges isolated as hypotheses or house lemmas | Download PDF; distill Proposition 1, Theorem 1, Corollaries 1/2, equations (27)--(29), and record exactly where Lean uses a stronger/weaker/hypothesized attainment edge |
| `MohajerinEsfahaniKuhn2018` | Peyman Mohajerin Esfahani, Daniel Kuhn, *Data-driven Distributionally Robust Optimization Using the Wasserstein Metric: Performance Guarantees and Tractable Reformulations*, Mathematical Programming 2018; arXiv:1505.05116 | `MohajerinEsfahaniKuhn2018/Basic.lean` | `prose/wasserstein-dro-duality.md` | Theorem 4.2; Theorem 4.4, equation (13); Corollary 4.6 | `primary`; declared proved in current repo, with support-restriction/fidelity caveats documented | Download PDF; distill Theorem 4.2, Theorem 4.4, Corollary 4.6, and the support-restricted correction used by Lean |
| `WangGaoXie2023` | Jie Wang, Rui Gao, Yao Xie, *Sinkhorn Distributionally Robust Optimization*, Operations Research 2025; doi:10.1287/opre.2023.0294; arXiv:2109.11926 | `WangGaoXie2023/*`, `Drsb.sdrsb_*`, `ForMathlib.OT.exists_coupling_sinkhorn_lagrangian_eq` | `prose/sinkhorn-dro-duality.md`; **`prose/distilled_literature/WangGaoXie2025_sinkhorn_dro_theorem1.tex` (full distillation, 2026-07-10)** | Definition 1; eq. (1)--(3); Assumption 1(I)--(IV); Condition 1; Theorem 1(I)--(IV) (all clauses in the **shifted** radius `ρ̄`, PDF p.7); Lemma 1 (weak duality, proof p.11--12); Lemma 2 (KL reformulation); Remark 4 (worst-case law); Lemmas EC.2/EC.3/EC.4, Lemma 3 (supplement) | `primary`, **distilled**; Theorem 1(II) is proved in Lean only under Slater (`ρ̄ > 0`) — the paper covers `ρ̄ ≥ 0` | Read supplement EC.2/EC.3/EC.4 + Lemma 3; then close the boundary case `ρ̄ = 0` (λ→∞ Jensen limit) to delete the Slater hypothesis |
| `DonskerVaradhan` | M. D. Donsker and S. R. S. Varadhan, *Asymptotic evaluation of certain Markov process expectations for large time* series, CPAM 1975--1983; plus modern textbook treatments such as Dupuis--Ellis | `ForMathlib/MeasureTheory/DonskerVaradhan.lean`, `WangGaoXie2023.logPartition_eq_gibbs_sSup` | `prose/kl-dro-gibbs-donsker-varadhan.md` | Donsker--Varadhan inequality, tilted-measure attainment, Gibbs variational formula / log-integral-exp supremum | `primary` for the DV/Gibbs root; `needs-distillation`, `exact-anchor-needed` | **Now a Mathlib candidate** (`Challenge/MathlibCandidate/DonskerVaradhan`). Cite Dupuis--Ellis, *A Weak Convergence Approach to the Theory of Large Deviations* (1997) Prop. 1.4.2 / Lemma 1.4.3 for the probability-measure Gibbs variational formula we actually proved; verify the anchors from the book, then write `DonskerVaradhan_gibbs_variational.tex` |
| `SinkhornKnopp1967` | Richard Sinkhorn, Paul Knopp, *Concerning nonnegative matrices and doubly stochastic matrices*, Pacific Journal of Mathematics 1967 | `ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean`; background for finite Sinkhorn scaling/convergence | Mentioned indirectly in CGP/Sinkhorn docs | Matrix scaling existence and convergence of alternating row/column scaling | `secondary` or `primary` depending on whether the matrix-scaling proof is compared to this source or to the repo's log-domain proof | Download PDF; decide if this is the source for the existence theorem, the convergence theorem, or only historical background |
| `FranklinLorenz1989` | Joel Franklin, Jens Lorenz, *On the scaling of multidimensional matrices*, Linear Algebra and its Applications 1989 | Possible proof source for matrix scaling and Hilbert/projective convergence facts | Not yet centralized in prose | Elementary scaling proofs; geometric convergence / Hilbert-metric material, depending on exact section | `candidate-primary`, `exact-anchor-needed` for remaining `ProjectiveLag.lean` | Download PDF; inspect whether it contains the exact finite positive-kernel asymptotic-regularity lemma needed by `ProjectiveLag.lean` |
| `BirkhoffHilbert` | Garrett Birkhoff's Hilbert projective metric contraction theorem and later expositions | Possible proof source for remaining `ProjectiveLag.lean` | Mentioned in planning docs as a possible route | Positive operator contraction in Hilbert projective metric | `candidate-primary`, `exact-anchor-needed` | Pick one citable source with a clean finite positive-matrix theorem; distill the contraction-to-projective-drift argument if used |
| `CameronMartin1944` | R. H. Cameron, W. T. Martin, *Transformations of Wiener Integrals Under Translations*, Annals of Mathematics 1944 | `ForMathlib/MeasureTheory/GaussianEntropy.lean`, `GaussianCameronMartin.lean`, `ChenGeorgiouPavon2021.Continuum.*` sequence/path wrappers | `PLAN_CONTINUUM_CLOSURE.md`, `ROADMAP_ENERGY_IDENTITY.md` | Cameron--Martin deterministic shift/quasi-invariance and KL energy identity | `primary` for sequence/continuum Cameron--Martin closure; exact Lean-local theorem anchors need a dedicated ledger pass | Download PDF; distill the deterministic shift identity and compare to the sequence-model proof now in `ForMathlib` |
| `Kakutani1948` | Shizuo Kakutani, *On Equivalence of Infinite Product Measures*, Annals of Mathematics 1948 | Infinite product/quasi-invariance support in `ForMathlib.MeasureTheory.GaussianCameronMartin` | `PLAN_CONTINUUM_CLOSURE.md` | Equivalence/singularity of countable product measures; product-Hellinger criterion | `primary` or `secondary`, depending on whether the sequence proof uses Kakutani explicitly | Download PDF; identify whether Lean's current proof follows Kakutani or a direct density-martingale route |
| `Girsanov1960` | I. V. Girsanov, *On Transforming a Certain Class of Stochastic Processes by Absolutely Continuous Substitution of Measures*, 1960 | Remaining continuous `ChenGeorgiouPavon2021.energy_identity` and feedback-drift energy identity | `ROADMAP_ENERGY_IDENTITY.md`, `EXTERNAL_AUDIT.md` | Girsanov theorem and KL/energy identity for path measures | `primary`, still blocked by missing Mathlib SDE/path-measure infrastructure | Download PDF or use a modern self-contained reference; distill the exact path-measure KL identity needed, separate from stochastic integral infrastructure |

### 1b. Sources for the `ForMathlib` upstream candidates (added 2026-07-10)

These are reusable, paper-agnostic results proved in the course of the DRSB work and now staged as
comparator challenges (`Challenge/README.md`). Each needs a citable baseline to diff the Lean against.

| Key | Reference | Lean scope | Distilled prose | Coverage status | Next task |
|---|---|---|---|---|---|
| `DupuisEllis1997` | Paul Dupuis, Richard S. Ellis, *A Weak Convergence Approach to the Theory of Large Deviations*, Wiley 1997 | `ForMathlib/MeasureTheory/DonskerVaradhan.lean` (`isGreatest_donskerVaradhan`, `log_integral_exp_eq_sSup`) | none yet | `primary`, `needs-distillation`, `exact-anchor-needed` | Distill the Gibbs variational formula for probability measures, with the tilted-measure attainment, and the change-of-measure inequality |
| `CoverThomas2006` | Thomas M. Cover, Joy A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley 2006 | `ForMathlib/MeasureTheory/KLConvex.lean` (`klDiv_mix_le`) | none yet | `secondary` (finite alphabet); `exact-anchor-needed` | Thm 2.7.2 gives joint convexity of relative entropy on finite alphabets. Our statement is convexity in the **first argument only**, on a general measurable space, `ℝ≥0∞`-valued. Find the general-space anchor (Csiszár; or the `x log x` route we actually used) |
| `Rockafellar1970` | R. T. Rockafellar, *Convex Analysis*, Princeton 1970 | `ForMathlib/Analysis/Supergradient.lean` | none yet | `primary`, `exact-anchor-needed` | Existence of a subgradient at a relative-interior point (Thm 23.4). Ours is the one-dimensional concave case, proved from `ConcaveOn.slope_anti_adjacent`; record the classical statement as baseline |
| `AliprantisBorder2006` | C. D. Aliprantis, K. C. Border, *Infinite Dimensional Analysis*, 3rd ed., Springer 2006 | `ForMathlib/MeasureTheory/MeasurableArgmax.lean` | none yet | `secondary`; `exact-anchor-needed` | The Kuratowski--Ryll-Nardzewski selection theorem (Thm 18.13/18.19) is the classical route. **We deliberately avoid it**: on a separable domain with a continuous integrand, a countable dense set plus `Nat.find` suffices. Record KRN as the baseline and the divergence as intentional |
| `Leonard2013` (already listed) | — | `ForMathlib/MeasureTheory/KLChainRule.lean` (`klDiv_compProd_eq_lintegral`) | none yet | `secondary`; `exact-anchor-needed` | Mathlib **has** the additive chain rule (`klDiv_compProd_eq_add`); the disintegration form `KL(μ⊗κ‖μ⊗η) = ∫ KL(κx‖ηx) dμ` is what we added. Find the standard reference (Léonard; or Dupuis--Ellis Lemma 1.4.3(f)) |

## 2. Provenance / estimator-only sources

These sources explain where the DRSB/GSB matching estimator and code objects come from.
They are not currently theorem-bearing sources for the robustness proof unless a Lean statement is
added for the estimator itself.

| Key | Reference | Repo role | Formalization status |
|---|---|---|---|
| `DSBM2023` | Shi, De Bortoli, Campbell, Doucet, *Diffusion Schrödinger Bridge Matching*, NeurIPS 2023; arXiv:2303.16852 | Explains the matching estimator; `prose/sb-matching-generative.md` cites Theorem 8 and Algorithm 1 | `provenance` |
| `GSBM2024` | Liu, Lipman, Nickel, Karrer, Theodorou, Chen, *Generalized Schrödinger Bridge Matching*, ICLR 2024; arXiv:2310.02233 | Explains generalized matching and soft-terminal SOC; cited for objective (3), equations (16a--b), Algorithm 5 | `provenance` |
| `AdjointMatching2025` | Domingo-Enrich, Drozdzal, Karrer, Chen, *Adjoint Matching: Fine-tuning ... with Memoryless SOC*, ICLR 2025; arXiv:2409.08861 | Explains the terminal/adjoint matching estimator objects | `provenance` |

## 3. Current proof-frontier reference needs

The current compactness/convergence frontier is concentrated in `ProjectiveLag.lean`.
The repo has already closed the precluster compactness, finite lag conversion, quotient drift,
scale lag, and assembly seams. The remaining proof obligation is the finite positive-kernel
projective/asymptotic-regularity step.

Immediate reference work:

1. Read `CGP2021` finite/discrete Sinkhorn convergence sections and extract the exact argument
   for successor/current projective drift.
2. Compare that argument with `SinkhornKnopp1967`, `FranklinLorenz1989`, and a finite-dimensional
   Hilbert/Birkhoff contraction source.
3. Decide the primary proof source for the remaining two Lean theorems:
   - `sinkhorn_hatted_left_projective_drift_tendsto_zero_from_gauge_iterates`
   - `sinkhorn_right_projective_drift_tendsto_zero_from_gauge_iterates`
4. Record whether the proof genuinely needs the positive-kernel hypothesis
   `hG : ∀ i j, 0 < G i j` threaded into the projective/scale wrappers.
5. Write a distilled LaTeX proof of the chosen literature argument before the next large Lean
   proof attempt.

## 4. PDF acquisition checklist

Use arXiv PDFs when available, publisher PDFs otherwise. Suggested local paths:

```text
prose/papers/CGP2021-2005.10963.pdf
prose/papers/Leonard2013-1308.0215.pdf
prose/papers/BlanchetMurthy2019-1604.01446.pdf
prose/papers/GaoKleywegt2023-1604.02199.pdf
prose/papers/MohajerinEsfahaniKuhn2018-1505.05116.pdf
prose/papers/WangGaoXie2023-2109.11926.pdf
prose/papers/SinkhornKnopp1967.pdf
prose/papers/FranklinLorenz1989.pdf
prose/papers/CameronMartin1944.pdf
prose/papers/Kakutani1948.pdf
prose/papers/Girsanov1960.pdf
```

## 5. Non-sources / caution list

- The GaTech internal DRSB manuscript/code labels such as `drsbm_paper`, `Eq. 47`, and
  `Algorithm 5` are not authoritative literature sources for this formalization. The published
  anchor for the SDRSB bound is `WangGaoXie2023`.
- Evaluation-card YAML files define claims to be justified; they are not proof sources.
- Modern survey papers can be useful for locating proof routes, but each Lean statement should
  ultimately map to a theorem/proposition/equation in a primary literature source or to a
  standalone `ForMathlib` proof with its own classical reference.
