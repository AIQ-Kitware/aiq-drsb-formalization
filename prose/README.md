# DRSB prose — published sources and Lean correspondence

This directory records the mathematical arguments and source anchors used by the DRSB
formalization. It serves two distinct purposes:

1. explain the published theory that motivates the two evaluation-card bounds;
2. support source-faithful formalizations of related strong-duality, worst-case-structure,
   Sinkhorn-scaling, and stochastic-control results.

The evaluation cards define the claims to be justified; they are not proof sources. Internal code
labels such as “Eq. 47” are not literature anchors. Use the published sources listed here and in
[`../LITERATURE_REFERENCES.md`](../LITERATURE_REFERENCES.md).

## The two card theorems

The literal card-facing declarations are:

```lean
Drsb.wdrsb_cost_bound
Drsb.sdrsb_cost_bound
```

They establish one-sided bounds for an abstract objective `V : X -> R`:

```text
E_mu[V] <= the corresponding DRO dual bound.
```

| Card theorem | Ambiguity set | Main published backing | Lean relationship |
|---|---|---|---|
| `Drsb.wdrsb_cost_bound` | quadratic Wasserstein ball | Blanchet--Murthy; Gao--Kleywegt | specialization of the Wasserstein-DRO weak-duality machinery to `f := V`, `c(x,y) := ||x-y||^2` |
| `Drsb.sdrsb_cost_bound` | Sinkhorn/entropic ball | Wang--Gao--Xie | specialization of the Sinkhorn-DRO log-partition bound to `f := V`, quadratic cost |

These inequalities do not require the reverse inequality needed for strong-duality equality. They
also do not construct the intended stochastic-control value function. `V` is abstract at this
boundary.

## Where the interpretation of `V` comes from

[`schrodinger-bridge-soc-ot.md`](schrodinger-bridge-soc-ot.md) records the
Chen--Georgiou--Pavon chain connecting Schrödinger bridges, stochastic optimal control, entropic
optimal transport, and the value function

```text
V(x) = E[ integral_0^1 (1/2)||u_t||^2 dt + rho g(X_1) | X_0 = x ].
```

The `ChenGeorgiouPavon2021` Lean library contains substantial finite, sequence-model, and assembly
results, plus explicit interfaces for continuum steps. The two card theorem proofs do not consume
that continuum chain. Its role at the capstone boundary is mathematical provenance for the abstract
`V`.

[`sb-matching-generative.md`](sb-matching-generative.md) documents estimator/model provenance. It
is not part of the proof of the robust expectation inequalities.

## Wasserstein-DRO literature

[`wasserstein-dro-duality.md`](wasserstein-dro-duality.md) covers:

- Blanchet--Murthy's optimal-transport DRO duality;
- Gao--Kleywegt's duality and worst-case-distribution structure;
- Mohajerin Esfahani--Kuhn's data-driven Wasserstein-DRO reformulation.

The Lean repository has several layers:

- reusable weak- and converse-Lagrangian results in `ForMathlib.OT`;
- source-facing duality declarations in `BlanchetMurthy2019` and `GaoKleywegt2023`;
- data-driven source-facing declarations in `MohajerinEsfahaniKuhn2018`;
- the card specialization in `Drsb.wdrsb_cost_bound`.

Do not treat all source-facing results as dependencies of the card theorem. In particular,
`MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` and the Gao--Kleywegt worst-case-structure
corollaries are parallel literature formalizations. Their theorem statements retain explicit
ingredient/attainment hypotheses where the full published derivation of those ingredients is not
yet encoded.

`Drsb.wdrsb_strong_duality` remains a factored theorem accepting the hard reverse inequality as
`hge`. `Drsb.wdrsb_strong_duality_of_regularity` discharges it from the repository's proved
Wasserstein-DRO machinery. Neither card theorem assumes `hge`.

## Sinkhorn-DRO literature

[`sinkhorn-dro-duality.md`](sinkhorn-dro-duality.md) covers Wang--Gao--Xie's Sinkhorn-DRO
log-partition formulation and Gibbs structure. The stable Lean namespace is `WangGaoXie2023`, while
the final journal publication is recorded as Operations Research 2025.

The relevant layers are:

- Donsker--Varadhan/Gibbs results in `ForMathlib.MeasureTheory`;
- Sinkhorn weak-duality and converse-Lagrangian machinery in `ForMathlib.OT`;
- source-facing strong duality in `WangGaoXie2023`;
- `Drsb.sdrsb_cost_bound` and `Drsb.sdrsb_strong_duality`.

`Drsb.sdrsb_strong_duality` does not accept an `hge` parameter. It uses an explicit
Slater/interiority premise, with a concrete sufficient-condition wrapper based on the independent
coupling. The current Lean result covers the strict-feasibility case; the source also treats a
boundary case that remains a possible source-faithful extension.

## Donsker--Varadhan and KL

[`kl-dro-gibbs-donsker-varadhan.md`](kl-dro-gibbs-donsker-varadhan.md) explains the Gibbs
variational formula and the KL machinery underlying the Sinkhorn dual. The canonical Lean results
are in `ForMathlib/MeasureTheory/DonskerVaradhan*.lean`; old `reference/` names are not the project
API.

## Finite Sinkhorn and Birkhoff--Hopf sources

The distilled-literature directory contains sources for finite matrix scaling and projective
contraction. The repository intentionally keeps two proofs of the positive-kernel Birkhoff--Hopf
contraction:

- an AI-discovered Doeblin/weighted-average proof in `BirkhoffHopf.lean`;
- an Eveson--Nussbaum source-faithful proof in `BirkhoffHopf/PaperRoute/*`.

The direct proof is not Carroll's linear-programming reduction. Carroll remains useful comparison
literature, while the implemented direct argument should be documented on its own terms.

## Reading order

For the evaluation-card correspondence:

1. `../Drsb/Basic.lean` module header and the two `*_cost_bound` docstrings;
2. this file;
3. `wasserstein-dro-duality.md` or `sinkhorn-dro-duality.md`;
4. `../LITERATURE_REFERENCES.md` for exact source anchors and fidelity notes.

For reusable/upstream mathematics:

1. `../PROOF_PIPELINE.md`;
2. the relevant distilled LaTeX source under `distilled_literature/`;
3. the `ForMathlib` implementation and its independent/source-faithful route notes.

## Source files

PDFs are kept locally under `prose/papers/` and are git-ignored. The principal source families are:

- Chen, Georgiou, Pavon — Schrödinger bridge / SOC / entropic OT;
- Blanchet, Murthy — optimal-transport DRO duality;
- Gao, Kleywegt — Wasserstein-DRO duality and worst-case structure;
- Mohajerin Esfahani, Kuhn — data-driven Wasserstein DRO;
- Wang, Gao, Xie — Sinkhorn DRO;
- Donsker--Varadhan and modern textbook treatments of the Gibbs variational formula;
- Sinkhorn--Knopp, Franklin--Lorenz, Birkhoff, Carroll, and Eveson--Nussbaum for finite scaling and
  projective contraction;
- Cameron--Martin, Kakutani, Girsanov, and modern sources for the long-horizon continuum program.
