# ForMathlib/KolmogorovExtension — vendored Kolmogorov extension theorem

The **general Kolmogorov extension theorem** (`projectiveLimit`: from a projective/consistent
family of finite measures on the finite-dimensional projections of a product of Polish spaces,
construct the measure on the full product) — the piece Mathlib does **not** yet have (its
`MeasureTheory.Constructions.ProjectiveFamilyContent` builds only the finitely-additive *content*;
the σ-additivity + Carathéodory extension to a measure "is not yet in Mathlib").

We need it to build the **continuum reference path measure** of the DRSB Schrödinger bridge
(`ChenGeorgiouPavon2021`): applying `projectiveLimit` to Mathlib's own
`ProbabilityTheory.BrownianReal.projectiveFamily` (already in-pin, proven consistent) yields the
Wiener measure on `ℝ≥0 → ℝ`.

## Provenance (Apache-2.0 — reused with attribution)

Vendored from **`RemyDegenne/kolmogorov_extension4`**
(https://github.com/RemyDegenne/kolmogorov_extension4), commit
**`bb86968580787bfa8024a11b93a26d4c850352b2`**, retrieved **2026-07-04**.

* **Authors (upstream):** Rémy Degenne, Peter Pfaffelhuber. Copyright (c) 2023.
* **License:** Apache-2.0 (SPDX: Apache-2.0) — compatible with ours; upstream copyright headers
  are retained verbatim at the top of each vendored file, above our vendoring note.
* **Files vendored** (the minimal delta not already upstreamed into our Mathlib pin
  `d3716e6d`, Lean `v4.32.0-rc1`):
  * `CompactSystem.lean` — cylinder/compact-system connective lemmas
  * `RegularContent.lean` — σ-additivity of a regular additive content
  * `KolmogorovExtension.lean` — `projectiveLimit`, `isProjectiveLimit_projectiveLimit`, …
* **Not vendored** (already in our Mathlib, used directly): `Semiring.lean` (⊂ `MeasureTheory.SetSemiring`,
  and unused by the extension files) and `AuxLemmas.lean` (unused by the extension files). The upstream
  Mathlib deps `ClosedCompactCylinders`, `ProjectiveFamilyContent`, `CompactSystem`, `AddContent`,
  `OfAddContent`, `RegularityCompacts` are used from Mathlib directly.

## Attribution & contribute-back discipline (per the DRSB effort's policy)

To be a **contributing** community member rather than a leech, every deviation from upstream is
tagged and greppable, so our deltas can be offered back:

| Tag | Meaning | Contribute-back |
|---|---|---|
| *(header, no tag)* | **vendored verbatim** from upstream | credit only; no PR |
| `DRSB-CHANGE:` | a change we made to the upstream code (API drift `v4.31.0 → v4.32.0-rc1`, a fix, a golf) | **candidate PR to `kolmogorov_extension4`** |
| `DRSB-ADD:` | a declaration we *added* that isn't upstream | candidate PR upstream or to Mathlib |
| `DRSB-INDEP:` | a result we proved **independently** that also exists upstream/in Mathlib — ours is our own work; we cite the related work as a see-also (not a derivation) | cross-reference only |

Find the whole contribute-back queue with `grep -rn "DRSB-CHANGE\|DRSB-ADD" ForMathlib/`.

When the general extension lands in Mathlib (the pieces are being upstreamed incrementally — the
content premeasure + closed-compact cylinders already have), delete this sub-library and use Mathlib's.
