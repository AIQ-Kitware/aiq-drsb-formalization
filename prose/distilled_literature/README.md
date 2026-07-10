# Distilled literature proof reconstructions

This directory contains standalone LaTeX reconstructions of the mathematical arguments in the cited sources. The goal is not brevity. Each note should preserve the paper's proof technique, order of reductions, hypotheses, notation-dependent distinctions, and any questionable step that matters to the argument, while modernizing notation and adding explanatory prose.

A satisfactory reconstruction should let a reader map every major definition, lemma, theorem, equation, and proof stage back to a precise source location. Cleaner substitute proofs should be identified as commentary rather than silently replacing the paper's argument.

`source_manifest.json` records the source files, intended scope, and anchor points for each note.

## Citation discipline

The primary paper must remain the visible source of the reconstructed proof route. When a note adds a later proof, a modern formulation of an omitted lemma, a correction, or a theorem imported from a newer source, that dependency must be named in the prose and included in the note's references. The note must distinguish the source paper's argument from the supplemental argument; a modern proof may clarify a gap, but it must not be silently attributed to the historical paper. `source_manifest.json` records these supplementary references for completed notes.

## Current state

The corpus currently represents **21 unique source papers** in 25 paper-specific TeX files. The file count is larger because Blanchet--Murthy, Gao--Kleywegt, and Wang--Gao--Xie each have both a broad note and a theorem-focused companion; `ClassicalFoundations_DV_KLconvexity_supergradient.tex` is a multi-source synthesis and is not counted as a paper.

As of the 2026-07-10 four-paper pass, **11/21 papers** have completed source-order proof reconstructions:

- Adjoint Matching (2025);
- Birkhoff (1957);
- Blanchet--Murthy (2019);
- Chen--Georgiou--Pavon (2021);
- Cameron--Martin (1945);
- Carroll (2004);
- Diffusion Schrödinger Bridge Matching (2023);
- Eveson--Nussbaum (1995);
- Fortet (1940);
- Franklin--Lorenz (1989), Section 3;
- Generalized Schrödinger Bridge Matching (2024).

The remaining ten papers retain expanded first-pass notes but still require the same source-by-source fidelity review before being marked complete. Completion status and exact source anchors are recorded in `source_manifest.json`.

## Building a note

From this directory:

```bash
pdflatex -interaction=nonstopmode -halt-on-error CGP2021_sinkhorn_schrodinger_bridge.tex
pdflatex -interaction=nonstopmode -halt-on-error CGP2021_sinkhorn_schrodinger_bridge.tex
```

The notes also support a first-pass syntax check with a single `pdflatex -halt-on-error` invocation.
