# Distilled literature proof reconstructions

This directory contains standalone LaTeX reconstructions of the mathematical arguments in the cited sources. The goal is not brevity. Each note should preserve the paper's proof technique, order of reductions, hypotheses, notation-dependent distinctions, and any questionable step that matters to the argument, while modernizing notation and adding explanatory prose.

A satisfactory reconstruction should let a reader map every major definition, lemma, theorem, equation, and proof stage back to a precise source location. Cleaner substitute proofs should be identified as commentary rather than silently replacing the paper's argument.

`source_manifest.json` records the source files, intended scope, and anchor points for each note.

## Citation discipline

The primary paper must remain the visible source of the reconstructed proof route. When a note adds a later proof, a modern formulation of an omitted lemma, a correction, or a theorem imported from a newer source, that dependency must be named in the prose and included in the note's references. The note must distinguish the source paper's argument from the supplemental argument; a modern proof may clarify a gap, but it must not be silently attributed to the historical paper. `source_manifest.json` records these supplementary references for completed notes.

## Current state

The corpus is under active expansion. Several classical projective-metric, matrix-scaling, and path-measure notes are already long proof-level reconstructions. The DRO, Schrödinger-bridge, and modern generative-model notes have received a substantial first expansion but still require a source-by-source fidelity pass before they should be treated as complete.

## Building a note

From this directory:

```bash
pdflatex -interaction=nonstopmode -halt-on-error CGP2021_sinkhorn_schrodinger_bridge.tex
pdflatex -interaction=nonstopmode -halt-on-error CGP2021_sinkhorn_schrodinger_bridge.tex
```

The notes also support a first-pass syntax check with a single `pdflatex -halt-on-error` invocation.
