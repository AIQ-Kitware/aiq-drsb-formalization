# Distilled literature proof reconstructions

This directory contains standalone LaTeX reconstructions of the mathematical arguments in the cited sources. The goal is not brevity. Each note should preserve the paper's proof technique, order of reductions, hypotheses, notation-dependent distinctions, and any questionable step that matters to the argument, while modernizing notation and adding explanatory prose.

A satisfactory reconstruction should let a reader map every major definition, lemma, theorem, equation, and proof stage back to a precise source location. Cleaner substitute proofs should be identified as commentary rather than silently replacing the paper's argument.

`source_manifest.json` records the source files, intended scope, and anchor points for each note.

## Current state

The corpus is under active expansion. Several classical projective-metric, matrix-scaling, and path-measure notes are already long proof-level reconstructions. The DRO, Schrödinger-bridge, and modern generative-model notes have received a substantial first expansion but still require a source-by-source fidelity pass before they should be treated as complete.

## Building a note

From this directory:

```bash
pdflatex CGP2021_sinkhorn_schrodinger_bridge.tex
bibtex CGP2021_sinkhorn_schrodinger_bridge
pdflatex CGP2021_sinkhorn_schrodinger_bridge.tex
pdflatex CGP2021_sinkhorn_schrodinger_bridge.tex
```

The notes also support a first-pass syntax check with a single `pdflatex -halt-on-error` invocation.
