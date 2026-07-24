# `DrsbTheory` package map

`DrsbTheory` is the paper-neutral architectural surface for the full theory program described in
[`FORMALIZATION_AGENDA.md`](../FORMALIZATION_AGENDA.md).

The initial modules are import boundaries, not claims of completion. They re-export current
implementations from `ForMathlib` and the source-paper libraries so downstream work can target a
stable mathematical layer while proofs are migrated incrementally.

Packages:

- `DrsbTheory.Information`
- `DrsbTheory.Transport`
- `DrsbTheory.EntropicTransport`
- `DrsbTheory.PathSpace`
- `DrsbTheory.StochasticControl`
- `DrsbTheory.SchrodingerBridge`
- `DrsbTheory.DRO`
- `DrsbTheory.RobustBridge`

Rules:

1. New reusable theorem families should enter the lowest package that states their mathematics.
2. Paper namespaces remain for source-faithful wrappers and provenance.
3. Higher packages may import lower packages; lower packages must not import higher packages.
4. An import-boundary file may be documentation plus imports. It must not contain vacuous theorem
   placeholders.
5. Package completion is tracked theorem-by-theorem in the agenda and dated status documents, never
   inferred from the existence of the module.
