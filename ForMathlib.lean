/-
# ForMathlib — paper-agnostic staging library

Reusable results, restated in Mathlib idiom, that the DRSB paper libraries import.
These are potential upstream Mathlib contributions (some already have complete
proofs in `reference/WellKnown.lean`; they are re-stated here with `sorry` while we
audit statements against the papers, per the first-pass "statements only" policy).

One file per proposed Mathlib destination area:
* `ForMathlib.MeasureTheory.DonskerVaradhan` — the DV inequality / Gibbs variational
  identity (root fact under the Sinkhorn-DRO dual).
* `ForMathlib.OptimalTransport.Basic` — the shared OT / DRO vocabulary (couplings,
  transport cost, Wasserstein-2 and Sinkhorn ambiguity balls, KL, DRO worst-case).
-/
import ForMathlib.MeasureTheory.DonskerVaradhan
import ForMathlib.OptimalTransport.Basic
