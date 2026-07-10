/-
# TiltedKernel -- solution / dependency audit (Leaderboard only)

No `Conformance.lean` and no comparator config: the statements name the project definition `tiltedKernel`, so they are not cleanly
Mathlib-only expressible; dependency-audit Leaderboard only, no Conformance/comparator config.
-/
import ForMathlib.MeasureTheory.TiltedKernel

#print axioms ForMathlib.MeasureTheory.tiltedKernel_apply
#print axioms ForMathlib.MeasureTheory.isMarkovKernel_tiltedKernel
#print axioms ForMathlib.MeasureTheory.measurable_tiltedKernel_normalizer
