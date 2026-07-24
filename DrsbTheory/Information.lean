/-
# Information and entropy theory boundary

Stable import surface for KL divergence, conditional entropy, Donsker-Varadhan/Gibbs variational
principles, tilting, data processing, and entropy limits needed by the full DRSB theory.

The imported declarations currently live in `ForMathlib`. Future paper-neutral information-theory
work should be added below this boundary rather than to a source-paper namespace.
-/
import ForMathlib.MeasureTheory.DonskerVaradhan
import ForMathlib.MeasureTheory.DonskerVaradhanDual
import ForMathlib.MeasureTheory.KLConvex
import ForMathlib.MeasureTheory.KLDataProcessing
import ForMathlib.MeasureTheory.KLChainRule
import ForMathlib.MeasureTheory.TiltedKernel
import ForMathlib.MeasureTheory.Normalization
import ForMathlib.MeasureTheory.GaussianEntropy

set_option autoImplicit false
