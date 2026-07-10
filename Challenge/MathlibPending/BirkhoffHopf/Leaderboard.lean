/-
# BirkhoffHopf -- solution / dependency audit (Leaderboard only)

No `Conformance.lean` and no comparator config: the statement names the project definitions `IsBirkhoffHopfContractionCoefficient`,
`positiveKernelBirkhoffCoefficient` and `PositiveKernelApplyHilbertLogDiameterBounded`,
so it is not cleanly Mathlib-only expressible; dependency-audit Leaderboard only.
-/
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf

#print axioms ForMathlib.Matrix.positive_kernel_birkhoff_hopf_contraction_of_apply_hilbert_log_diameter_bound
