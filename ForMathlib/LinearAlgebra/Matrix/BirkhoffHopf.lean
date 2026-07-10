/-
# Birkhoff--Hopf projective contraction for positive finite matrices (umbrella)

Compatibility umbrella re-exporting the finite Birkhoff--Hopf development.  It was previously a
single monolithic file; it is now split into two route-neutral / route-specific modules:

* `BirkhoffHopf.Basic`  — shared neutral projective-kernel vocabulary and elementary lemmas
  (imports neither proof route);
* `BirkhoffHopf.Direct` — the AI-discovered Doeblin / weighted-average contraction proof
  (imports `Basic`).

Every declaration keeps its original fully-qualified name in namespace `ForMathlib.Matrix`, so
existing clients importing `ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf` continue to work
unchanged.  The source-faithful Eveson--Nussbaum development lives under
`BirkhoffHopf.PaperRoute`, which depends only on `Basic` and never on `Direct`.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.Basic
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.Direct
