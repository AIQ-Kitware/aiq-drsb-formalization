/-
# Birkhoff--Hopf projective contraction for positive finite matrices (umbrella)

Compatibility umbrella re-exporting the finite Birkhoff--Hopf development, split into shared
vocabulary and route-specific modules:

* `BirkhoffHopf.Basic`  — shared neutral projective-kernel vocabulary and elementary lemmas
  (imports neither proof route);
* `BirkhoffHopf.Direct` — the AI-discovered Doeblin / weighted-average contraction proof
  (imports `Basic`).

Declarations retain their fully-qualified names in namespace `ForMathlib.Matrix`, so clients may
continue to import this umbrella module.  The source-faithful Eveson--Nussbaum development lives under
`BirkhoffHopf.PaperRoute`, which depends only on `Basic` and never on `Direct`.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.Basic
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.Direct
