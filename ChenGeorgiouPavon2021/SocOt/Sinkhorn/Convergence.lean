/-
# Finite Sinkhorn convergence import wrapper

The finite convergence proof frontier is split into topic files so agents can work independently:

* `Convergence.Bounds` proves gauge-normalized uniform bounds.
* `Convergence.Compactness` proves phase-compatible finite-dimensional compactness.
* `Convergence.LimitPassage` passes iterate equations to cluster-point equations.
* `Convergence.Gauge` performs gauge inheritance, uniqueness, and full convergence assembly.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Gauge
