/-
# Ideal theorem targets for finite Sinkhorn uniqueness/convergence

The finite Sinkhorn target has been split into smaller modules:

* `SocOt.Sinkhorn.FiniteSystem` contains the shared finite potential/iterate/cluster predicates.
* `SocOt.Sinkhorn.Ratio` contains the finite positive-matrix maximum-principle uniqueness scaffold.
* `SocOt.Sinkhorn.Convergence` is now an import wrapper over the topic files
  `Convergence.Bounds`, `Convergence.Compactness`, `Convergence.LimitPassage`, and
  `Convergence.Gauge`.

This file remains the project-facing import target so downstream modules can continue importing
`ChenGeorgiouPavon2021.SocOt.SinkhornTargets`.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence
