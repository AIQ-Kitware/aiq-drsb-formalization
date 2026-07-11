/-
# Phase-compatible compactness interfaces for finite Sinkhorn convergence

This import wrapper separates the compactness development into focused modules:

* `Compactness.Basic` contains shared predicates.
* `Compactness.Precluster` owns raw bounded subsequence extraction.
* `Compactness.Projective` owns Sinkhorn projective/scale lag seams.
* `Compactness.FiniteLag` owns finite positive-box lag conversion.
* `Compactness.QuotientDrift` owns quotient-update transfer to mixed-phase drift.
* `Compactness.Assembly` preserves the public cluster-subsequence API.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.Assembly
