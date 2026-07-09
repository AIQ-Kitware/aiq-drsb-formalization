/-
# Phase-compatible compactness seams for finite Sinkhorn convergence

This is now an import wrapper.  The compactness frontier is split so follow-on agents can work on
independent files:

* `Compactness.Basic` contains shared predicates and no proof debt.
* `Compactness.Precluster` owns raw bounded subsequence extraction.
* `Compactness.Projective` owns Sinkhorn projective/scale lag seams.
* `Compactness.FiniteLag` owns finite positive-box lag conversion.
* `Compactness.QuotientDrift` owns quotient-update transfer to mixed-phase drift.
* `Compactness.Assembly` preserves the public cluster-subsequence API.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.Assembly
