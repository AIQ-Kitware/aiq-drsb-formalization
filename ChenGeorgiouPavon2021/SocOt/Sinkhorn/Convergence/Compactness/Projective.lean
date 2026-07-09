/-
# Projective/scale lag import wrapper

This wrapper preserves the `Compactness.Projective` module name while splitting its two independent
work surfaces into:

* `Compactness.ProjectiveLag` for denominator projective-shape collapse;
* `Compactness.ScaleLag` for scalar/total-mass control and the projective-scale wrapper.
-/

import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence.Compactness.ScaleLag
