/-
# Chen, Georgiou, Pavon (2021) aggregate module

This file is the public import point for downstream code.  The implementation is organized into
focused modules under `ChenGeorgiouPavon2021/`.

Because this file is an aggregate import, `lake env lean
ChenGeorgiouPavon2021/Basic.lean` requires the imported module `.olean` files to
exist first. Use `lake build ChenGeorgiouPavon2021` before the direct-file check,
or run `dev/check_cgp_module_split.sh`.
-/
import ChenGeorgiouPavon2021.SocOt
import ChenGeorgiouPavon2021.ProjectTheoremTargets

set_option autoImplicit false
