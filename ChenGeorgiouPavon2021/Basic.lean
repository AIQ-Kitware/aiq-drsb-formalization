/-
# Chen, Georgiou, Pavon (2021) aggregate module

This file intentionally remains as the public import point for downstream code.
The former monolithic implementation has been split into smaller proof-frontier
modules under `ChenGeorgiouPavon2021/`.

Validation note: because this file is now an aggregate import, `lake env lean
ChenGeorgiouPavon2021/Basic.lean` requires the imported module `.olean` files to
exist first. Use `lake build ChenGeorgiouPavon2021` before the direct-file check,
or run `dev/check_cgp_module_split.sh`.
-/
import ChenGeorgiouPavon2021.SocOt
