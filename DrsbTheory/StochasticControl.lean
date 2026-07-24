/-
# Controlled diffusion and stochastic-control boundary

Stable import surface for controlled path laws, finite-energy controls, Girsanov/control-energy
identities, dynamic programming targets, and value-function verification.

Current implementations retain the Chen-Georgiou-Pavon source namespace. The long-term package
contract is a concrete controlled-diffusion model on the canonical interval path carrier.
-/
import DrsbTheory.PathSpace
import ChenGeorgiouPavon2021.Core
import ChenGeorgiouPavon2021.EnergyIdentity
import ChenGeorgiouPavon2021.EnergyIdentityTargets
import ChenGeorgiouPavon2021.SocOt.Dynamic
import ChenGeorgiouPavon2021.SocOt.DynamicTargets

set_option autoImplicit false
