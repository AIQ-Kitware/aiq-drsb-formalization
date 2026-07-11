/-
# Project-wide theorem target aggregate

This compatibility umbrella imports the target and interface modules across the continuum and
SOC/OT program. Production developments should prefer the concrete modules. Provisional carrier
choices and future theorem directions are documented in the dated roadmaps, while this aggregate
contains only explicit propositions and data interfaces.
-/

import ChenGeorgiouPavon2021.Continuum.IntervalWiener
import ChenGeorgiouPavon2021.EnergyIdentityTargets
import ChenGeorgiouPavon2021.SocOt.DynamicTargets
import ChenGeorgiouPavon2021.SocOt.StaticTargets
import ChenGeorgiouPavon2021.SocOt.EntropicOTTargets
import ChenGeorgiouPavon2021.SocOt.SinkhornTargets

set_option autoImplicit false
