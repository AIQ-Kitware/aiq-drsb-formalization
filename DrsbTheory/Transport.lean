/-
# Optimal transport and Wasserstein DRO boundary

Stable import surface for couplings, extended- and real-valued transport costs, Wasserstein
ambiguity sets, measurable selectors, value-function geometry, and transport-DRO duality.

The immediate development target is the honest `ENNReal` Kantorovich/Wasserstein layer described in
`FORMALIZATION_AGENDA.md`.
-/
import DrsbTheory.Information
import ForMathlib.MeasureTheory.MeasurableArgmax
import ForMathlib.Analysis.Supergradient
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.Coupling
import ForMathlib.OptimalTransport.Convexity
import ForMathlib.OptimalTransport.DroValue
import ForMathlib.OptimalTransport.DroValueFunction
import ForMathlib.OptimalTransport.WeakDuality
import ForMathlib.OptimalTransport.ConverseLagrangian
import ForMathlib.OptimalTransport.StrongDualityGe

set_option autoImplicit false
