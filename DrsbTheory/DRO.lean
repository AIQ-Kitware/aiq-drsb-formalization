/-
# Distributionally robust optimization boundary

Stable import surface for Wasserstein and entropic robust expectations, strong duality, optimizer
structure, data-driven reformulations, and radius/value-function geometry.

The source-paper modules remain provenance-preserving wrappers. Reusable duality and compactness
results should migrate into this package or its lower transport/information dependencies.
-/
import DrsbTheory.Transport
import DrsbTheory.EntropicTransport
import BlanchetMurthy2019.Basic
import GaoKleywegt2023.Basic
import MohajerinEsfahaniKuhn2018.Basic
import WangGaoXie2023.Basic

set_option autoImplicit false
