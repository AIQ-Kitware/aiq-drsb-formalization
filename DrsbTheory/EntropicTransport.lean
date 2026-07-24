/-
# Entropic transport, Schrodinger systems, and Sinkhorn boundary

Stable import surface for entropy-regularized transport, Gibbs kernels, finite matrix scaling,
Schrodinger potentials, projective contraction, and Sinkhorn/IPF convergence.

Imports from source-paper namespaces are transitional. Reusable theorem cores should migrate toward
paper-neutral modules while the source wrappers retain provenance.
-/
import DrsbTheory.Transport
import ForMathlib.OptimalTransport.SinkhornConverse
import ForMathlib.OptimalTransport.SinkhornValueFunction
import ForMathlib.OptimalTransport.SinkhornStrongDualityGe
import ForMathlib.LinearAlgebra.Matrix.SinkhornScaling
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.Comparison
import WangGaoXie2023.Basic
import ChenGeorgiouPavon2021.SocOt.Sinkhorn
import ChenGeorgiouPavon2021.SocOt.Sinkhorn.Convergence

set_option autoImplicit false
