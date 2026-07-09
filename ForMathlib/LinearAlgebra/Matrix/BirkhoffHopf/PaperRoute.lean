/-
# Paper-route finite Birkhoff--Hopf development

Aggregate import for the Eveson--Nussbaum / finite positive-matrix proof spine.

This hierarchy is intentionally separate from the existing weighted-average staging in
`ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf`; the goal is to let agents attack the paper route in
parallel without changing the downstream Franklin--Lorenz API until this route is ready.
-/

import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.PositiveConeHilbert
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.ConvexHullDiameter
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.PositiveMatrixDiameter
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.TwoByTwo
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute.Assemble
