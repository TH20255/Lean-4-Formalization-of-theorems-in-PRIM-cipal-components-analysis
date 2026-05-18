import Prim.Elliptical.StochasticRepresentation.DiagonalProfile.Basic
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Ambient.Angular
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Blocks

/-!
Basic full off-diagonal accepted-assumptions v0 source package.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile
open MeasureTheory

noncomputable section

/--
Full off-diagonal v0 source package for the stochastic-representation theorem.

This is the stronger sibling of `StochasticPrincipalBoxAmbientFormulaSource`;
it should be used when the lower proof gives full off-diagonal cancellation.
-/
structure StochasticPrincipalBoxAmbientOffDiagFormulaSource (d : Nat) where
  core : EllipticalCore d
  q : Real
  hq : 0 <= q
  family : EllipticalCore.PrincipalBoxDiagonalCovarianceFamily core q hq
  k : Nat
  angularDiag :
    let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily
      core q hq family
    CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula
      D.diagonal k
  offDiag :
    let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily
      core q hq family
    CardinalRotatedPeelCenteredMomentOffDiagFormula D.diagonal k
  quantileSource : EllipticalCore.PrincipalCentralQuantileSource core
  same_radius : q = quantileSource.radius

namespace StochasticPrincipalBoxAmbientOffDiagFormulaSource

variable {d : Nat}
variable (S : StochasticPrincipalBoxAmbientOffDiagFormulaSource d)

/-- The stochastic diagonal profile attached to the full off-diagonal v0 package. -/
def diagonalProfile : StochasticDiagonalProfile d :=
  StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily
    S.core S.q S.hq S.family

end StochasticPrincipalBoxAmbientOffDiagFormulaSource

end

end Prim.Elliptical