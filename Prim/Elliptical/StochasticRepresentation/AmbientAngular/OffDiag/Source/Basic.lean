import Prim.Elliptical.StochasticRepresentation.DiagonalProfile.Basic
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Ambient.Angular
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Blocks

/-!
Basic off-diagonal ambient-angular source package.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile
open MeasureTheory
open scoped BigOperators

noncomputable section

/--
Ambient-angular moment source package with full off-diagonal cancellation.

Use this variant when the angular symmetry calculation gives a full
off-diagonal cancellation block rather than only an upper-triangular block.
-/
structure StochasticAmbientAngularMomentOffDiagSource (d : Nat) where
  diagonal : StochasticDiagonalProfile d
  k : Nat
  coeff_nonpos : diagonal.diagonal.b - diagonal.diagonal.a <= 0
  angularDiag :
    CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula
      diagonal.diagonal k
  offDiag : CardinalRotatedPeelCenteredMomentOffDiagFormula diagonal.diagonal k
  quantileSource : EllipticalCore.PrincipalCentralQuantileSource diagonal.core
  quantile_same_radius : diagonal.radius = quantileSource.radius

end

end Prim.Elliptical