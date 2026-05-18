import Prim.Elliptical.StochasticRepresentation.FormulaSource.Source.OffDiag

/-!
Basic full off-diagonal centered-product source package.
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
Centered-product moment source package with full off-diagonal cancellation.

This variant is convenient when the representation-side symmetry proof gives
all off-diagonal entries at once, rather than only the upper-triangular half.
-/
structure StochasticCenteredProductMomentOffDiagSource (d : Nat) where
  diagonal : StochasticDiagonalProfile d
  k : Nat
  coeff_nonpos : diagonal.diagonal.b - diagonal.diagonal.a <= 0
  diag : CardinalRotatedPeelCenteredMomentDiagFormula diagonal.diagonal k
  offDiag : CardinalRotatedPeelCenteredMomentOffDiagFormula diagonal.diagonal k
  quantileSource : EllipticalCore.PrincipalCentralQuantileSource diagonal.core
  quantile_same_radius : diagonal.radius = quantileSource.radius

end

end Prim.Elliptical