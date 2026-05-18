import Prim.Elliptical.StochasticRepresentation.AmbientAngular.OffDiag.Source.Basic

/-!
Formula-object constructors for full off-diagonal ambient-angular sources.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile
open MeasureTheory
open scoped BigOperators

noncomputable section

namespace StochasticAmbientAngularMomentOffDiagSource

variable {d : Nat}

/--
Build the full off-diagonal ambient-angular source from already packaged
observed ambient-angular diagonal and full off-diagonal formula objects.
-/
noncomputable def ofAmbientAngularSecondMomentDiagFormulaAndOffDiagFormula
    (D : StochasticDiagonalProfile d) (k : Nat)
    (hcoeff : D.diagonal.b - D.diagonal.a <= 0)
    (angularDiag :
      CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula
        D.diagonal k)
    (offDiag : CardinalRotatedPeelCenteredMomentOffDiagFormula D.diagonal k)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    StochasticAmbientAngularMomentOffDiagSource d where
  diagonal := D
  k := k
  coeff_nonpos := hcoeff
  angularDiag := angularDiag
  offDiag := offDiag
  quantileSource := quantileSource
  quantile_same_radius := same_radius

/--
Build the full off-diagonal ambient-angular source from a principal-box
diagonal covariance family, the observed ambient-angular diagonal object, and
the standard full off-diagonal formula object.
-/
noncomputable def ofPrincipalBoxDiagonalCovarianceFamilyAmbientAngularSecondMomentDiagFormulaAndOffDiagFormula
    (core : EllipticalCore d) (q : Real) (hq : 0 <= q)
    (F : EllipticalCore.PrincipalBoxDiagonalCovarianceFamily core q hq)
    (k : Nat)
    (angularDiag :
      let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
      CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula
        D.diagonal k)
    (offDiag :
      let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
      CardinalRotatedPeelCenteredMomentOffDiagFormula D.diagonal k)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource core)
    (same_radius : q = quantileSource.radius) :
    StochasticAmbientAngularMomentOffDiagSource d := by
  let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
  exact
    ofAmbientAngularSecondMomentDiagFormulaAndOffDiagFormula D k
      (by
        simpa [D] using
          StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily_coeff_nonpos F)
      angularDiag offDiag quantileSource (by simpa [D] using same_radius)

end StochasticAmbientAngularMomentOffDiagSource

end

end Prim.Elliptical