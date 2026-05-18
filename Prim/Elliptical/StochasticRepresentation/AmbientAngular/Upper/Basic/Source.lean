import Prim.Elliptical.StochasticRepresentation.CenteredProduct.Basic.Source
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Ambient.Angular

/-! Source and conversion layer for the upper ambient-angular stochastic route. -/

namespace Prim.Elliptical

open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

/-- Ambient-angular moment source package for the public stochastic theorem. -/
structure StochasticAmbientAngularMomentSource (d : Nat) where
  diagonal : StochasticDiagonalProfile d
  k : Nat
  coeff_nonpos : diagonal.diagonal.b - diagonal.diagonal.a <= 0
  angularDiag :
    CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula
      diagonal.diagonal k
  upper : CardinalRotatedPeelCenteredMomentUpperFormula diagonal.diagonal k
  quantileSource : EllipticalCore.PrincipalCentralQuantileSource diagonal.core
  quantile_same_radius : diagonal.radius = quantileSource.radius

namespace StochasticAmbientAngularMomentSource

variable {d : Nat}

/-- Build the source from packaged ambient-angular diagonal and upper objects. -/
noncomputable def ofAmbientAngularSecondMomentDiagFormulaAndUpperFormula
    (D : StochasticDiagonalProfile d) (k : Nat)
    (hcoeff : D.diagonal.b - D.diagonal.a <= 0)
    (angularDiag :
      CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula
        D.diagonal k)
    (upper : CardinalRotatedPeelCenteredMomentUpperFormula D.diagonal k)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    StochasticAmbientAngularMomentSource d where
  diagonal := D
  k := k
  coeff_nonpos := hcoeff
  angularDiag := angularDiag
  upper := upper
  quantileSource := quantileSource
  quantile_same_radius := same_radius

/-- Build the source from a principal-box covariance family and formula objects. -/
noncomputable def ofPrincipalBoxDiagonalCovarianceFamilyAmbientAngularSecondMomentDiagFormulaAndUpperFormula
    (core : EllipticalCore d) (q : Real) (hq : 0 <= q)
    (F : EllipticalCore.PrincipalBoxDiagonalCovarianceFamily core q hq)
    (k : Nat)
    (angularDiag :
      let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
      CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula
        D.diagonal k)
    (upper :
      let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
      CardinalRotatedPeelCenteredMomentUpperFormula D.diagonal k)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource core)
    (same_radius : q = quantileSource.radius) :
    StochasticAmbientAngularMomentSource d := by
  let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
  exact
    ofAmbientAngularSecondMomentDiagFormulaAndUpperFormula D k
      (by
        simpa [D] using
          StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily_coeff_nonpos F)
      angularDiag upper quantileSource (by simpa [D] using same_radius)

variable (A : StochasticAmbientAngularMomentSource d)

/-- Convert the ambient-angular source package to the centered-product source. -/
noncomputable def toCenteredProductMomentSource :
    StochasticCenteredProductMomentSource d where
  diagonal := A.diagonal
  k := A.k
  coeff_nonpos := A.coeff_nonpos
  diag := A.angularDiag.toRotatedPeelCenteredMomentDiagFormula
  upper := A.upper
  quantileSource := A.quantileSource
  quantile_same_radius := A.quantile_same_radius

/-- Convert the ambient-angular source package to the formula-block source. -/
noncomputable def toFormulaSource : StochasticFormulaSource d :=
  A.toCenteredProductMomentSource.toFormulaSource

/-- Convert the ambient-angular source to the final public stochastic source. -/
noncomputable def toRotationOptimalitySource :
    StochasticRotationOptimalitySource d :=
  A.toCenteredProductMomentSource.toRotationOptimalitySource

end StochasticAmbientAngularMomentSource

end

end Prim.Elliptical
