import Prim.Elliptical.StochasticRepresentation.AmbientAngular.Upper.Basic.Source

/-!
V0 source-assumption entrances for the stochastic-representation theorem.

These packages make the current publishable-v0 boundary explicit: stochastic
representation, a principal quantile source, a principal-box diagonal covariance
family, and observed ambient-angular formula objects.  They contain no
characteristic-function assumptions and are intended as stable theorem targets
while the lower B1/B2/B3 sources are being proved.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile
open MeasureTheory

noncomputable section

/--
Upper-triangular v0 source package for the stochastic-representation theorem.

This is the clean source-assumption boundary when the lower proof supplies an
observed ambient-angular diagonal formula and an upper off-diagonal formula on
top of a principal-box diagonal covariance family.
-/
structure StochasticPrincipalBoxAmbientFormulaSource (d : Nat) where
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
  upper :
    let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily
      core q hq family
    CardinalRotatedPeelCenteredMomentUpperFormula D.diagonal k
  quantileSource : EllipticalCore.PrincipalCentralQuantileSource core
  same_radius : q = quantileSource.radius

namespace StochasticPrincipalBoxAmbientFormulaSource

variable {d : Nat}
variable (S : StochasticPrincipalBoxAmbientFormulaSource d)

/-- The stochastic diagonal profile attached to the v0 source package. -/
def diagonalProfile : StochasticDiagonalProfile d :=
  StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily
    S.core S.q S.hq S.family

/-- Convert the v0 source package to the canonical ambient-angular source. -/
noncomputable def toAmbientAngularMomentSource :
    StochasticAmbientAngularMomentSource d :=
  StochasticAmbientAngularMomentSource.ofPrincipalBoxDiagonalCovarianceFamilyAmbientAngularSecondMomentDiagFormulaAndUpperFormula
    S.core S.q S.hq S.family S.k S.angularDiag S.upper
    S.quantileSource S.same_radius

/-- Convert the v0 source package to the final public stochastic source. -/
noncomputable def toRotationOptimalitySource :
    StochasticRotationOptimalitySource d :=
  S.toAmbientAngularMomentSource.toRotationOptimalitySource

end StochasticPrincipalBoxAmbientFormulaSource

end

end Prim.Elliptical
