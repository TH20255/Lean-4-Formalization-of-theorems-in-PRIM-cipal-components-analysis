import Prim.Elliptical.StochasticRepresentation.V0.OffDiag.Source.Basic
import Prim.Elliptical.StochasticRepresentation.V0.Upper.Basic
import Prim.Elliptical.StochasticRepresentation.AmbientAngular.OffDiag.Source.FormulaConstructors
import Prim.Elliptical.StochasticRepresentation.AmbientAngular.OffDiag.Source.Conversions

/-!
Conversions out of the full off-diagonal accepted-assumptions v0 source.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile
open MeasureTheory

noncomputable section

namespace StochasticPrincipalBoxAmbientOffDiagFormulaSource

variable {d : Nat}
variable (S : StochasticPrincipalBoxAmbientOffDiagFormulaSource d)

/-- Convert the full off-diagonal v0 package to the upper-triangular sibling. -/
noncomputable def toUpperFormulaSource :
    StochasticPrincipalBoxAmbientFormulaSource d where
  core := S.core
  q := S.q
  hq := S.hq
  family := S.family
  k := S.k
  angularDiag := S.angularDiag
  upper := S.offDiag.toUpperFormula
  quantileSource := S.quantileSource
  same_radius := S.same_radius

/-- Convert the full off-diagonal v0 package to the ambient-angular source. -/
noncomputable def toAmbientAngularMomentOffDiagSource :
    StochasticAmbientAngularMomentOffDiagSource d :=
  StochasticAmbientAngularMomentOffDiagSource.ofPrincipalBoxDiagonalCovarianceFamilyAmbientAngularSecondMomentDiagFormulaAndOffDiagFormula
    S.core S.q S.hq S.family S.k S.angularDiag S.offDiag
    S.quantileSource S.same_radius

/-- Convert the full off-diagonal v0 package to the final public stochastic source. -/
noncomputable def toRotationOptimalitySource :
    StochasticRotationOptimalitySource d :=
  S.toAmbientAngularMomentOffDiagSource.toRotationOptimalitySource

end StochasticPrincipalBoxAmbientOffDiagFormulaSource

end

end Prim.Elliptical