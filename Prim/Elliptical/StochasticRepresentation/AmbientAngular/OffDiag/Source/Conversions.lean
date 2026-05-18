import Prim.Elliptical.StochasticRepresentation.AmbientAngular.OffDiag.Source.Basic
import Prim.Elliptical.StochasticRepresentation.AmbientAngular.Upper.Basic.Source
import Prim.Elliptical.StochasticRepresentation.CenteredProduct.OffDiag.Source.Conversions

/-!
Conversions out of full off-diagonal ambient-angular sources.
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

variable (A : StochasticAmbientAngularMomentOffDiagSource d)

/-- Forget full off-diagonal cancellation to obtain the upper-triangular ambient source. -/
noncomputable def toAmbientAngularMomentSource :
    StochasticAmbientAngularMomentSource d where
  diagonal := A.diagonal
  k := A.k
  coeff_nonpos := A.coeff_nonpos
  angularDiag := A.angularDiag
  upper :=
    { formula := by
        intro U I hI j l hjl
        exact A.offDiag.formula U I hI (j := j) (l := l) (ne_of_lt hjl) }
  quantileSource := A.quantileSource
  quantile_same_radius := A.quantile_same_radius

/-- Convert the full off-diagonal ambient-angular source to the centered-product source. -/
noncomputable def toCenteredProductMomentOffDiagSource :
    StochasticCenteredProductMomentOffDiagSource d where
  diagonal := A.diagonal
  k := A.k
  coeff_nonpos := A.coeff_nonpos
  diag := A.angularDiag.toRotatedPeelCenteredMomentDiagFormula
  offDiag := A.offDiag
  quantileSource := A.quantileSource
  quantile_same_radius := A.quantile_same_radius

/-- Convert the full off-diagonal ambient-angular source to the formula-block source. -/
noncomputable def toFormulaSource : StochasticFormulaSource d :=
  A.toCenteredProductMomentOffDiagSource.toFormulaSource

/-- Convert the full off-diagonal ambient-angular source to the final public source. -/
noncomputable def toRotationOptimalitySource :
    StochasticRotationOptimalitySource d :=
  A.toCenteredProductMomentOffDiagSource.toRotationOptimalitySource

end StochasticAmbientAngularMomentOffDiagSource

end

end Prim.Elliptical
