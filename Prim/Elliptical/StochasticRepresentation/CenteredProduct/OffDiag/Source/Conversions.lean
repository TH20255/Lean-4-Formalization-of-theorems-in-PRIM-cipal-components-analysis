import Prim.Elliptical.StochasticRepresentation.CenteredProduct.OffDiag.Source.Basic
import Prim.Elliptical.StochasticRepresentation.CenteredProduct.Basic.Source
import Prim.Elliptical.StochasticRepresentation.FormulaSource.Source.OffDiag

/-!
Conversions out of full off-diagonal centered-product sources.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile
open MeasureTheory
open scoped BigOperators

noncomputable section

namespace StochasticCenteredProductMomentOffDiagSource

variable {d : Nat}
variable (M : StochasticCenteredProductMomentOffDiagSource d)

/-- Forget full off-diagonal cancellation to obtain the upper-triangular source. -/
noncomputable def toCenteredProductMomentSource :
    StochasticCenteredProductMomentSource d where
  diagonal := M.diagonal
  k := M.k
  coeff_nonpos := M.coeff_nonpos
  diag := M.diag
  upper :=
    { formula := by
        intro U I hI j l hjl
        exact M.offDiag.formula U I hI (j := j) (l := l) (ne_of_lt hjl) }
  quantileSource := M.quantileSource
  quantile_same_radius := M.quantile_same_radius

/-- Convert the full off-diagonal centered-product source to the formula-block source. -/
noncomputable def toFormulaSource : StochasticFormulaSource d :=
  StochasticFormulaSource.ofCenteredProductMomentOffDiagBlocks
    M.diagonal M.k M.coeff_nonpos M.diag M.offDiag
    M.quantileSource M.quantile_same_radius

/-- Convert the full off-diagonal centered-product source to the final public source. -/
noncomputable def toRotationOptimalitySource :
    StochasticRotationOptimalitySource d :=
  M.toFormulaSource.toRotationOptimalitySource

end StochasticCenteredProductMomentOffDiagSource

end

end Prim.Elliptical
