import Prim.Elliptical.StochasticRepresentation.FormulaSource.Source.Basic
import Prim.Elliptical.StochasticRepresentation.DiagonalProfile.OffDiag

/-! Full off-diagonal formula-block source constructors. -/

namespace Prim.Elliptical

open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

namespace StochasticFormulaSource

variable {d : Nat}

/-- Build a formula-block source from centered-product diagonal and off-diagonal blocks. -/
noncomputable def ofCenteredProductMomentOffDiagBlocks
    (D : StochasticDiagonalProfile d) (k : Nat)
    (hcoeff : D.diagonal.b - D.diagonal.a <= 0)
    (diag : CardinalRotatedPeelCenteredMomentDiagFormula D.diagonal k)
    (offDiag : CardinalRotatedPeelCenteredMomentOffDiagFormula D.diagonal k)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    StochasticFormulaSource d where
  diagonal := D
  quantileSource := quantileSource
  quantile_same_radius := same_radius
  blocks := D.formulaBlocksOfCenteredProductMomentOffDiagBlocks
    k hcoeff diag offDiag

end StochasticFormulaSource

end

end Prim.Elliptical
