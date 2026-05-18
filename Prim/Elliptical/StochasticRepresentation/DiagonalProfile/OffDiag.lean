import Prim.Elliptical.StochasticRepresentation.DiagonalProfile.FormulaBlocks

/-! Full off-diagonal formula-block assembly for stochastic diagonal profiles. -/

namespace Prim.Elliptical

open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

namespace StochasticDiagonalProfile

variable {d : Nat}

/-- Extract formula blocks from centered-product diagonal and full off-diagonal blocks. -/
noncomputable def formulaBlocksOfCenteredProductMomentOffDiagBlocks
    (D : StochasticDiagonalProfile d) (k : Nat)
    (hcoeff : D.diagonal.b - D.diagonal.a <= 0)
    (diag : CardinalRotatedPeelCenteredMomentDiagFormula D.diagonal k)
    (offDiag : CardinalRotatedPeelCenteredMomentOffDiagFormula D.diagonal k) :
    FormulaBlocks D :=
  D.formulaBlocksOfDiagonalCovarianceProfile
    (cardinalRotatedPeelDiagonalCovarianceProfileOfDiagAndOffDiagBlocks
      D.diagonal k hcoeff diag offDiag)
    rfl

end StochasticDiagonalProfile

end

end Prim.Elliptical
