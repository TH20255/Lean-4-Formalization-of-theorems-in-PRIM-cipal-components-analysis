import Prim.Proofs.RotationOptimality.MomentFormulaTarget.FormulaBlockConstructors.DiagonalCovariance.Targets
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Covariance

/-!
Diagonal-covariance profile constructors from formula blocks.

This owner depends only on the compact target constructors. Formula extraction
from an existing diagonal-covariance profile lives in
`FormulaBlockConstructors.DiagonalCovariance.Formulas`.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/-- Build the stronger fixed-cardinality diagonal-covariance profile directly from separated named-moment formula blocks. -/
noncomputable def cardinalRotatedPeelDiagonalCovarianceProfileOfFormulaBlocks
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hcoeff : diagonal.b - diagonal.a <= 0)
    (D : CardinalRotatedPeelCenteredMomentDiagFormula diagonal k)
    (U : CardinalRotatedPeelCenteredMomentUpperFormula diagonal k) :
    CardinalRotatedPeelDiagonalCovarianceProfile d :=
  (cardinalRotatedPeelCenteredMomentTargetOfFormulaBlocks
    diagonal k hcoeff D U).toDiagonalCovarianceProfile

/-- Build the stronger fixed-cardinality diagonal-covariance profile directly from diagonal and full off-diagonal named-moment blocks. -/
noncomputable def cardinalRotatedPeelDiagonalCovarianceProfileOfDiagAndOffDiagBlocks
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hcoeff : diagonal.b - diagonal.a <= 0)
    (D : CardinalRotatedPeelCenteredMomentDiagFormula diagonal k)
    (O : CardinalRotatedPeelCenteredMomentOffDiagFormula diagonal k) :
    CardinalRotatedPeelDiagonalCovarianceProfile d :=
  (cardinalRotatedPeelCenteredMomentTargetOfDiagAndOffDiagBlocks
    diagonal k hcoeff D O).toDiagonalCovarianceProfile

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
