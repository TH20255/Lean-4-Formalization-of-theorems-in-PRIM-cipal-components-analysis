import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Blocks
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Integral.Data
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Data

/-!
Compact target constructors for diagonal-covariance formula blocks.

This is the thinnest diagonal-covariance formula-block owner: it only turns
already packaged diagonal/upper/off-diagonal blocks into compact rotation
targets.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/-- Combine separated named moment formula blocks into the compact target. -/
noncomputable def cardinalRotatedPeelCenteredMomentTargetOfFormulaBlocks
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hcoeff : diagonal.b - diagonal.a <= 0)
    (D : CardinalRotatedPeelCenteredMomentDiagFormula diagonal k)
    (U : CardinalRotatedPeelCenteredMomentUpperFormula diagonal k) :
    CardinalRotatedPeelCenteredMomentTarget d where
  diagonal := diagonal
  k := k
  coeff_nonpos := hcoeff
  diag_formula := D.formula
  upper_formula := U.formula

/-- Combine diagonal and full off-diagonal named moment blocks into a target. -/
noncomputable def cardinalRotatedPeelCenteredMomentTargetOfDiagAndOffDiagBlocks
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hcoeff : diagonal.b - diagonal.a <= 0)
    (D : CardinalRotatedPeelCenteredMomentDiagFormula diagonal k)
    (O : CardinalRotatedPeelCenteredMomentOffDiagFormula diagonal k) :
    CardinalRotatedPeelCenteredMomentTarget d :=
  cardinalRotatedPeelCenteredMomentTargetOfFormulaBlocks
    diagonal k hcoeff D O.toUpperFormula

/-- Combine separated raw integral formula blocks into the compact target. -/
noncomputable def cardinalRotatedPeelCenteredIntegralTargetOfFormulaBlocks
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hcoeff : diagonal.b - diagonal.a <= 0)
    (D : CardinalRotatedPeelCenteredIntegralDiagFormula diagonal k)
    (U : CardinalRotatedPeelCenteredIntegralUpperFormula diagonal k) :
    CardinalRotatedPeelCenteredIntegralTarget d where
  diagonal := diagonal
  k := k
  coeff_nonpos := hcoeff
  diag_formula := D.formula
  upper_formula := U.formula

/-- Combine diagonal and full off-diagonal raw integral blocks into a target. -/
noncomputable def cardinalRotatedPeelCenteredIntegralTargetOfDiagAndOffDiagBlocks
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hcoeff : diagonal.b - diagonal.a <= 0)
    (D : CardinalRotatedPeelCenteredIntegralDiagFormula diagonal k)
    (O : CardinalRotatedPeelCenteredIntegralOffDiagFormula diagonal k) :
    CardinalRotatedPeelCenteredIntegralTarget d :=
  cardinalRotatedPeelCenteredIntegralTargetOfFormulaBlocks
    diagonal k hcoeff D O.toUpperFormula

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
