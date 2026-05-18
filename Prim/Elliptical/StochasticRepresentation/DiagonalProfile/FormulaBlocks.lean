import Prim.Elliptical.StochasticRepresentation.DiagonalProfile.Basic
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.FormulaBlockConstructors.DiagonalCovariance.Formulas.Basic
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.FormulaBlockConstructors.DiagonalCovariance.Profiles

/-! Formula-block assembly for stochastic diagonal profiles. -/

namespace Prim.Elliptical

open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

namespace StochasticDiagonalProfile

variable {d : Nat}

/-- Cardinality-local formula blocks attached to one shared stochastic diagonal profile. -/
structure FormulaBlocks (D : StochasticDiagonalProfile d) where
  momentK : Nat
  integralK : Nat
  coeff_nonpos : D.diagonal.b - D.diagonal.a <= 0
  momentDiag : CardinalRotatedPeelCenteredMomentDiagFormula D.diagonal momentK
  momentUpper : CardinalRotatedPeelCenteredMomentUpperFormula D.diagonal momentK
  integralDiag : CardinalRotatedPeelCenteredIntegralDiagFormula D.diagonal integralK
  integralUpper : CardinalRotatedPeelCenteredIntegralUpperFormula D.diagonal integralK

/-- Extract formula blocks from one matching fixed-cardinality covariance profile. -/
noncomputable def formulaBlocksOfDiagonalCovarianceProfile
    (D : StochasticDiagonalProfile d)
    (P : CardinalRotatedPeelDiagonalCovarianceProfile d)
    (same_diagonal : P.diagonal = D.diagonal) :
    FormulaBlocks D where
  momentK := P.k
  integralK := P.k
  coeff_nonpos := by
    simpa [same_diagonal] using P.coeff_nonpos
  momentDiag := by
    simpa [same_diagonal] using
      cardinalRotatedPeelCenteredMomentDiagFormulaOfDiagonalCovarianceProfile P
  momentUpper := by
    simpa [same_diagonal] using
      cardinalRotatedPeelCenteredMomentUpperFormulaOfDiagonalCovarianceProfile P
  integralDiag := by
    simpa [same_diagonal] using
      cardinalRotatedPeelCenteredIntegralDiagFormulaOfDiagonalCovarianceProfile P
  integralUpper := by
    simpa [same_diagonal] using
      cardinalRotatedPeelCenteredIntegralUpperFormulaOfDiagonalCovarianceProfile P

/-- Extract formula blocks from centered-product diagonal and upper blocks. -/
noncomputable def formulaBlocksOfCenteredProductMomentBlocks
    (D : StochasticDiagonalProfile d) (k : Nat)
    (hcoeff : D.diagonal.b - D.diagonal.a <= 0)
    (diag : CardinalRotatedPeelCenteredMomentDiagFormula D.diagonal k)
    (upper : CardinalRotatedPeelCenteredMomentUpperFormula D.diagonal k) :
    FormulaBlocks D :=
  D.formulaBlocksOfDiagonalCovarianceProfile
    (cardinalRotatedPeelDiagonalCovarianceProfileOfFormulaBlocks
      D.diagonal k hcoeff diag upper)
    rfl

end StochasticDiagonalProfile

end

end Prim.Elliptical
