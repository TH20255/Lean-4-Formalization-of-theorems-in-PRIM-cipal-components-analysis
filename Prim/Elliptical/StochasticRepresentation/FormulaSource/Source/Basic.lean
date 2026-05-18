import Prim.Elliptical.StochasticRepresentation.DiagonalProfile.Source

/-!
Formula-block source package for the public stochastic-representation theorem.

Full off-diagonal constructors live in `FormulaSource.Source.OffDiag`.
-/

namespace Prim.Elliptical

open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

/--
Formula-block-level source package for the public stochastic theorem.

This is the current clean source-assumption layer between the future analytic
principal-box work and the public theorem in `Main`: it keeps the quantile
source public, keeps the formula blocks explicit, and derives the compact
rotation-optimality source internally.
-/
structure StochasticFormulaSource (d : Nat) where
  diagonal : StochasticDiagonalProfile d
  quantileSource : EllipticalCore.PrincipalCentralQuantileSource diagonal.core
  quantile_same_radius : diagonal.radius = quantileSource.radius
  blocks : diagonal.FormulaBlocks

namespace StochasticFormulaSource

variable {d : Nat}
variable (F : StochasticFormulaSource d)

/-- Build a formula-block source from one matching diagonal-covariance profile. -/
noncomputable def ofDiagonalCovarianceProfile
    (D : StochasticDiagonalProfile d)
    (P : CardinalRotatedPeelDiagonalCovarianceProfile d)
    (same_diagonal : P.diagonal = D.diagonal)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    StochasticFormulaSource d where
  diagonal := D
  quantileSource := quantileSource
  quantile_same_radius := same_radius
  blocks := D.formulaBlocksOfDiagonalCovarianceProfile P same_diagonal

/-- Build a formula-block source from centered-product diagonal and upper blocks. -/
noncomputable def ofCenteredProductMomentBlocks
    (D : StochasticDiagonalProfile d) (k : Nat)
    (hcoeff : D.diagonal.b - D.diagonal.a <= 0)
    (diag : CardinalRotatedPeelCenteredMomentDiagFormula D.diagonal k)
    (upper : CardinalRotatedPeelCenteredMomentUpperFormula D.diagonal k)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    StochasticFormulaSource d where
  diagonal := D
  quantileSource := quantileSource
  quantile_same_radius := same_radius
  blocks := D.formulaBlocksOfCenteredProductMomentBlocks k hcoeff diag upper

/-- Convert the formula-block source package to the compact public source. -/
def toRotationOptimalitySource : StochasticRotationOptimalitySource d :=
  F.blocks.toRotationOptimalitySource F.quantileSource F.quantile_same_radius

@[simp] theorem toRotationOptimalitySource_core :
    F.toRotationOptimalitySource.core = F.diagonal.core := rfl

@[simp] theorem toRotationOptimalitySource_quantileSource :
    F.toRotationOptimalitySource.quantileSource = F.quantileSource := rfl

@[simp] theorem toRotationOptimalitySource_momentTarget_k :
    F.toRotationOptimalitySource.momentTarget.k = F.blocks.momentK := rfl

@[simp] theorem toRotationOptimalitySource_integralTarget_k :
    F.toRotationOptimalitySource.integralTarget.k = F.blocks.integralK := rfl

end StochasticFormulaSource

end

end Prim.Elliptical
