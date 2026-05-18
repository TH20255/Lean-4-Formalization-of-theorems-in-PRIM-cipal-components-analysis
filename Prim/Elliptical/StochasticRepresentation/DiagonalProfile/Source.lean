import Prim.Elliptical.StochasticRepresentation.Main.Source
import Prim.Elliptical.StochasticRepresentation.DiagonalProfile.FormulaBlocks

/-! Convert stochastic diagonal-profile formula blocks to the compact source. -/

namespace Prim.Elliptical

open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

namespace StochasticDiagonalProfile
namespace FormulaBlocks

variable {d : Nat}
variable {D : StochasticDiagonalProfile d}
variable (B : FormulaBlocks D)

/-- Build the compact centered-moment target represented by the bundled blocks. -/
def momentTarget : StochasticCenteredMomentRotationTarget d :=
  cardinalRotatedPeelCenteredMomentTargetOfFormulaBlocks
    D.diagonal B.momentK B.coeff_nonpos B.momentDiag B.momentUpper

/-- Build the compact centered-integral target represented by the bundled blocks. -/
def integralTarget : StochasticCenteredIntegralRotationTarget d :=
  cardinalRotatedPeelCenteredIntegralTargetOfFormulaBlocks
    D.diagonal B.integralK B.coeff_nonpos B.integralDiag B.integralUpper

/-- Convert bundled formula blocks to the public stochastic source package. -/
def toRotationOptimalitySource
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    StochasticRotationOptimalitySource d where
  core := D.core
  quantileSource := quantileSource
  momentTarget := B.momentTarget
  integralTarget := B.integralTarget
  moment_same_core := by
    dsimp [momentTarget]
    exact D.same_core
  integral_same_core := by
    dsimp [integralTarget]
    exact D.same_core
  moment_same_radius := by
    change D.diagonal.q = quantileSource.radius
    rw [D.same_radius, same_radius]
  integral_same_radius := by
    change D.diagonal.q = quantileSource.radius
    rw [D.same_radius, same_radius]

@[simp] theorem toRotationOptimalitySource_core
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    (B.toRotationOptimalitySource quantileSource same_radius).core = D.core := rfl

@[simp] theorem toRotationOptimalitySource_quantileSource
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    (B.toRotationOptimalitySource quantileSource same_radius).quantileSource =
      quantileSource := rfl

end FormulaBlocks
end StochasticDiagonalProfile

end

end Prim.Elliptical
