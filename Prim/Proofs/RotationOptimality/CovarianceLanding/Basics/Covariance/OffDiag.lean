import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Covariance.Basic

/-!
Off-diagonal covariance closure helpers for rotated peeling events.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open MeasureTheory

variable {d : Nat}

/--
For a fixed rotated-peeling event, vanishing of upper-triangular
cross-covariances implies all off-diagonal cross-covariances vanish.
-/
theorem rotatedPeelPreservedCov_offDiag_eq_zero_of_lt
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (hupper :
      ∀ {j l : Prim.Idx d}, j < l →
        rotatedPeelPreservedCov diagonal U I j l = 0)
    {j l : Prim.Idx d} (hjl : j ≠ l) :
    rotatedPeelPreservedCov diagonal U I j l = 0 := by
  exact Prim.Probability.preservedCov_offDiag_eq_zero_of_lt d diagonal.core.μ
    (rotatedPeelEvent diagonal U I) diagonal.core.Y hupper hjl

/--
For a fixed rotated-peeling event, vanishing of upper-triangular centered
moments implies all off-diagonal centered moments vanish.
-/
theorem rotatedPeelCenteredProductMoment_offDiag_eq_zero_of_lt
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (hupper :
      ∀ {j l : Prim.Idx d}, j < l →
        rotatedPeelCenteredProductMoment diagonal U I j l = 0)
    {j l : Prim.Idx d} (hjl : j ≠ l) :
    rotatedPeelCenteredProductMoment diagonal U I j l = 0 := by
  rcases lt_or_gt_of_ne hjl with hlt | hgt
  · exact hupper hlt
  · rw [rotatedPeelCenteredProductMoment_comm diagonal U I j l]
    exact hupper hgt


end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
