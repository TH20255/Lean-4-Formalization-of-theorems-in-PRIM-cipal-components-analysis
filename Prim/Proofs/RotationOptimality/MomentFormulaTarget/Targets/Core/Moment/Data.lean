import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Covariance.Basic

/-!
Compact centered-product moment target data.
-/

open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
The compact cardinality-local target for the current covariance milestone.

Constructing this structure is enough to obtain the theorem-facing
same-cardinality rotated-peeling trace optimality statement.
-/
structure CardinalRotatedPeelCenteredMomentTarget (d : Nat) where
  diagonal : KDimensionalDiagonalProfile d
  k : Nat
  coeff_nonpos : diagonal.b - diagonal.a ≤ 0
  diag_formula :
    ∀ U I, I.card = k →
      ∀ j,
        rotatedPeelCenteredProductMoment diagonal U I j j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j
  upper_formula :
    ∀ U I, I.card = k →
      ∀ {j l : Prim.Idx d}, j < l →
        rotatedPeelCenteredProductMoment diagonal U I j l = 0

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
