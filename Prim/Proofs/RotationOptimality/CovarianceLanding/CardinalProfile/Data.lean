import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Trace

/-!
Data object for fixed-cardinality covariance landing profiles.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Cardinality-local final landing profile for rotated-coordinate peeling.

Unlike `RotatedPeelCovarianceProfile`, this only asks for diagonal-entry
witnesses on selected sets of the fixed cardinality `k`, exactly matching the
scope of the same-cardinality optimality theorem.
-/
structure CardinalRotatedPeelCovarianceProfile (d : Nat) where
  diagonal : KDimensionalDiagonalProfile d
  k : Nat
  coeff_nonpos : diagonal.b - diagonal.a ≤ 0
  diagonal_entries :
    ∀ U I, I.card = k →
      Prim.Probability.PreservedCovarianceDiagonalEntries d diagonal.core.μ
        (rotatedPeelEvent diagonal U I) diagonal.core.Y
  diagonal_entries_eq :
    ∀ U I (hI : I.card = k) j,
      (diagonal_entries U I hI).diagVal j =
        orthogonalMatrixDiagonalTraceDiagVal diagonal U I j

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
