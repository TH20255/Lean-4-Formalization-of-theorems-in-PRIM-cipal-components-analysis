import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Representation.Basic
import Prim.Proofs.RotationOptimality.DiagonalTrace.Objective.DiagVal

/-!
Fixed-cardinality diagonal-covariance profile objects.

This small owner module keeps the profile structure needed by compact
moment-formula targets separate from the larger diagonal-witness landing route.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Stronger cardinality-local rotated-peeling landing profile built from full
diagonal covariance witnesses on the family `I.card = k`.

This is the fixed-cardinality analogue of
`RotatedPeelDiagonalCovarianceProfile`: it keeps the full diagonal witness
available, while packaging the same-cardinality diagonal covariance data into
one reusable object.
-/
structure CardinalRotatedPeelDiagonalCovarianceProfile (d : Nat) where
  diagonal : KDimensionalDiagonalProfile d
  k : Nat
  coeff_nonpos : diagonal.b - diagonal.a <= 0
  diagonal_covariance :
    forall U I, I.card = k ->
      Prim.Probability.DiagonalPreservedCovariance d diagonal.core.μ
        (rotatedPeelEvent diagonal U I) diagonal.core.Y
  diagonal_covariance_eq :
    forall U I (hI : I.card = k) j,
      (diagonal_covariance U I hI).diagVal j =
        orthogonalMatrixDiagonalTraceDiagVal diagonal U I j

/-- Package cardinality-local diagonal-covariance witnesses into the stronger fixed-cardinality profile object. -/
noncomputable def cardinalRotatedPeelDiagonalCovarianceProfileOfDiagonalCovariance
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hcoeff : diagonal.b - diagonal.a <= 0)
    (hdiagCov :
      forall U I, I.card = k ->
        Prim.Probability.DiagonalPreservedCovariance d diagonal.core.μ
          (rotatedPeelEvent diagonal U I) diagonal.core.Y)
    (hdiagVal :
      forall U I (hI : I.card = k) j,
        (hdiagCov U I hI).diagVal j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j) :
    CardinalRotatedPeelDiagonalCovarianceProfile d where
  diagonal := diagonal
  k := k
  coeff_nonpos := hcoeff
  diagonal_covariance := hdiagCov
  diagonal_covariance_eq := hdiagVal

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
