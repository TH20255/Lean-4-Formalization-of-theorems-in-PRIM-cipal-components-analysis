import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Covariance.OffDiag
import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Trace

/-!
Whole-matrix covariance target helpers for rotated peeling events.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
The full covariance-target equality implies the raw diagonal formula needed by
`rotatedPeelDiagonalEntriesOfCovDiagEq`.
-/
theorem rotatedPeelPreservedCov_diag_eq_of_covTarget_eq
    (diagonal : KDimensionalDiagonalProfile d)
    (hcov :
      ∀ U I,
        rotatedPeelPreservedCov diagonal U I =
          orthogonalMatrixDiagonalTraceCovTarget diagonal U I) :
    ∀ U I j,
      rotatedPeelPreservedCov diagonal U I j j =
        orthogonalMatrixDiagonalTraceDiagVal diagonal U I j := by
  intro U I j
  rw [hcov U I]
  simp

/--
Diagonal entries plus vanishing off-diagonal entries imply the whole-matrix
covariance target.  This is the useful decomposition for future probability
work: prove the variance formula and the cross-covariances separately.
-/
theorem rotatedPeelPreservedCov_eq_covTarget_of_diag_and_offDiag
    (diagonal : KDimensionalDiagonalProfile d)
    (hdiag :
      ∀ U I j,
        rotatedPeelPreservedCov diagonal U I j j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j)
    (hoffDiag :
      ∀ U I {j k}, j ≠ k →
        rotatedPeelPreservedCov diagonal U I j k = 0) :
    ∀ U I,
      rotatedPeelPreservedCov diagonal U I =
        orthogonalMatrixDiagonalTraceCovTarget diagonal U I := by
  intro U I
  ext j k
  by_cases hjk : j = k
  · subst k
    rw [hdiag U I j]
    simp
  · rw [hoffDiag U I hjk]
    exact (orthogonalMatrixDiagonalTraceCovTarget_offDiag diagonal U I hjk).symm

/--
Cardinality-local version of
`rotatedPeelPreservedCov_eq_covTarget_of_diag_and_offDiag`.
-/
theorem rotatedPeelPreservedCov_eq_covTarget_of_cardinal_diag_and_offDiag
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hdiag :
      ∀ U I, I.card = k →
        ∀ j,
          rotatedPeelPreservedCov diagonal U I j j =
            orthogonalMatrixDiagonalTraceDiagVal diagonal U I j)
    (hoffDiag :
      ∀ U I, I.card = k →
        ∀ {j l}, j ≠ l →
          rotatedPeelPreservedCov diagonal U I j l = 0) :
    ∀ U I, I.card = k →
      rotatedPeelPreservedCov diagonal U I =
        orthogonalMatrixDiagonalTraceCovTarget diagonal U I := by
  intro U I hI
  ext j l
  by_cases hjl : j = l
  · subst l
    rw [hdiag U I hI j]
    simp
  · rw [hoffDiag U I hI hjl]
    exact (orthogonalMatrixDiagonalTraceCovTarget_offDiag diagonal U I hjl).symm

/--
Upper-triangular version of the decomposed covariance target route.  Symmetry
of preserved covariance supplies the lower-triangular off-diagonal entries.
-/
theorem rotatedPeelPreservedCov_eq_covTarget_of_diag_and_upperOffDiag
    (diagonal : KDimensionalDiagonalProfile d)
    (hdiag :
      ∀ U I j,
        rotatedPeelPreservedCov diagonal U I j j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j)
    (hupper :
      ∀ U I, ∀ {j l : Prim.Idx d}, j < l →
        rotatedPeelPreservedCov diagonal U I j l = 0) :
    ∀ U I,
      rotatedPeelPreservedCov diagonal U I =
        orthogonalMatrixDiagonalTraceCovTarget diagonal U I :=
  rotatedPeelPreservedCov_eq_covTarget_of_diag_and_offDiag diagonal hdiag
    (fun U I => rotatedPeelPreservedCov_offDiag_eq_zero_of_lt
      diagonal U I (hupper U I))

/--
Cardinality-local upper-triangular version of the decomposed covariance target
route.
-/
theorem rotatedPeelPreservedCov_eq_covTarget_of_cardinal_diag_and_upperOffDiag
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hdiag :
      ∀ U I, I.card = k →
        ∀ j,
          rotatedPeelPreservedCov diagonal U I j j =
            orthogonalMatrixDiagonalTraceDiagVal diagonal U I j)
    (hupper :
      ∀ U I, I.card = k →
        ∀ {j l : Prim.Idx d}, j < l →
          rotatedPeelPreservedCov diagonal U I j l = 0) :
    ∀ U I, I.card = k →
      rotatedPeelPreservedCov diagonal U I =
        orthogonalMatrixDiagonalTraceCovTarget diagonal U I :=
  rotatedPeelPreservedCov_eq_covTarget_of_cardinal_diag_and_offDiag diagonal k hdiag
    (fun U I hI => rotatedPeelPreservedCov_offDiag_eq_zero_of_lt
      diagonal U I (hupper U I hI))

/-- Whole-matrix target equality immediately identifies the rotated preserved trace. -/
theorem rotatedPeelPreservedTrace_eq_trace_covTarget_of_covTarget_eq
    (diagonal : KDimensionalDiagonalProfile d)
    (hcov :
      ∀ U I,
        rotatedPeelPreservedCov diagonal U I =
          orthogonalMatrixDiagonalTraceCovTarget diagonal U I)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedPeelPreservedTrace diagonal U I =
      Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget diagonal U I) := by
  rw [rotatedPeelPreservedTrace_eq_trace_cov, hcov U I]

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
