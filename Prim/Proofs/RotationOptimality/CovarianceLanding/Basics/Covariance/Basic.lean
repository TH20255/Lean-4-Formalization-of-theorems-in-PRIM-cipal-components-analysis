import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Target
import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Representation.EventEquiv

/-!
Preserved covariance and centered-product moment bridges for rotated peeling events.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open MeasureTheory

variable {d : Nat}

def identityRotatedPeelDiagonalEntries
    (diagonal : KDimensionalDiagonalProfile d) (I : Finset (Prim.Idx d)) :
    Prim.Probability.PreservedCovarianceDiagonalEntries d diagonal.core.μ
      (rotatedPeelEvent diagonal (OrthogonalMatrixRotation.identity d) I)
      diagonal.core.Y where
  diagVal := (diagonal.diagonal_witness I).diagVal
  diag_eq := by
    intro j
    rw [rotatedPeelEvent_identity]
    exact (diagonal.diagonal_witness I).diag_eq j

@[simp] theorem identityRotatedPeelDiagonalEntries_diagVal
    (diagonal : KDimensionalDiagonalProfile d)
    (I : Finset (Prim.Idx d)) (j : Prim.Idx d) :
    (identityRotatedPeelDiagonalEntries diagonal I).diagVal j =
      orthogonalMatrixDiagonalTraceDiagVal diagonal
        (OrthogonalMatrixRotation.identity d) I j := by
  change (diagonal.diagonal_witness I).diagVal j =
    orthogonalMatrixDiagonalTraceDiagVal diagonal
      (OrthogonalMatrixRotation.identity d) I j
  rw [diagonal.diagonal_formula I j]
  simp

/-- Preserved covariance after conditioning on a rotated-coordinate peeling event. -/
noncomputable def rotatedPeelPreservedCov
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) : Prim.Mat d :=
  Prim.Probability.preservedCov d diagonal.core.μ
    (rotatedPeelEvent diagonal U I) diagonal.core.Y

/-- Preserved covariance using the stochastic-representation-coordinate event. -/
noncomputable def rotatedRepPeelPreservedCov
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) : Prim.Mat d :=
  Prim.Probability.preservedCov d diagonal.core.μ
    (rotatedRepPeelEvent diagonal U I) diagonal.core.Y

/- The stochastic-representation-event covariance may use the explicit
principal representation vector. -/
theorem rotatedRepPeelPreservedCov_eq_principalRepVector
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedRepPeelPreservedCov diagonal U I =
      Prim.Probability.preservedCov d diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I) (principalRepVector diagonal.core) := by
  simpa [rotatedRepPeelPreservedCov] using
    Prim.Probability.preservedCov_congr_ae d diagonal.core.μ
      (rotatedRepPeelEvent diagonal U I)
      (principalRepVector_ae_eq diagonal.core)

/-- The rotated-peeling preserved covariance can be computed using the
stochastic-representation event. -/
theorem rotatedPeelPreservedCov_eq_rep
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedPeelPreservedCov diagonal U I = rotatedRepPeelPreservedCov diagonal U I := by
  simpa [rotatedPeelPreservedCov, rotatedRepPeelPreservedCov] using
    Prim.Probability.preservedCov_congr_set d diagonal.core.μ
      (rotatedPeelEvent_ae_eq_rep diagonal U I) diagonal.core.Y

/-- Centered product moment under a rotated-peeling conditioned measure. -/
noncomputable def rotatedPeelCenteredProductMoment
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) : ℝ :=
  Prim.Probability.preservedCenteredProductMoment d diagonal.core.μ
    (rotatedPeelEvent diagonal U I) diagonal.core.Y j l

/-- Centered product moment using the stochastic-representation-coordinate event. -/
noncomputable def rotatedRepPeelCenteredProductMoment
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) : ℝ :=
  Prim.Probability.preservedCenteredProductMoment d diagonal.core.μ
    (rotatedRepPeelEvent diagonal U I) diagonal.core.Y j l

/- The stochastic-representation-event centered product moment may use the
explicit principal representation vector. -/
theorem rotatedRepPeelCenteredProductMoment_eq_principalRepVector
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) :
    rotatedRepPeelCenteredProductMoment diagonal U I j l =
      Prim.Probability.preservedCenteredProductMoment d diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I) (principalRepVector diagonal.core) j l := by
  simpa [rotatedRepPeelCenteredProductMoment] using
    Prim.Probability.preservedCenteredProductMoment_congr_ae d diagonal.core.μ
      (rotatedRepPeelEvent diagonal U I)
      (principalRepVector_ae_eq diagonal.core) j l

/-- Rotated-peeling centered product moments can be computed using the
stochastic-representation event. -/
theorem rotatedPeelCenteredProductMoment_eq_rep
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) :
    rotatedPeelCenteredProductMoment diagonal U I j l =
      rotatedRepPeelCenteredProductMoment diagonal U I j l := by
  simpa [rotatedPeelCenteredProductMoment, rotatedRepPeelCenteredProductMoment] using
    Prim.Probability.preservedCenteredProductMoment_congr_set d diagonal.core.μ
      (rotatedPeelEvent_ae_eq_rep diagonal U I) diagonal.core.Y j l

/-- Rotated-peeling centered product moments are symmetric. -/
theorem rotatedPeelCenteredProductMoment_comm
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) :
    rotatedPeelCenteredProductMoment diagonal U I j l =
      rotatedPeelCenteredProductMoment diagonal U I l j := by
  simpa [rotatedPeelCenteredProductMoment] using
    Prim.Probability.preservedCenteredProductMoment_comm d diagonal.core.μ
      (rotatedPeelEvent diagonal U I) diagonal.core.Y j l

/-- A rotated-peeling covariance entry is a centered product moment. -/
theorem rotatedPeelPreservedCov_eq_centeredProductMoment
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) :
    rotatedPeelPreservedCov diagonal U I j l =
      rotatedPeelCenteredProductMoment diagonal U I j l := by
  rfl

/-- Rotated-peeling preserved covariance is symmetric. -/
theorem rotatedPeelPreservedCov_comm
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) :
    rotatedPeelPreservedCov diagonal U I j l =
      rotatedPeelPreservedCov diagonal U I l j := by
  simpa [rotatedPeelPreservedCov] using
    Prim.Probability.preservedCov_comm d diagonal.core.μ
      (rotatedPeelEvent diagonal U I) diagonal.core.Y j l


end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
