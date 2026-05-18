import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Covariance.Basic

/-!
Preserved trace definitions and representation-event trace transport.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open MeasureTheory

variable {d : Nat}

/-- Preserved trace after conditioning on a rotated-coordinate peeling event. -/
noncomputable def rotatedPeelPreservedTrace
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) : ℝ :=
  Prim.Probability.preservedTrace d diagonal.core.μ
    (rotatedPeelEvent diagonal U I) diagonal.core.Y

/-- Preserved trace using the stochastic-representation-coordinate event. -/
noncomputable def rotatedRepPeelPreservedTrace
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) : ℝ :=
  Prim.Probability.preservedTrace d diagonal.core.μ
    (rotatedRepPeelEvent diagonal U I) diagonal.core.Y

/- The stochastic-representation-event trace may use the explicit principal
representation vector. -/
theorem rotatedRepPeelPreservedTrace_eq_principalRepVector
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedRepPeelPreservedTrace diagonal U I =
      Prim.Probability.preservedTrace d diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I) (principalRepVector diagonal.core) := by
  simpa [rotatedRepPeelPreservedTrace] using
    Prim.Probability.preservedTrace_congr_ae d diagonal.core.μ
      (rotatedRepPeelEvent diagonal U I)
      (principalRepVector_ae_eq diagonal.core)

/-- The rotated-peeling preserved trace can be computed using the
stochastic-representation event. -/
theorem rotatedPeelPreservedTrace_eq_rep
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedPeelPreservedTrace diagonal U I =
      rotatedRepPeelPreservedTrace diagonal U I := by
  simpa [rotatedPeelPreservedTrace, rotatedRepPeelPreservedTrace] using
    Prim.Probability.preservedTrace_congr_set d diagonal.core.μ
      (rotatedPeelEvent_ae_eq_rep diagonal U I) diagonal.core.Y

@[simp] theorem rotatedPeelPreservedTrace_eq_trace_cov
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedPeelPreservedTrace diagonal U I =
      Matrix.trace (rotatedPeelPreservedCov diagonal U I) := by
  rfl

/-- Trace of a rotated-coordinate peeling covariance is the sum of its diagonal. -/
theorem rotatedPeelPreservedTrace_eq_sum_diag
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedPeelPreservedTrace diagonal U I =
      ∑ j : Prim.Idx d, rotatedPeelPreservedCov diagonal U I j j := by
  simpa [rotatedPeelPreservedTrace, rotatedPeelPreservedCov] using
    Prim.Probability.preservedTrace_eq_sum_diag d diagonal.core.μ
      (rotatedPeelEvent diagonal U I) diagonal.core.Y

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
