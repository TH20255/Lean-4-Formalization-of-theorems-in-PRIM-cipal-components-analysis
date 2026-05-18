import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Covariance

/-!
Covariance-target trace endpoints for compact centered-moment targets.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

namespace CardinalRotatedPeelCenteredMomentTarget

variable (T : CardinalRotatedPeelCenteredMomentTarget d)

/-- The compact moment target identifies the preserved trace with the target trace. -/
theorem rotatedTrace_eq_trace_covTarget
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = T.k) :
    rotatedPeelPreservedTrace T.diagonal U I =
      Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I) := by
  rw [rotatedPeelPreservedTrace_eq_trace_cov]
  rw [T.cov_eq_covTarget U hI]

/-- The explicit covariance target trace is the concrete orthogonal objective. -/
theorem covTarget_trace_eq_objective
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I) =
      orthogonalMatrixDiagonalTraceObjective T.diagonal U I :=
  orthogonalMatrixDiagonalTraceCovTarget_trace_eq_objective
    T.diagonal U I

/-- The explicit covariance target trace satisfies the same sandwich. -/
theorem covTarget_trace_sandwich
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = T.k) :
    T.diagonal.core.preservedTraceOn T.diagonal.q (leadingIndexSet d T.k) ≤
        Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I) ∧
      Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I) ≤
        T.diagonal.core.preservedTraceOn T.diagonal.q
          (trailingIndexSet d T.k) := by
  exact orthogonalMatrixDiagonalTraceCovTarget_trace_sandwich
    T.diagonal T.k T.coeff_nonpos U hI

end CardinalRotatedPeelCenteredMomentTarget

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
