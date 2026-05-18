import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Integral.Conversion
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Trace.CovTarget

/-!
Covariance-target trace endpoints for compact centered-integral targets.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

namespace CardinalRotatedPeelCenteredIntegralTarget

variable (T : CardinalRotatedPeelCenteredIntegralTarget d)

/-- The compact integral target identifies the preserved trace with the target trace. -/
theorem rotatedTrace_eq_trace_covTarget
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = T.k) :
    rotatedPeelPreservedTrace T.diagonal U I =
      Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I) :=
  T.toCenteredMomentTarget.rotatedTrace_eq_trace_covTarget U hI

/-- The explicit covariance target trace is the concrete orthogonal objective. -/
theorem covTarget_trace_eq_objective
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I) =
      orthogonalMatrixDiagonalTraceObjective T.diagonal U I :=
  T.toCenteredMomentTarget.covTarget_trace_eq_objective U I

/-- The explicit covariance target trace satisfies the same sandwich. -/
theorem covTarget_trace_sandwich
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = T.k) :
    T.diagonal.core.preservedTraceOn T.diagonal.q (leadingIndexSet d T.k) ≤
        Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I) ∧
      Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I) ≤
        T.diagonal.core.preservedTraceOn T.diagonal.q
          (trailingIndexSet d T.k) :=
  T.toCenteredMomentTarget.covTarget_trace_sandwich U hI

end CardinalRotatedPeelCenteredIntegralTarget

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
