import Prim.Proofs.RotationOptimality.DiagonalTrace.Objective.DiagVal
import Prim.Proofs.RotationOptimality.DiagonalTrace.Objective.Sandwich

/-!
Explicit diagonal covariance target matrix and trace/objective helpers.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open MeasureTheory

variable {d : Nat}

@[simp] theorem orthogonalMatrixDiagonalTraceDiagVal_identity_eq_coeff
    (diagonal : KDimensionalDiagonalProfile d)
    (I : Finset (Prim.Idx d)) (j : Prim.Idx d) :
    orthogonalMatrixDiagonalTraceDiagVal diagonal
        (OrthogonalMatrixRotation.identity d) I j =
      (if j ∈ I then diagonal.b else diagonal.a) *
        diagonal.core.profile.eigenvalue j := by
  by_cases hj : j ∈ I
  · simp [orthogonalMatrixDiagonalTraceDiagVal, hj, Matrix.mul_apply,
      Matrix.diagonal]
    ring
  · simp [orthogonalMatrixDiagonalTraceDiagVal, hj]

@[simp] theorem orthogonalMatrixDiagonalTraceDiagVal_empty
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (j : Prim.Idx d) :
    orthogonalMatrixDiagonalTraceDiagVal diagonal U
        (∅ : Finset (Prim.Idx d)) j =
      diagonal.a * diagonal.core.profile.eigenvalue j := by
  simp [orthogonalMatrixDiagonalTraceDiagVal]

/--
Matrix target whose diagonal entries are exactly the concrete rotated
diagonal-trace entries.

This is a stronger landing target than the raw diagonal formula: a future
covariance calculation may prove the whole preserved covariance matrix equals
this diagonal matrix, and the raw diagonal bridge below then follows
automatically.
-/
noncomputable def orthogonalMatrixDiagonalTraceCovTarget
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Prim.Mat d :=
  Matrix.diagonal (orthogonalMatrixDiagonalTraceDiagVal diagonal U I)

@[simp] theorem orthogonalMatrixDiagonalTraceCovTarget_diag
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j : Prim.Idx d) :
    orthogonalMatrixDiagonalTraceCovTarget diagonal U I j j =
      orthogonalMatrixDiagonalTraceDiagVal diagonal U I j := by
  simp [orthogonalMatrixDiagonalTraceCovTarget]

@[simp] theorem orthogonalMatrixDiagonalTraceCovTarget_offDiag
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    {j k : Prim.Idx d} (hjk : j ≠ k) :
    orthogonalMatrixDiagonalTraceCovTarget diagonal U I j k = 0 := by
  simp [orthogonalMatrixDiagonalTraceCovTarget, Matrix.diagonal, hjk]

/-- The trace of the explicit covariance target is the sum of its prescribed diagonal entries. -/
theorem orthogonalMatrixDiagonalTraceCovTarget_trace_eq_sum_diagVal
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget diagonal U I) =
      ∑ j : Prim.Idx d, orthogonalMatrixDiagonalTraceDiagVal diagonal U I j := by
  simp [orthogonalMatrixDiagonalTraceCovTarget, Matrix.trace]

/-- The trace of the explicit covariance target is the concrete trace objective. -/
theorem orthogonalMatrixDiagonalTraceCovTarget_trace_eq_objective
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget diagonal U I) =
      orthogonalMatrixDiagonalTraceObjective diagonal U I := by
  rw [orthogonalMatrixDiagonalTraceCovTarget_trace_eq_sum_diagVal,
    ← orthogonalMatrixDiagonalTraceObjective_eq_sum_diagVal]

/-- The explicit covariance target itself satisfies the checked trace sandwich. -/
theorem orthogonalMatrixDiagonalTraceCovTarget_trace_sandwich
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hcoeff : diagonal.b - diagonal.a ≤ 0)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    diagonal.core.preservedTraceOn diagonal.q (leadingIndexSet d k) ≤
        Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget diagonal U I) ∧
      Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget diagonal U I) ≤
        diagonal.core.preservedTraceOn diagonal.q (trailingIndexSet d k) := by
  rw [orthogonalMatrixDiagonalTraceCovTarget_trace_eq_objective]
  exact orthogonalMatrixDiagonalTraceObjective_sandwich diagonal k hcoeff U hI

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
