import Prim.Proofs.RotationOptimality.DiagonalTrace.Objective.Basic

/-!
Matrix-level diagonal entries for the concrete orthogonal diagonal-trace
objective.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Diagonal entries whose sum gives the concrete diagonal-covariance trace
objective after an orthogonal rotation.

This is the matrix-level target for a future preserved-covariance computation:
prove that the actual rotated preserved covariance has these diagonal entries,
then the trace automatically agrees with `orthogonalMatrixDiagonalTraceObjective`.
-/
noncomputable def orthogonalMatrixDiagonalTraceDiagVal
    (P : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Prim.Idx d → ℝ :=
  fun j =>
    P.a * P.core.profile.eigenvalue j +
      if j ∈ I then
        (P.b - P.a) *
          (U.matrix * Matrix.diagonal P.core.profile.eigenvalue * U.matrix.transpose) j j
      else 0

/--
The concrete diagonal-covariance trace objective is the sum of its matrix-level
diagonal entries.
-/
theorem orthogonalMatrixDiagonalTraceObjective_eq_sum_diagVal
    (P : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    orthogonalMatrixDiagonalTraceObjective P U I =
      ∑ j : Prim.Idx d, orthogonalMatrixDiagonalTraceDiagVal P U I j := by
  let c := P.b - P.a
  let diag : Prim.Idx d → ℝ :=
    fun j => (U.matrix * Matrix.diagonal P.core.profile.eigenvalue * U.matrix.transpose) j j
  have htotal :
      (∑ j : Prim.Idx d, P.a * P.core.profile.eigenvalue j) =
        P.a * (∑ j : Prim.Idx d, P.core.profile.eigenvalue j) := by
    rw [Finset.mul_sum]
  have hselected :
      (∑ j : Prim.Idx d, if j ∈ I then c * diag j else 0) =
        c * (∑ i ∈ I, diag i) := by
    rw [Finset.sum_ite_mem_eq, Finset.mul_sum]
  calc
    orthogonalMatrixDiagonalTraceObjective P U I
        = P.a * (∑ j : Prim.Idx d, P.core.profile.eigenvalue j) +
            c * (∑ i ∈ I, diag i) := by
              rfl
    _ = (∑ j : Prim.Idx d, P.a * P.core.profile.eigenvalue j) +
          (∑ j : Prim.Idx d, if j ∈ I then c * diag j else 0) := by
              rw [htotal, hselected]
    _ = ∑ j : Prim.Idx d,
          (P.a * P.core.profile.eigenvalue j +
            if j ∈ I then c * diag j else 0) := by
              rw [Finset.sum_add_distrib]
    _ = ∑ j : Prim.Idx d, orthogonalMatrixDiagonalTraceDiagVal P U I j := by
              rfl

end CardinalOrderedValueKDimensionalRotationConExpProfile

end Prim.Proofs
