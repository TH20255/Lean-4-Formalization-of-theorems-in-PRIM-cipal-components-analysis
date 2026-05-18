import Prim.LinearAlgebra.DoublyStochastic.Kernel
import Mathlib.LinearAlgebra.UnitaryGroup

namespace Prim.LinearAlgebra

open scoped BigOperators

namespace DoublyStochasticKernel

variable {d : Nat}

/--
The entrywise square of a matrix is a doubly-stochastic kernel once its row and
column square sums are normalized to one.

For an orthogonal matrix these hypotheses come from `U * Uᵀ = 1` and
`Uᵀ * U = 1`; see `fromOrthogonalEquations` and `fromOrthogonalGroup`.
-/
noncomputable def fromSquareMatrix
    (U : Prim.Mat d)
    (hrow : ∀ i : Prim.Idx d, (∑ j : Prim.Idx d, U i j ^ (2 : Nat)) = 1)
    (hcol : ∀ j : Prim.Idx d, (∑ i : Prim.Idx d, U i j ^ (2 : Nat)) = 1) :
    DoublyStochasticKernel d where
  kernel := fun i j => U i j ^ (2 : Nat)
  entry_nonneg := by
    intro i j
    exact sq_nonneg (U i j)
  row_sum_eq_one := hrow
  col_sum_eq_one := hcol

@[simp] theorem fromSquareMatrix_kernel
    (U : Prim.Mat d)
    (hrow : ∀ i : Prim.Idx d, (∑ j : Prim.Idx d, U i j ^ (2 : Nat)) = 1)
    (hcol : ∀ j : Prim.Idx d, (∑ i : Prim.Idx d, U i j ^ (2 : Nat)) = 1)
    (i j : Prim.Idx d) :
    (fromSquareMatrix U hrow hcol).kernel i j = U i j ^ (2 : Nat) := by
  rfl

/-- Row square sums are one when `U * Uᵀ = 1`. -/
theorem row_square_sum_eq_one_of_mul_transpose_eq_one
    (U : Prim.Mat d) (hU : U * U.transpose = 1) (i : Prim.Idx d) :
    (∑ j : Prim.Idx d, U i j ^ (2 : Nat)) = 1 := by
  have hi := congrArg (fun M : Prim.Mat d => M i i) hU
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, pow_two] using hi

/-- Column square sums are one when `Uᵀ * U = 1`. -/
theorem col_square_sum_eq_one_of_transpose_mul_eq_one
    (U : Prim.Mat d) (hU : U.transpose * U = 1) (j : Prim.Idx d) :
    (∑ i : Prim.Idx d, U i j ^ (2 : Nat)) = 1 := by
  have hj := congrArg (fun M : Prim.Mat d => M j j) hU
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, pow_two] using hj

/-- A matrix satisfying the two orthogonality equations yields a square-entry kernel. -/
noncomputable def fromOrthogonalEquations
    (U : Prim.Mat d) (hrow : U * U.transpose = 1) (hcol : U.transpose * U = 1) :
    DoublyStochasticKernel d :=
  fromSquareMatrix U
    (row_square_sum_eq_one_of_mul_transpose_eq_one U hrow)
    (col_square_sum_eq_one_of_transpose_mul_eq_one U hcol)

@[simp] theorem fromOrthogonalEquations_kernel
    (U : Prim.Mat d) (hrow : U * U.transpose = 1) (hcol : U.transpose * U = 1)
    (i j : Prim.Idx d) :
    (fromOrthogonalEquations U hrow hcol).kernel i j = U i j ^ (2 : Nat) := by
  rfl

/-- A member of mathlib's real orthogonal group yields a square-entry kernel. -/
noncomputable def fromOrthogonalGroup
    (U : Prim.Mat d) (hU : U ∈ Matrix.orthogonalGroup (Prim.Idx d) ℝ) :
    DoublyStochasticKernel d :=
  fromOrthogonalEquations U
    ((Matrix.mem_orthogonalGroup_iff (A := U)).mp hU)
    ((Matrix.mem_orthogonalGroup_iff' (A := U)).mp hU)

@[simp] theorem fromOrthogonalGroup_kernel
    (U : Prim.Mat d) (hU : U ∈ Matrix.orthogonalGroup (Prim.Idx d) ℝ)
    (i j : Prim.Idx d) :
    (fromOrthogonalGroup U hU).kernel i j = U i j ^ (2 : Nat) := by
  simp [fromOrthogonalGroup, fromOrthogonalEquations, fromSquareMatrix]

/-- Selected sums through a square-entry kernel are the expected rotated-diagonal sums. -/
theorem fromSquareMatrix_selectedSum_eq
    (U : Prim.Mat d)
    (hrow : ∀ i : Prim.Idx d, (∑ j : Prim.Idx d, U i j ^ (2 : Nat)) = 1)
    (hcol : ∀ j : Prim.Idx d, (∑ i : Prim.Idx d, U i j ^ (2 : Nat)) = 1)
    (w : Prim.Idx d → ℝ) (I : Finset (Prim.Idx d)) :
    (fromSquareMatrix U hrow hcol).selectedSum w I =
      ∑ i ∈ I, ∑ j : Prim.Idx d, U i j ^ (2 : Nat) * w j := by
  rfl

end DoublyStochasticKernel

end Prim.LinearAlgebra
