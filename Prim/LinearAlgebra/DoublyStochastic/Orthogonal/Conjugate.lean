import Prim.LinearAlgebra.DoublyStochastic.Orthogonal.Kernel

namespace Prim.LinearAlgebra

open scoped BigOperators

namespace DoublyStochasticKernel

variable {d : Nat}

/--
Diagonal entry of an orthogonally rotated diagonal matrix, written as the
square-entry kernel applied to the diagonal profile.
-/
theorem diagonal_conjugate_diagonal_apply
    (U : Prim.Mat d) (w : Prim.Idx d → ℝ) (i : Prim.Idx d) :
    (U * Matrix.diagonal w * U.transpose) i i =
      ∑ j : Prim.Idx d, U i j ^ (2 : Nat) * w j := by
  calc
    (U * Matrix.diagonal w * U.transpose) i i
        = ∑ j : Prim.Idx d, (U * Matrix.diagonal w) i j * U.transpose j i := by
            simp [Matrix.mul_apply]
    _ = ∑ j : Prim.Idx d, (U i j * w j) * U i j := by
            simp [Matrix.transpose_apply]
    _ = ∑ j : Prim.Idx d, U i j ^ (2 : Nat) * w j := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring

/-- The square-kernel selected sum is the selected diagonal trace of `U * diagonal w * Uᵀ`. -/
theorem fromOrthogonalGroup_selectedSum_eq_diagonal_conjugate
    (U : Prim.Mat d) (hU : U ∈ Matrix.orthogonalGroup (Prim.Idx d) ℝ)
    (w : Prim.Idx d → ℝ) (I : Finset (Prim.Idx d)) :
    (fromOrthogonalGroup U hU).selectedSum w I =
      ∑ i ∈ I, (U * Matrix.diagonal w * U.transpose) i i := by
  calc
    (fromOrthogonalGroup U hU).selectedSum w I
        = ∑ i ∈ I, ∑ j : Prim.Idx d, U i j ^ (2 : Nat) * w j := by
            simp [DoublyStochasticKernel.selectedSum]
    _ = ∑ i ∈ I, (U * Matrix.diagonal w * U.transpose) i i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact (diagonal_conjugate_diagonal_apply U w i).symm

/-- Orthogonal matrices satisfy the selected-sum sandwich via their square-entry kernels. -/
theorem fromOrthogonalGroup_selectedSum_sandwich {k : Nat}
    (U : Prim.Mat d) (hU : U ∈ Matrix.orthogonalGroup (Prim.Idx d) ℝ)
    (w : Prim.Idx d → ℝ) (hanti : Antitone w)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    trailingPartialSum d w k ≤
        (fromOrthogonalGroup U hU).selectedSum w I ∧
      (fromOrthogonalGroup U hU).selectedSum w I ≤
        leadingPartialSum d w k := by
  exact (fromOrthogonalGroup U hU).selectedSum_sandwich w hanti hI

/--
Explicit square-entry form of the orthogonal-matrix Ky Fan sandwich.

This is the theorem to use when a rotated diagonal has already been reduced to
the coordinate formula `∑ j, U i j ^ 2 * w j`.
-/
theorem orthogonal_square_selectedSum_sandwich {k : Nat}
    (U : Prim.Mat d) (hU : U ∈ Matrix.orthogonalGroup (Prim.Idx d) ℝ)
    (w : Prim.Idx d → ℝ) (hanti : Antitone w)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    trailingPartialSum d w k ≤
        (∑ i ∈ I, ∑ j : Prim.Idx d, U i j ^ (2 : Nat) * w j) ∧
      (∑ i ∈ I, ∑ j : Prim.Idx d, U i j ^ (2 : Nat) * w j) ≤
        leadingPartialSum d w k := by
  simpa [DoublyStochasticKernel.selectedSum] using
    fromOrthogonalGroup_selectedSum_sandwich U hU w hanti hI

/--
Matrix-form Ky Fan sandwich for selected diagonal entries of
`U * diagonal w * Uᵀ`.
-/
theorem orthogonal_diagonal_conjugate_selectedSum_sandwich {k : Nat}
    (U : Prim.Mat d) (hU : U ∈ Matrix.orthogonalGroup (Prim.Idx d) ℝ)
    (w : Prim.Idx d → ℝ) (hanti : Antitone w)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    trailingPartialSum d w k ≤
        (∑ i ∈ I, (U * Matrix.diagonal w * U.transpose) i i) ∧
      (∑ i ∈ I, (U * Matrix.diagonal w * U.transpose) i i) ≤
        leadingPartialSum d w k := by
  simpa [fromOrthogonalGroup_selectedSum_eq_diagonal_conjugate U hU w I] using
    fromOrthogonalGroup_selectedSum_sandwich U hU w hanti hI

end DoublyStochasticKernel

end Prim.LinearAlgebra
