import Prim.LinearAlgebra.DoublyStochastic.Orthogonal.Conjugate

namespace Prim.LinearAlgebra

open scoped BigOperators

namespace DoublyStochasticKernel

/-- Orthogonal matrices as the concrete rotation family for the matrix bridge. -/
abbrev OrthogonalMatrixRotation (d : Nat) :=
  { U : Prim.Mat d // U ∈ Matrix.orthogonalGroup (Prim.Idx d) ℝ }

namespace OrthogonalMatrixRotation

variable {d : Nat}

/-- The underlying matrix of an orthogonal-matrix rotation. -/
abbrev matrix (U : OrthogonalMatrixRotation d) : Prim.Mat d := U.1

/-- The identity rotation as an orthogonal matrix. -/
noncomputable def identity (d : Nat) : OrthogonalMatrixRotation d :=
  ⟨1, by
    rw [Matrix.mem_orthogonalGroup_iff]
    simp⟩

@[simp] theorem identity_matrix (d : Nat) :
    (identity d).matrix = (1 : Prim.Mat d) := by
  rfl

@[simp] theorem matrix_mem_orthogonalGroup (U : OrthogonalMatrixRotation d) :
    U.matrix ∈ Matrix.orthogonalGroup (Prim.Idx d) ℝ :=
  U.2

/-- Selected diagonal sum after conjugating a diagonal principal profile by an orthogonal matrix. -/
noncomputable def selectedDiagonalSum
    (w : Prim.Idx d → ℝ) (U : OrthogonalMatrixRotation d)
    (I : Finset (Prim.Idx d)) : ℝ :=
  ∑ i ∈ I, (U.matrix * Matrix.diagonal w * U.matrix.transpose) i i

/-- The identity rotation recovers ordinary selected sums of the principal profile. -/
theorem identity_selectedDiagonalSum_eq
    (w : Prim.Idx d → ℝ) (I : Finset (Prim.Idx d)) :
    selectedDiagonalSum w (identity d) I = Finset.sum I w := by
  unfold selectedDiagonalSum
  simp

/--
Concrete cardinal Ky Fan bounds for orthogonal diagonal conjugations.

This packages `orthogonal_diagonal_conjugate_selectedSum_sandwich` into the
cardinality-aware selection-bound interface used by theorem-facing layers.
-/
noncomputable def toCardinalOrderedValueSelectionBounds
    (w : Prim.Idx d → ℝ) (hanti : Antitone w) (k : Nat) :
    CardinalOrderedValueSelectionBounds (OrthogonalMatrixRotation d) d where
  k := k
  principalValue := w
  principalValue_antitone := hanti
  selectedSum := selectedDiagonalSum w
  principalRotation := identity d
  principal_selectedSum_eq := identity_selectedDiagonalSum_eq w
  lower_bound := by
    intro U I hI
    have hsand :=
      orthogonal_diagonal_conjugate_selectedSum_sandwich
        U.matrix U.matrix_mem_orthogonalGroup w hanti hI
    calc
      selectedDiagonalSum w (identity d) (trailingIndexSet d k)
          = trailingPartialSum d w k := by
              rw [identity_selectedDiagonalSum_eq]
              rfl
      _ ≤ selectedDiagonalSum w U I := hsand.1
  upper_bound := by
    intro U I hI
    have hsand :=
      orthogonal_diagonal_conjugate_selectedSum_sandwich
        U.matrix U.matrix_mem_orthogonalGroup w hanti hI
    calc
      selectedDiagonalSum w U I ≤ leadingPartialSum d w k := hsand.2
      _ = selectedDiagonalSum w (identity d) (leadingIndexSet d k) := by
              rw [identity_selectedDiagonalSum_eq]
              rfl

/-- Sandwich theorem specialized to the concrete orthogonal-matrix rotation family. -/
theorem selectedDiagonalSum_sandwich {k : Nat}
    (w : Prim.Idx d → ℝ) (hanti : Antitone w)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    trailingPartialSum d w k ≤ selectedDiagonalSum w U I ∧
      selectedDiagonalSum w U I ≤ leadingPartialSum d w k := by
  exact (toCardinalOrderedValueSelectionBounds w hanti k).selectedSum_sandwich U hI

end OrthogonalMatrixRotation

end DoublyStochasticKernel

end Prim.LinearAlgebra
