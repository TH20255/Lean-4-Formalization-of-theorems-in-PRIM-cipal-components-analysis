import Prim.LinearAlgebra.MatrixMajorization.Fractional.KyFan.Sandwich
import Prim.LinearAlgebra.MatrixMajorization.PermutationKernel

namespace Prim.LinearAlgebra

open scoped BigOperators

/--
A finite doubly-stochastic kernel on the principal coordinate index set.

This is the light-weight matrix-majorization bridge needed for rotated
diagonals.  Once a rotated diagonal can be written as `kernel` applied to the
ordered principal values, the fractional Ky Fan theorem supplies the sandwich
bounds without requiring an explicit Birkhoff decomposition into permutations.
-/
structure DoublyStochasticKernel (d : Nat) where
  kernel : Prim.Idx d → Prim.Idx d → ℝ
  entry_nonneg : ∀ i j, 0 ≤ kernel i j
  row_sum_eq_one : ∀ i, (∑ j : Prim.Idx d, kernel i j) = 1
  col_sum_eq_one : ∀ j, (∑ i : Prim.Idx d, kernel i j) = 1

namespace DoublyStochasticKernel

variable {d : Nat} (K : DoublyStochasticKernel d)

/-- Selected value sum induced by a doubly-stochastic kernel. -/
noncomputable def selectedSum
    (w : Prim.Idx d → ℝ) (I : Finset (Prim.Idx d)) : ℝ :=
  ∑ i ∈ I, ∑ j : Prim.Idx d, K.kernel i j * w j

/-- Column weights induced by selecting rows `I`. -/
noncomputable def selectedColumnWeight
    (I : Finset (Prim.Idx d)) (j : Prim.Idx d) : ℝ :=
  ∑ i ∈ I, K.kernel i j

/-- Selected column weights are nonnegative. -/
theorem selectedColumnWeight_nonneg
    (I : Finset (Prim.Idx d)) (j : Prim.Idx d) :
    0 ≤ K.selectedColumnWeight I j := by
  unfold selectedColumnWeight
  exact Finset.sum_nonneg (fun i _hi => K.entry_nonneg i j)

/-- Selected column weights are bounded above by one. -/
theorem selectedColumnWeight_le_one
    (I : Finset (Prim.Idx d)) (j : Prim.Idx d) :
    K.selectedColumnWeight I j ≤ 1 := by
  calc
    K.selectedColumnWeight I j
        ≤ ∑ i : Prim.Idx d, K.kernel i j := by
            unfold selectedColumnWeight
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
              (fun i _hi_univ _hi_not => K.entry_nonneg i j)
    _ = 1 := K.col_sum_eq_one j

/-- The selected column weights have total mass equal to the number of selected rows. -/
theorem sum_selectedColumnWeight_eq_card
    (I : Finset (Prim.Idx d)) :
    (∑ j : Prim.Idx d, K.selectedColumnWeight I j) = (I.card : ℝ) := by
  calc
    (∑ j : Prim.Idx d, K.selectedColumnWeight I j)
        = ∑ j : Prim.Idx d, ∑ i ∈ I, K.kernel i j := by
            rfl
    _ = ∑ i ∈ I, ∑ j : Prim.Idx d, K.kernel i j := by
            exact Finset.sum_comm
    _ = ∑ i ∈ I, (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [K.row_sum_eq_one i]
    _ = (I.card : ℝ) := by
            simp

/-- Kernel-selected sums can be written using the induced fractional column weights. -/
theorem selectedSum_eq_sum_selectedColumnWeight
    (w : Prim.Idx d → ℝ) (I : Finset (Prim.Idx d)) :
    K.selectedSum w I =
      ∑ j : Prim.Idx d, K.selectedColumnWeight I j * w j := by
  unfold selectedSum selectedColumnWeight
  calc
    (∑ i ∈ I, ∑ j : Prim.Idx d, K.kernel i j * w j)
        = ∑ j : Prim.Idx d, ∑ i ∈ I, K.kernel i j * w j := by
            exact Finset.sum_comm
    _ = ∑ j : Prim.Idx d, (∑ i ∈ I, K.kernel i j) * w j := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [Finset.sum_mul]

/-- The fractional selection associated to a selected set of kernel rows. -/
noncomputable def toFractionalSelection
    (I : Finset (Prim.Idx d)) : FractionalSelection d where
  k := I.card
  weight := K.selectedColumnWeight I
  weight_nonneg := K.selectedColumnWeight_nonneg I
  weight_le_one := K.selectedColumnWeight_le_one I
  weight_sum_eq_k := K.sum_selectedColumnWeight_eq_card I

/-- Kernel-selected sums agree with the weighted sum of the induced fractional selection. -/
theorem selectedSum_eq_toFractionalSelection_weightedSum
    (w : Prim.Idx d → ℝ) (I : Finset (Prim.Idx d)) :
    K.selectedSum w I = (K.toFractionalSelection I).weightedSum w := by
  rw [K.selectedSum_eq_sum_selectedColumnWeight w I]
  rfl

/-- A doubly-stochastic kernel satisfies the fractional Ky Fan sandwich bounds. -/
theorem selectedSum_sandwich {k : Nat}
    (w : Prim.Idx d → ℝ) (hanti : Antitone w)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    trailingPartialSum d w k ≤ K.selectedSum w I ∧
      K.selectedSum w I ≤ leadingPartialSum d w k := by
  rw [K.selectedSum_eq_toFractionalSelection_weightedSum w I]
  simpa [toFractionalSelection, hI] using
    (K.toFractionalSelection I).weightedSum_sandwich w hanti

/-- The identity permutation kernel is doubly stochastic. -/
noncomputable def identity (d : Nat) : DoublyStochasticKernel d where
  kernel := permutationKernelEntry (Equiv.refl (Prim.Idx d))
  entry_nonneg := permutationKernelEntry_nonneg (Equiv.refl (Prim.Idx d))
  row_sum_eq_one := permutationKernelEntry_row_sum (Equiv.refl (Prim.Idx d))
  col_sum_eq_one := permutationKernelEntry_col_sum (Equiv.refl (Prim.Idx d))

@[simp] theorem identity_kernel (i j : Prim.Idx d) :
    (identity d).kernel i j = permutationKernelEntry (Equiv.refl (Prim.Idx d)) i j := by
  rfl

/--
Doubly-stochastic kernels provide the cardinality-aware ordered-value selection
bounds.  This is the preferred target for future rotated-diagonal work.
-/
noncomputable def toCardinalOrderedValueSelectionBounds
    (w : Prim.Idx d → ℝ) (hanti : Antitone w) (k : Nat) :
    CardinalOrderedValueSelectionBounds (DoublyStochasticKernel d) d where
  k := k
  principalValue := w
  principalValue_antitone := hanti
  selectedSum := fun K I => K.selectedSum w I
  principalRotation := identity d
  principal_selectedSum_eq := by
    intro I
    unfold selectedSum
    simp [permutationKernelEntry]
  lower_bound := by
    intro K I hI
    have hsand := K.selectedSum_sandwich w hanti hI
    calc
      (∑ i ∈ trailingIndexSet d k,
          ∑ j : Prim.Idx d,
            permutationKernelEntry (Equiv.refl (Prim.Idx d)) i j * w j)
          = trailingPartialSum d w k := by
            simp [trailingPartialSum, permutationKernelEntry]
      _ ≤ K.selectedSum w I := hsand.1
  upper_bound := by
    intro K I hI
    have hsand := K.selectedSum_sandwich w hanti hI
    calc
      K.selectedSum w I ≤ leadingPartialSum d w k := hsand.2
      _ = (∑ i ∈ leadingIndexSet d k,
          ∑ j : Prim.Idx d,
            permutationKernelEntry (Equiv.refl (Prim.Idx d)) i j * w j) := by
            simp [leadingPartialSum, permutationKernelEntry]

end DoublyStochasticKernel

end Prim.LinearAlgebra
