import Prim.LinearAlgebra.MatrixMajorization.Base

namespace Prim.LinearAlgebra

open scoped BigOperators

/-- Entry of the permutation matrix associated to `σ`. -/
def permutationKernelEntry {d : Nat}
    (σ : Equiv.Perm (Prim.Idx d)) (i j : Prim.Idx d) : ℝ :=
  if σ i = j then 1 else 0

/-- Permutation-matrix entries are nonnegative. -/
theorem permutationKernelEntry_nonneg {d : Nat}
    (σ : Equiv.Perm (Prim.Idx d)) (i j : Prim.Idx d) :
    0 ≤ permutationKernelEntry σ i j := by
  by_cases h : σ i = j <;> simp [permutationKernelEntry, h]

/-- Each row of a permutation matrix sums to one. -/
theorem permutationKernelEntry_row_sum {d : Nat}
    (σ : Equiv.Perm (Prim.Idx d)) (i : Prim.Idx d) :
    (∑ j : Prim.Idx d, permutationKernelEntry σ i j) = 1 := by
  rw [Finset.sum_eq_single (σ i)]
  · simp [permutationKernelEntry]
  · intro j _hj hne
    simp [permutationKernelEntry, hne.symm]
  · intro hnot
    simp at hnot

/-- Each column of a permutation matrix sums to one. -/
theorem permutationKernelEntry_col_sum {d : Nat}
    (σ : Equiv.Perm (Prim.Idx d)) (j : Prim.Idx d) :
    (∑ i : Prim.Idx d, permutationKernelEntry σ i j) = 1 := by
  rw [Finset.sum_eq_single (σ.symm j)]
  · simp [permutationKernelEntry]
  · intro i _hi hne
    have hne' : σ i ≠ j := by
      intro h
      apply hne
      exact σ.injective (by simpa using h)
    simp [permutationKernelEntry, hne']
  · intro hnot
    simp at hnot

/-- Multiplying a permutation-matrix row by a value profile picks the permuted value. -/
theorem permutationKernelEntry_sum_mul_value {d : Nat}
    (w : Prim.Idx d → ℝ) (σ : Equiv.Perm (Prim.Idx d)) (i : Prim.Idx d) :
    (∑ j : Prim.Idx d, permutationKernelEntry σ i j * w j) = w (σ i) := by
  rw [Finset.sum_eq_single (σ i)]
  · simp [permutationKernelEntry]
  · intro j _hj hne
    simp [permutationKernelEntry, hne.symm]
  · intro hnot
    simp at hnot


end Prim.LinearAlgebra
