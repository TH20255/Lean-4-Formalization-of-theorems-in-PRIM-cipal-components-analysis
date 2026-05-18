import Prim.LinearAlgebra.MatrixMajorization.Fractional.Basic

namespace Prim.LinearAlgebra

open scoped BigOperators

namespace FractionalSelection

/--
If two nonnegative weighted families have the same total mass and every
`b`-value in the source family is bounded by every `a`-value in the target
family, then the weighted `b`-sum is bounded by the weighted `a`-sum.
-/
theorem weighted_sum_le_weighted_sum_of_pairwise_le
    {α β : Type*} (A : Finset α) (B : Finset β)
    (p : α → ℝ) (q : β → ℝ) (a : α → ℝ) (b : β → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) (hq : ∀ j ∈ B, 0 ≤ q j)
    (hmass : Finset.sum A p = Finset.sum B q)
    (hle : ∀ i ∈ A, ∀ j ∈ B, b j ≤ a i) :
    Finset.sum B (fun j => q j * b j) ≤
      Finset.sum A (fun i => p i * a i) := by
  let M : ℝ := Finset.sum A p
  by_cases hM : M = 0
  · have hpzero : ∀ i ∈ A, p i = 0 := by
      intro i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg hp).mp (by simpa [M] using hM) i hi
    have hqsum : Finset.sum B q = 0 := by
      simpa [← hmass, M] using hM
    have hqzero : ∀ j ∈ B, q j = 0 := by
      intro j hj
      exact (Finset.sum_eq_zero_iff_of_nonneg hq).mp hqsum j hj
    have hleft : Finset.sum B (fun j => q j * b j) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      rw [hqzero j hj, zero_mul]
    have hright : Finset.sum A (fun i => p i * a i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      rw [hpzero i hi, zero_mul]
    rw [hleft, hright]
  · have hM_nonneg : 0 ≤ M := by
      simpa [M] using Finset.sum_nonneg hp
    have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM)
    have hdouble :
        Finset.sum A (fun i => Finset.sum B (fun j => (p i * q j) * b j)) ≤
          Finset.sum A (fun i => Finset.sum B (fun j => (p i * q j) * a i)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      exact mul_le_mul_of_nonneg_left (hle i hi j hj)
        (mul_nonneg (hp i hi) (hq j hj))
    have hleft :
        M * Finset.sum B (fun j => q j * b j) =
          Finset.sum A (fun i => Finset.sum B (fun j => (p i * q j) * b j)) := by
      calc
        M * Finset.sum B (fun j => q j * b j)
            = (Finset.sum A p) * Finset.sum B (fun j => q j * b j) := by
                simp [M]
        _ = Finset.sum A (fun i => p i * Finset.sum B (fun j => q j * b j)) := by
                rw [Finset.sum_mul]
        _ = Finset.sum A (fun i => Finset.sum B (fun j => p i * (q j * b j))) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                rw [Finset.mul_sum]
        _ = Finset.sum A (fun i => Finset.sum B (fun j => (p i * q j) * b j)) := by
                simp [mul_assoc]
    have hright :
        M * Finset.sum A (fun i => p i * a i) =
          Finset.sum A (fun i => Finset.sum B (fun j => (p i * q j) * a i)) := by
      calc
        M * Finset.sum A (fun i => p i * a i)
            = (Finset.sum A p) * Finset.sum A (fun i => p i * a i) := by
                simp [M]
        _ = (Finset.sum B q) * Finset.sum A (fun i => p i * a i) := by
                rw [hmass]
        _ = Finset.sum B (fun j => q j * Finset.sum A (fun i => p i * a i)) := by
                rw [Finset.sum_mul]
        _ = Finset.sum B (fun j => Finset.sum A (fun i => q j * (p i * a i))) := by
                refine Finset.sum_congr rfl ?_
                intro j _hj
                rw [Finset.mul_sum]
        _ = Finset.sum A (fun i => Finset.sum B (fun j => q j * (p i * a i))) := by
                exact Finset.sum_comm
        _ = Finset.sum A (fun i => Finset.sum B (fun j => (p i * q j) * a i)) := by
                simp [mul_left_comm, mul_comm]
    exact le_of_mul_le_mul_of_pos_left (by
      rw [hleft, hright]
      exact hdouble) hM_pos

end FractionalSelection

end Prim.LinearAlgebra
