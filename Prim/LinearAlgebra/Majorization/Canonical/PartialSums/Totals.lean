import Prim.LinearAlgebra.Majorization.Canonical.PartialSums.Basic
import Prim.LinearAlgebra.Majorization.Canonical.Sets.Recurrence

namespace Prim.LinearAlgebra

open scoped BigOperators

theorem leadingPartialSum_add_trailingPartialSum_sub_eq_total
    (d : Nat) (w : Prim.Idx d → ℝ) {k : Nat} (hk : k ≤ d) :
    leadingPartialSum d w k + trailingPartialSum d w (d - k) = Finset.sum Finset.univ w := by
  rw [leadingPartialSum, trailingPartialSum, trailingIndexSet_sub_eq_filter_not_lt hk]
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun i : Prim.Idx d => i.1 < k) (f := w))

theorem trailingPartialSum_add_leadingPartialSum_sub_eq_total
    (d : Nat) (w : Prim.Idx d → ℝ) {k : Nat} (hk : k ≤ d) :
    trailingPartialSum d w k + leadingPartialSum d w (d - k) = Finset.sum Finset.univ w := by
  have hk' : d - k ≤ d := Nat.sub_le _ _
  have hsplit := leadingPartialSum_add_trailingPartialSum_sub_eq_total d w hk'
  rw [Nat.sub_sub_self hk, add_comm] at hsplit
  exact hsplit

end Prim.LinearAlgebra
