import Prim.LinearAlgebra.Majorization.Canonical.PartialSums.Basic
import Prim.LinearAlgebra.Majorization.Canonical.Sets.Recurrence

namespace Prim.LinearAlgebra

open scoped BigOperators

theorem leadingPartialSum_succ {d k : Nat} (w : Prim.Idx d → ℝ) (hk : k < d) :
    leadingPartialSum d w (k + 1) =
      leadingPartialSum d w k + w (⟨k, hk⟩ : Prim.Idx d) := by
  rw [leadingPartialSum, leadingIndexSet_succ hk]
  have hnot : (⟨k, hk⟩ : Prim.Idx d) ∉ leadingIndexSet d k := by
    simp [mem_leadingIndexSet]
  rw [Finset.sum_insert hnot, leadingPartialSum]
  ring

theorem trailingPartialSum_succ {d k : Nat} (w : Prim.Idx d → ℝ) (hk : k < d) :
    trailingPartialSum d w (k + 1) =
      trailingPartialSum d w k + w (⟨d - (k + 1), by omega⟩ : Prim.Idx d) := by
  let j : Prim.Idx d := ⟨d - (k + 1), by omega⟩
  rw [trailingPartialSum, trailingIndexSet_succ hk]
  have hnot : j ∉ trailingIndexSet d k := by
    simp [j, mem_trailingIndexSet]
    omega
  rw [Finset.sum_insert hnot, trailingPartialSum]
  ring

theorem leadingPartialSum_succ_sub {d k : Nat} (w : Prim.Idx d → ℝ) (hk : k < d) :
    leadingPartialSum d w (k + 1) - leadingPartialSum d w k =
      w (⟨k, hk⟩ : Prim.Idx d) := by
  rw [leadingPartialSum_succ w hk]
  ring

theorem trailingPartialSum_succ_sub {d k : Nat} (w : Prim.Idx d → ℝ) (hk : k < d) :
    trailingPartialSum d w (k + 1) - trailingPartialSum d w k =
      w (⟨d - (k + 1), by omega⟩ : Prim.Idx d) := by
  rw [trailingPartialSum_succ w hk]
  ring

end Prim.LinearAlgebra
