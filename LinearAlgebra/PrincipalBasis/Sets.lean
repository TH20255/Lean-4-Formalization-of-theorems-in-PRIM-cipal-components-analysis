import Prim.LinearAlgebra.PrincipalBasis.Core
import Prim.LinearAlgebra.Majorization.Canonical.Sets.Recurrence

namespace Prim.LinearAlgebra

open scoped BigOperators

namespace PrincipalBasisData

variable {d : Nat} (B : PrincipalBasisData d)

theorem leadingSet_zero :
    B.leadingSet 0 = ∅ := by
  ext i
  simp [mem_leadingSet]

theorem trailingSet_zero :
    B.trailingSet 0 = ∅ := by
  ext i
  simp [mem_trailingSet]

theorem leadingSet_all :
    B.leadingSet d = Finset.univ := by
  ext i
  simp [mem_leadingSet]

theorem trailingSet_all :
    B.trailingSet d = Finset.univ := by
  ext i
  simp [mem_trailingSet]

/-- The principal leading set agrees with the canonical ordered index set. -/
theorem leadingSet_eq_leadingIndexSet (k : Nat) :
    B.leadingSet k = leadingIndexSet d k := by
  ext i
  simp [mem_leadingSet, mem_leadingIndexSet]

/-- The principal trailing set agrees with the canonical ordered index set. -/
theorem trailingSet_eq_trailingIndexSet (k : Nat) :
    B.trailingSet k = trailingIndexSet d k := by
  ext i
  simp [mem_trailingSet, mem_trailingIndexSet]

/-- The principal leading set has exactly `k` coordinates when `k ≤ d`. -/
theorem leadingSet_card {k : Nat} (hk : k ≤ d) :
    (B.leadingSet k).card = k := by
  rw [B.leadingSet_eq_leadingIndexSet]
  exact leadingIndexSet_card hk

/-- The principal trailing set has exactly `k` coordinates when `k ≤ d`. -/
theorem trailingSet_card {k : Nat} (hk : k ≤ d) :
    (B.trailingSet k).card = k := by
  rw [B.trailingSet_eq_trailingIndexSet]
  exact trailingIndexSet_card hk

/-- Moving from the first `k` to the first `k + 1` principal coordinates adds one element. -/
theorem leadingSet_card_succ {k : Nat} (hk : k < d) :
    (B.leadingSet (k + 1)).card = (B.leadingSet k).card + 1 := by
  rw [B.leadingSet_eq_leadingIndexSet, B.leadingSet_eq_leadingIndexSet]
  exact leadingIndexSet_card_succ hk

/-- Moving from the last `k` to the last `k + 1` principal coordinates adds one element. -/
theorem trailingSet_card_succ {k : Nat} (hk : k < d) :
    (B.trailingSet (k + 1)).card = (B.trailingSet k).card + 1 := by
  rw [B.trailingSet_eq_trailingIndexSet, B.trailingSet_eq_trailingIndexSet]
  exact trailingIndexSet_card_succ hk

theorem leadingSet_succ {k : Nat} (hk : k < d) :
    B.leadingSet (k + 1) = insert (⟨k, hk⟩ : Prim.Idx d) (B.leadingSet k) := by
  rw [B.leadingSet_eq_leadingIndexSet, B.leadingSet_eq_leadingIndexSet]
  exact leadingIndexSet_succ hk

theorem trailingSet_succ {k : Nat} (hk : k < d) :
    B.trailingSet (k + 1) =
      insert (⟨d - (k + 1), by omega⟩ : Prim.Idx d) (B.trailingSet k) := by
  rw [B.trailingSet_eq_trailingIndexSet, B.trailingSet_eq_trailingIndexSet]
  exact trailingIndexSet_succ hk

end PrincipalBasisData

end Prim.LinearAlgebra
