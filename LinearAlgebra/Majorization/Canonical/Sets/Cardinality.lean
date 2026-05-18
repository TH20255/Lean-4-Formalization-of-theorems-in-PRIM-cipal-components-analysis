import Prim.LinearAlgebra.Majorization.Canonical.Sets.Basic

namespace Prim.LinearAlgebra

open scoped BigOperators

/-- The canonical leading set has exactly `k` indices when `k ≤ d`. -/
theorem leadingIndexSet_card {d k : Nat} (hk : k ≤ d) :
    (leadingIndexSet d k).card = k := by
  let e : Fin k ↪ Prim.Idx d :=
    { toFun := fun i => ⟨i.1, lt_of_lt_of_le i.2 hk⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun x : Prim.Idx d => x.1) hij }
  have hset : leadingIndexSet d k = Finset.univ.map e := by
    ext i
    constructor
    · intro hi
      have hik : i.1 < k := mem_leadingIndexSet.mp hi
      refine Finset.mem_map.mpr ?_
      refine ⟨⟨i.1, hik⟩, by simp, ?_⟩
      apply Fin.ext
      rfl
    · intro hi
      rcases Finset.mem_map.mp hi with ⟨j, _hj, rfl⟩
      exact mem_leadingIndexSet.mpr j.2
  rw [hset]
  simp

/-- The canonical trailing set has exactly `k` indices when `k ≤ d`. -/
theorem trailingIndexSet_card {d k : Nat} (hk : k ≤ d) :
    (trailingIndexSet d k).card = k := by
  let e : Fin k ↪ Prim.Idx d :=
    { toFun := fun i => ⟨d - k + i.1, by omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        have hval := congrArg (fun x : Prim.Idx d => x.1) hij
        dsimp at hval
        omega }
  have hset : trailingIndexSet d k = Finset.univ.map e := by
    ext i
    constructor
    · intro hi
      have hlow : d - k ≤ i.1 := mem_trailingIndexSet.mp hi
      let j : Fin k := ⟨i.1 - (d - k), by omega⟩
      refine Finset.mem_map.mpr ?_
      refine ⟨j, by simp, ?_⟩
      apply Fin.ext
      dsimp [e, j]
      omega
    · intro hi
      rcases Finset.mem_map.mp hi with ⟨j, _hj, rfl⟩
      exact mem_trailingIndexSet.mpr (by dsimp [e]; omega)
  rw [hset]
  simp

/-- Moving from the first `k` to the first `k + 1` canonical indices adds one element. -/
theorem leadingIndexSet_card_succ {d k : Nat} (hk : k < d) :
    (leadingIndexSet d (k + 1)).card = (leadingIndexSet d k).card + 1 := by
  rw [leadingIndexSet_card (Nat.succ_le_of_lt hk), leadingIndexSet_card (Nat.le_of_lt hk)]

/-- Moving from the last `k` to the last `k + 1` canonical indices adds one element. -/
theorem trailingIndexSet_card_succ {d k : Nat} (hk : k < d) :
    (trailingIndexSet d (k + 1)).card = (trailingIndexSet d k).card + 1 := by
  rw [trailingIndexSet_card (Nat.succ_le_of_lt hk), trailingIndexSet_card (Nat.le_of_lt hk)]

end Prim.LinearAlgebra
