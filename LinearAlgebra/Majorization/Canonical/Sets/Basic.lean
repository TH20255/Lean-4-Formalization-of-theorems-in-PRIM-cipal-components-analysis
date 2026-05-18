import Prim.Basic

namespace Prim.LinearAlgebra

open scoped BigOperators

/-- First `k` canonical indices in `Fin d`. -/
def leadingIndexSet (d k : Nat) : Finset (Prim.Idx d) :=
  Finset.univ.filter (fun i => i.1 < k)

/-- Last `k` canonical indices in `Fin d`. -/
def trailingIndexSet (d k : Nat) : Finset (Prim.Idx d) :=
  Finset.univ.filter (fun i => d - k ≤ i.1)

theorem mem_leadingIndexSet {d k : Nat} {i : Prim.Idx d} :
    i ∈ leadingIndexSet d k ↔ i.1 < k := by
  simp [leadingIndexSet]

theorem mem_trailingIndexSet {d k : Nat} {i : Prim.Idx d} :
    i ∈ trailingIndexSet d k ↔ d - k ≤ i.1 := by
  simp [trailingIndexSet]

theorem leadingIndexSet_zero (d : Nat) :
    leadingIndexSet d 0 = ∅ := by
  ext i
  simp [mem_leadingIndexSet]

theorem trailingIndexSet_zero (d : Nat) :
    trailingIndexSet d 0 = ∅ := by
  ext i
  simp [mem_trailingIndexSet]

theorem leadingIndexSet_all (d : Nat) :
    leadingIndexSet d d = Finset.univ := by
  ext i
  simp [mem_leadingIndexSet]

theorem trailingIndexSet_all (d : Nat) :
    trailingIndexSet d d = Finset.univ := by
  ext i
  simp [mem_trailingIndexSet]

end Prim.LinearAlgebra
