import Prim.LinearAlgebra.Majorization.Canonical.Sets.Cardinality

namespace Prim.LinearAlgebra

open scoped BigOperators

theorem leadingIndexSet_one {n : Nat} :
    leadingIndexSet (n + 1) 1 = ({0} : Finset (Prim.Idx (n + 1))) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_singleton]
    apply Fin.ext
    exact Nat.lt_one_iff.mp (mem_leadingIndexSet.mp hi)
  · intro hi
    rw [Finset.mem_singleton] at hi
    subst hi
    simp [mem_leadingIndexSet]

theorem trailingIndexSet_one {n : Nat} :
    trailingIndexSet (n + 1) 1 = ({Fin.last n} : Finset (Prim.Idx (n + 1))) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_singleton]
    apply Fin.ext
    have hlower : n ≤ i.1 := by
      simpa [Nat.succ_sub_one] using (mem_trailingIndexSet.mp hi)
    have hupper : i.1 ≤ n := Nat.le_of_lt_succ i.2
    exact Nat.le_antisymm hupper hlower
  · intro hi
    rw [Finset.mem_singleton] at hi
    subst hi
    simp [mem_trailingIndexSet]

theorem leadingIndexSet_pred {n : Nat} :
    leadingIndexSet (n + 1) n = Finset.univ.erase (Fin.last n) := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_univ]
  constructor
  · intro hi
    constructor
    · intro hEq
      apply Nat.lt_irrefl n
      simpa [hEq] using (mem_leadingIndexSet.mp hi)
    · trivial
  · intro hi
    have hne : i ≠ Fin.last n := hi.1
    have hlt_succ : i.1 < n + 1 := i.2
    have hle : i.1 ≤ n := Nat.le_of_lt_succ hlt_succ
    have hneval : i.1 ≠ n := by
      intro h
      apply hne
      apply Fin.ext
      simpa [Fin.last] using h
    exact mem_leadingIndexSet.mpr (lt_of_le_of_ne hle hneval)

theorem trailingIndexSet_pred {n : Nat} :
    trailingIndexSet (n + 1) n = Finset.univ.erase (0 : Prim.Idx (n + 1)) := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_univ]
  constructor
  · intro hi
    constructor
    · intro hEq
      apply Nat.lt_irrefl 1
      simpa [hEq] using (mem_trailingIndexSet.mp hi)
    · trivial
  · intro hi
    have hne : i ≠ (0 : Prim.Idx (n + 1)) := hi.1
    have hpos : 1 ≤ i.1 := by
      have hneval : i.1 ≠ 0 := by
        intro h
        apply hne
        apply Fin.ext
        simpa using h
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hneval)
    exact mem_trailingIndexSet.mpr (by simpa using hpos)

theorem trailingIndexSet_sub_eq_filter_not_lt {d k : Nat} (hk : k ≤ d) :
    trailingIndexSet d (d - k) = Finset.univ.filter (fun i : Prim.Idx d => ¬ i.1 < k) := by
  ext i
  rw [mem_trailingIndexSet]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Nat.sub_sub_self hk]
  exact (Nat.not_lt).symm

theorem leadingIndexSet_subset_leadingIndexSet {d k l : Nat} (hkl : k ≤ l) :
    leadingIndexSet d k ⊆ leadingIndexSet d l := by
  intro i hi
  exact mem_leadingIndexSet.mpr (lt_of_lt_of_le (mem_leadingIndexSet.mp hi) hkl)

theorem trailingIndexSet_subset_trailingIndexSet {d k l : Nat} (hkl : k ≤ l) :
    trailingIndexSet d k ⊆ trailingIndexSet d l := by
  intro i hi
  have hmem : d - k ≤ i.1 := mem_trailingIndexSet.mp hi
  have hsub : d - l ≤ d - k := Nat.sub_le_sub_left hkl d
  exact mem_trailingIndexSet.mpr (le_trans hsub hmem)

theorem leadingIndexSet_succ {d k : Nat} (hk : k < d) :
    leadingIndexSet d (k + 1) =
      insert (⟨k, hk⟩ : Prim.Idx d) (leadingIndexSet d k) := by
  ext i
  constructor
  · intro hi
    by_cases hEq : i = (⟨k, hk⟩ : Prim.Idx d)
    · simp [hEq]
    · have hik : i.1 < k + 1 := mem_leadingIndexSet.mp hi
      have hik' : i.1 < k := by
        have hle : i.1 ≤ k := Nat.le_of_lt_succ hik
        have hne : i.1 ≠ k := by
          intro hval
          apply hEq
          apply Fin.ext
          exact hval
        exact lt_of_le_of_ne hle hne
      simp [hEq, mem_leadingIndexSet.mpr hik']
  · intro hi
    simp only [Finset.mem_insert, mem_leadingIndexSet] at hi ⊢
    rcases hi with hEq | hik
    · subst hEq
      exact Nat.lt_succ_self k
    · omega

theorem trailingIndexSet_succ {d k : Nat} (hk : k < d) :
    trailingIndexSet d (k + 1) =
      insert (⟨d - (k + 1), by omega⟩ : Prim.Idx d) (trailingIndexSet d k) := by
  let j : Prim.Idx d := ⟨d - (k + 1), by omega⟩
  ext i
  constructor
  · intro hi
    by_cases hEq : i = j
    · simp [hEq, j]
    · have hik : d - (k + 1) ≤ i.1 := mem_trailingIndexSet.mp hi
      have hik' : d - k ≤ i.1 := by
        have hne : d - (k + 1) ≠ i.1 := by
          intro hval
          apply hEq
          apply Fin.ext
          dsimp [j]
          symm
          exact hval
        have hlt : d - (k + 1) < i.1 := lt_of_le_of_ne hik hne
        have hstep : d - k = d - (k + 1) + 1 := by
          omega
        simpa [hstep] using Nat.succ_le_of_lt hlt
      simp [hEq, j, mem_trailingIndexSet.mpr hik']
  · intro hi
    simp only [Finset.mem_insert, mem_trailingIndexSet] at hi ⊢
    rcases hi with hEq | hik
    · subst hEq
      dsimp [j]
      omega
    · omega

end Prim.LinearAlgebra
