import Prim.LinearAlgebra.Majorization.Canonical.PartialSums.Basic
import Mathlib.Data.Finset.Sort

namespace Prim.LinearAlgebra

open scoped BigOperators

theorem strictMono_fin_nat_id_le {k : Nat} {f : Fin k → Nat} (hf : StrictMono f) :
    ∀ i : Fin k, i.1 ≤ f i := by
  intro i
  refine Fin.strong_induction_on (motive := fun i : Fin k => i.1 ≤ f i) ?_ i
  intro j ih
  by_cases hzero : j.1 = 0
  · omega
  · let p : Fin k := ⟨j.1 - 1, by omega⟩
    have hpj : p < j := by
      rw [Fin.lt_def]
      dsimp [p]
      omega
    have hp_le : p.1 ≤ f p := ih p hpj
    have hfp_lt : f p < f j := hf hpj
    have hsucc : p.1 + 1 ≤ f j := Nat.succ_le_of_lt (lt_of_le_of_lt hp_le hfp_lt)
    have hpval : p.1 + 1 = j.1 := by
      dsimp [p]
      omega
    omega

/--
An increasing enumeration of a `k`-element subset of `Fin d` lies pointwise
above the canonical first `k` indices.
-/
theorem castLE_le_orderEmbOfFin {d k : Nat} (hk : k ≤ d)
    (I : Finset (Prim.Idx d)) (hI : I.card = k) (i : Fin k) :
    Fin.castLE hk i ≤ I.orderEmbOfFin hI i := by
  rw [Fin.le_iff_val_le_val]
  have hmono :
      StrictMono (fun i : Fin k => ((I.orderEmbOfFin hI i : Prim.Idx d) : Nat)) := by
    intro a b hab
    exact (I.orderEmbOfFin hI).strictMono hab
  simpa using strictMono_fin_nat_id_le hmono i

/-- The canonical leading set is the image of the order-preserving cast `Fin k -> Fin d`. -/
theorem leadingIndexSet_eq_map_castLE {d k : Nat} (hk : k ≤ d) :
    leadingIndexSet d k =
      Finset.map (Fin.castLEOrderEmb hk).toEmbedding (Finset.univ : Finset (Fin k)) := by
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

/-- A leading partial sum can be written as a sum over `Fin k`. -/
theorem leadingPartialSum_eq_sum_fin {d k : Nat}
    (w : Prim.Idx d → ℝ) (hk : k ≤ d) :
    leadingPartialSum d w k =
      Finset.sum (Finset.univ : Finset (Fin k)) (fun i => w (Fin.castLE hk i)) := by
  rw [leadingPartialSum, leadingIndexSet_eq_map_castLE hk]
  exact Finset.sum_map
    (s := (Finset.univ : Finset (Fin k)))
    (e := (Fin.castLEOrderEmb hk).toEmbedding) (f := w)

/-- A selected sum over a `k`-element set can be written using its increasing enumeration. -/
theorem sum_eq_sum_orderEmbOfFin {d k : Nat}
    (w : Prim.Idx d → ℝ) (I : Finset (Prim.Idx d)) (hI : I.card = k) :
    Finset.sum I w =
      Finset.sum (Finset.univ : Finset (Fin k)) (fun i => w (I.orderEmbOfFin hI i)) := by
  calc
    Finset.sum I w =
        Finset.sum (Finset.map (I.orderEmbOfFin hI).toEmbedding
          (Finset.univ : Finset (Fin k))) w := by
          rw [I.map_orderEmbOfFin_univ hI]
    _ = Finset.sum (Finset.univ : Finset (Fin k))
          (fun i => w (I.orderEmbOfFin hI i)) := by
          exact Finset.sum_map
            (s := (Finset.univ : Finset (Fin k)))
            (e := (I.orderEmbOfFin hI).toEmbedding) (f := w)

end Prim.LinearAlgebra
