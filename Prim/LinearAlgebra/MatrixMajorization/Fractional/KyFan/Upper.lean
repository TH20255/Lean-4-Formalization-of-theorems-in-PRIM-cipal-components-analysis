import Prim.LinearAlgebra.MatrixMajorization.Fractional.KyFan.Common

namespace Prim.LinearAlgebra

open scoped BigOperators

namespace FractionalSelection

variable {d : Nat} (F : FractionalSelection d)

/-- Fractional Ky Fan upper bound for antitone ordered values. -/
theorem weightedSum_le_leadingPartialSum
    (w : Prim.Idx d → ℝ) (hanti : Antitone w) :
    F.weightedSum w ≤ leadingPartialSum d w F.k := by
  let L : Finset (Prim.Idx d) := leadingIndexSet d F.k
  let C : Finset (Prim.Idx d) :=
    Finset.univ.filter (fun j : Prim.Idx d => j ∉ L)
  have hsplit_weighted :
      F.weightedSum w =
        Finset.sum L (fun j => F.weight j * w j) +
          Finset.sum C (fun j => F.weight j * w j) := by
    unfold weightedSum
    have h :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun j : Prim.Idx d => j ∈ L)
        (f := fun j => F.weight j * w j)
    simpa [L, C] using h.symm
  have hsplit_leading :
      leadingPartialSum d w F.k =
        Finset.sum L (fun j => F.weight j * w j) +
          Finset.sum L (fun j => ((1 : ℝ) - F.weight j) * w j) := by
    unfold leadingPartialSum
    calc
      Finset.sum (leadingIndexSet d F.k) w
          = Finset.sum L (fun j => F.weight j * w j + ((1 : ℝ) - F.weight j) * w j) := by
              refine Finset.sum_congr ?_ ?_
              · simp [L]
              · intro j _hj
                ring
      _ = Finset.sum L (fun j => F.weight j * w j) +
            Finset.sum L (fun j => ((1 : ℝ) - F.weight j) * w j) := by
              rw [Finset.sum_add_distrib]
  have houtside_le_deficit :
      Finset.sum C (fun j => F.weight j * w j) ≤
        Finset.sum L (fun j => ((1 : ℝ) - F.weight j) * w j) := by
    refine weighted_sum_le_weighted_sum_of_pairwise_le
      (A := L) (B := C)
      (p := fun j => (1 : ℝ) - F.weight j) (q := F.weight)
      (a := w) (b := w) ?_ ?_ ?_ ?_
    · intro i _hi
      exact sub_nonneg.mpr (F.weight_le_one i)
    · intro j _hj
      exact F.weight_nonneg j
    · simpa [L, C] using F.leading_deficit_eq_not_leading_mass
    · intro i hi j hj
      have hi_lt : i.1 < F.k := by
        exact mem_leadingIndexSet.mp (by simpa [L] using hi)
      have hj_not : j ∉ leadingIndexSet d F.k := by
        have hj_not_L : j ∉ L := (Finset.mem_filter.mp hj).2
        simpa [L] using hj_not_L
      have hj_ge : F.k ≤ j.1 := by
        exact Nat.not_lt.mp (by
          intro hj_lt
          exact hj_not (mem_leadingIndexSet.mpr hj_lt))
      exact hanti (Fin.le_iff_val_le_val.mpr (le_trans (Nat.le_of_lt hi_lt) hj_ge))
  calc
    F.weightedSum w
        = Finset.sum L (fun j => F.weight j * w j) +
            Finset.sum C (fun j => F.weight j * w j) := hsplit_weighted
    _ ≤ Finset.sum L (fun j => F.weight j * w j) +
          Finset.sum L (fun j => ((1 : ℝ) - F.weight j) * w j) := by
            exact add_le_add (le_refl _) houtside_le_deficit
    _ = leadingPartialSum d w F.k := hsplit_leading.symm

end FractionalSelection

end Prim.LinearAlgebra
