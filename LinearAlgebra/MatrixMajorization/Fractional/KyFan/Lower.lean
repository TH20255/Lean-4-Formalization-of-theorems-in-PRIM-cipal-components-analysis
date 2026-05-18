import Prim.LinearAlgebra.MatrixMajorization.Fractional.KyFan.Common

namespace Prim.LinearAlgebra

open scoped BigOperators

namespace FractionalSelection

variable {d : Nat} (F : FractionalSelection d)

/-- Fractional Ky Fan lower bound for antitone ordered values. -/
theorem trailingPartialSum_le_weightedSum
    (w : Prim.Idx d → ℝ) (hanti : Antitone w) :
    trailingPartialSum d w F.k ≤ F.weightedSum w := by
  let T : Finset (Prim.Idx d) := trailingIndexSet d F.k
  let C : Finset (Prim.Idx d) :=
    Finset.univ.filter (fun j : Prim.Idx d => j ∉ T)
  have hsplit_weighted :
      F.weightedSum w =
        Finset.sum T (fun j => F.weight j * w j) +
          Finset.sum C (fun j => F.weight j * w j) := by
    unfold weightedSum
    have h :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun j : Prim.Idx d => j ∈ T)
        (f := fun j => F.weight j * w j)
    simpa [T, C] using h.symm
  have hsplit_trailing :
      trailingPartialSum d w F.k =
        Finset.sum T (fun j => F.weight j * w j) +
          Finset.sum T (fun j => ((1 : ℝ) - F.weight j) * w j) := by
    unfold trailingPartialSum
    calc
      Finset.sum (trailingIndexSet d F.k) w
          = Finset.sum T (fun j => F.weight j * w j + ((1 : ℝ) - F.weight j) * w j) := by
              refine Finset.sum_congr ?_ ?_
              · simp [T]
              · intro j _hj
                ring
      _ = Finset.sum T (fun j => F.weight j * w j) +
            Finset.sum T (fun j => ((1 : ℝ) - F.weight j) * w j) := by
              rw [Finset.sum_add_distrib]
  have hdeficit_le_outside :
      Finset.sum T (fun j => ((1 : ℝ) - F.weight j) * w j) ≤
        Finset.sum C (fun j => F.weight j * w j) := by
    refine weighted_sum_le_weighted_sum_of_pairwise_le
      (A := C) (B := T)
      (p := F.weight) (q := fun j => (1 : ℝ) - F.weight j)
      (a := w) (b := w) ?_ ?_ ?_ ?_
    · intro i _hi
      exact F.weight_nonneg i
    · intro j _hj
      exact sub_nonneg.mpr (F.weight_le_one j)
    · simpa [T, C] using F.trailing_deficit_eq_not_trailing_mass.symm
    · intro i hi j hj
      have hj_ge : d - F.k ≤ j.1 := by
        exact mem_trailingIndexSet.mp (by simpa [T] using hj)
      have hi_not : i ∉ trailingIndexSet d F.k := by
        have hi_not_T : i ∉ T := (Finset.mem_filter.mp hi).2
        simpa [T] using hi_not_T
      have hi_lt : i.1 < d - F.k := by
        exact Nat.lt_of_not_ge (by
          intro hi_ge
          exact hi_not (mem_trailingIndexSet.mpr hi_ge))
      exact hanti (Fin.le_iff_val_le_val.mpr (le_trans (Nat.le_of_lt hi_lt) hj_ge))
  calc
    trailingPartialSum d w F.k
        = Finset.sum T (fun j => F.weight j * w j) +
            Finset.sum T (fun j => ((1 : ℝ) - F.weight j) * w j) := hsplit_trailing
    _ ≤ Finset.sum T (fun j => F.weight j * w j) +
          Finset.sum C (fun j => F.weight j * w j) := by
            exact add_le_add (le_refl _) hdeficit_le_outside
    _ = F.weightedSum w := hsplit_weighted.symm

end FractionalSelection

end Prim.LinearAlgebra
