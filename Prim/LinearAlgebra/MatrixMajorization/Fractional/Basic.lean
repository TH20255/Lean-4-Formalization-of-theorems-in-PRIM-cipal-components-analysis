import Prim.LinearAlgebra.Majorization.Finite
import Prim.LinearAlgebra.Majorization.Canonical.Sets.Cardinality
import Prim.LinearAlgebra.MatrixMajorization.Base

namespace Prim.LinearAlgebra

open scoped BigOperators

/--
A fractional `k`-selection of coordinates.

The integral case is the indicator of a `k`-element set.  The kernel bridge below
produces fractional selections by summing selected rows of a doubly-stochastic
kernel.
-/
structure FractionalSelection (d : Nat) where
  k : Nat
  weight : Prim.Idx d → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  weight_le_one : ∀ j, weight j ≤ 1
  weight_sum_eq_k : (∑ j : Prim.Idx d, weight j) = k

namespace FractionalSelection

variable {d : Nat} (F : FractionalSelection d)

/-- Weighted value selected by a fractional coordinate selection. -/
noncomputable def weightedSum (w : Prim.Idx d → ℝ) : ℝ :=
  ∑ j : Prim.Idx d, F.weight j * w j

/-- Fractional-selection weights have nonnegative total mass. -/
theorem k_nonneg_as_real : (0 : ℝ) ≤ F.k := by
  rw [← F.weight_sum_eq_k]
  exact Finset.sum_nonneg (fun j _hj => F.weight_nonneg j)

/-- A fractional selection cannot have total mass larger than the ambient dimension. -/
theorem k_le_dimension : F.k ≤ d := by
  have hsum_le :
      (∑ j : Prim.Idx d, F.weight j) ≤ ∑ _j : Prim.Idx d, (1 : ℝ) := by
    exact Finset.sum_le_sum (fun j _hj => F.weight_le_one j)
  have hreal : (F.k : ℝ) ≤ (d : ℝ) := by
    rw [← F.weight_sum_eq_k]
    simpa using hsum_le
  exact Nat.cast_le.mp hreal

/--
For any `k` coordinates, the total deficit `1 - weight` equals the mass placed
outside that coordinate block.

This is the mass-balance identity behind the fractional Ky Fan bounds.
-/
theorem deficit_eq_notMem_mass_of_card {S : Finset (Prim.Idx d)}
    (hS : S.card = F.k) :
    Finset.sum S (fun j => (1 : ℝ) - F.weight j) =
      Finset.sum (Finset.univ.filter (fun j : Prim.Idx d => j ∉ S)) F.weight := by
  have hones : Finset.sum S (fun _j : Prim.Idx d => (1 : ℝ)) = (F.k : ℝ) := by
    simp [hS]
  have hsplit :
      Finset.sum S F.weight +
        Finset.sum (Finset.univ.filter (fun j : Prim.Idx d => j ∉ S)) F.weight =
          (F.k : ℝ) := by
    have h :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun j : Prim.Idx d => j ∈ S) (f := F.weight)
    simpa [F.weight_sum_eq_k] using h
  calc
    Finset.sum S (fun j => (1 : ℝ) - F.weight j)
        = Finset.sum S (fun _j : Prim.Idx d => (1 : ℝ)) - Finset.sum S F.weight := by
            exact Finset.sum_sub_distrib
              (s := S) (f := fun _ : Prim.Idx d => (1 : ℝ)) (g := F.weight)
    _ = (F.k : ℝ) - Finset.sum S F.weight := by
            rw [hones]
    _ = Finset.sum (Finset.univ.filter (fun j : Prim.Idx d => j ∉ S)) F.weight := by
            linarith

/--
For the leading `k` coordinates, the total deficit `1 - weight` equals the
mass placed outside the leading block.
-/
theorem leading_deficit_eq_not_leading_mass :
    Finset.sum (leadingIndexSet d F.k) (fun j => (1 : ℝ) - F.weight j) =
      Finset.sum
        (Finset.univ.filter (fun j : Prim.Idx d => j ∉ leadingIndexSet d F.k)) F.weight := by
  exact F.deficit_eq_notMem_mass_of_card (leadingIndexSet_card F.k_le_dimension)

/--
For the trailing `k` coordinates, the total deficit `1 - weight` equals the
mass placed outside the trailing block.
-/
theorem trailing_deficit_eq_not_trailing_mass :
    Finset.sum (trailingIndexSet d F.k) (fun j => (1 : ℝ) - F.weight j) =
      Finset.sum
        (Finset.univ.filter (fun j : Prim.Idx d => j ∉ trailingIndexSet d F.k)) F.weight := by
  exact F.deficit_eq_notMem_mass_of_card (trailingIndexSet_card F.k_le_dimension)

end FractionalSelection

end Prim.LinearAlgebra
