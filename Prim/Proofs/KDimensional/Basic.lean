import Prim.Elliptical.Core.Base
import Prim.LinearAlgebra.Majorization.Canonical.PartialSums.Recurrence

namespace Prim.Proofs

open scoped BigOperators
open Prim.Elliptical

/--
Sum of the eigenvalues selected by a finite coordinate set.
-/
def eigenSum {d : Nat} (core : EllipticalCore d) (I : Finset (Prim.Idx d)) : ℝ :=
  Finset.sum I (fun i => core.profile.eigenvalue i)

/-- Sum of squared selected eigenvalues. -/
def eigenSqSum {d : Nat} (core : EllipticalCore d) (I : Finset (Prim.Idx d)) : ℝ :=
  Finset.sum I (fun i => (core.profile.eigenvalue i) ^ (2 : Nat))

/-- Selected eigenvalue sums are monotone under inclusion of index sets. -/
theorem eigenSum_le_of_subset {d : Nat} (core : EllipticalCore d)
    {I J : Finset (Prim.Idx d)} (hIJ : I ⊆ J) :
    eigenSum core I ≤ eigenSum core J := by
  dsimp [eigenSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hIJ
    (fun i hiJ hiI => core.profile.lambda_nonneg i)

/-- The selected squared-eigenvalue sum is nonnegative. -/
theorem eigenSqSum_nonneg {d : Nat} (core : EllipticalCore d) (I : Finset (Prim.Idx d)) :
    0 ≤ eigenSqSum core I := by
  dsimp [eigenSqSum]
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (core.profile.eigenvalue i))

/-- Selected squared-eigenvalue sums are monotone under inclusion of index sets. -/
theorem eigenSqSum_le_of_subset {d : Nat} (core : EllipticalCore d)
    {I J : Finset (Prim.Idx d)} (hIJ : I ⊆ J) :
    eigenSqSum core I ≤ eigenSqSum core J := by
  dsimp [eigenSqSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hIJ
    (fun i hiJ hiI => sq_nonneg (core.profile.eigenvalue i))

/-- Enlarging the canonical leading set adds the square of the next ordered eigenvalue. -/
theorem eigenSqSum_leadingIndexSet_succ {d k : Nat}
    (core : EllipticalCore d) (hk : k < d) :
    eigenSqSum core (Prim.LinearAlgebra.leadingIndexSet d (k + 1)) =
      eigenSqSum core (Prim.LinearAlgebra.leadingIndexSet d k) +
        (core.profile.eigenvalue (⟨k, hk⟩ : Prim.Idx d)) ^ (2 : Nat) := by
  simpa [eigenSqSum, Prim.LinearAlgebra.leadingPartialSum] using
    Prim.LinearAlgebra.leadingPartialSum_succ
      (fun i : Prim.Idx d => (core.profile.eigenvalue i) ^ (2 : Nat)) hk

/-- Enlarging the canonical trailing set adds the square of the next smallest eigenvalue. -/
theorem eigenSqSum_trailingIndexSet_succ {d k : Nat}
    (core : EllipticalCore d) (hk : k < d) :
    eigenSqSum core (Prim.LinearAlgebra.trailingIndexSet d (k + 1)) =
      eigenSqSum core (Prim.LinearAlgebra.trailingIndexSet d k) +
        (core.profile.eigenvalue (⟨d - (k + 1), by omega⟩ : Prim.Idx d)) ^ (2 : Nat) := by
  simpa [eigenSqSum, Prim.LinearAlgebra.trailingPartialSum, Nat.add_comm] using
    Prim.LinearAlgebra.trailingPartialSum_succ
      (fun i : Prim.Idx d => (core.profile.eigenvalue i) ^ (2 : Nat)) hk

/-- Difference form of the leading squared-eigenvalue recursion. -/
theorem eigenSqSum_leadingIndexSet_succ_sub {d k : Nat}
    (core : EllipticalCore d) (hk : k < d) :
    eigenSqSum core (Prim.LinearAlgebra.leadingIndexSet d (k + 1)) -
      eigenSqSum core (Prim.LinearAlgebra.leadingIndexSet d k) =
        (core.profile.eigenvalue (⟨k, hk⟩ : Prim.Idx d)) ^ (2 : Nat) := by
  rw [eigenSqSum_leadingIndexSet_succ core hk]
  ring

/-- Difference form of the trailing squared-eigenvalue recursion. -/
theorem eigenSqSum_trailingIndexSet_succ_sub {d k : Nat}
    (core : EllipticalCore d) (hk : k < d) :
    eigenSqSum core (Prim.LinearAlgebra.trailingIndexSet d (k + 1)) -
      eigenSqSum core (Prim.LinearAlgebra.trailingIndexSet d k) =
        (core.profile.eigenvalue (⟨d - (k + 1), by omega⟩ : Prim.Idx d)) ^ (2 : Nat) := by
  rw [eigenSqSum_trailingIndexSet_succ core hk]
  ring

/-- Ordered nonnegative eigenvalues remain ordered after squaring. -/
theorem eigenvalue_sq_antitone {d : Nat} (core : EllipticalCore d)
    {i j : Prim.Idx d} (hij : (i : Nat) ≤ (j : Nat)) :
    (core.profile.eigenvalue j) ^ (2 : Nat) ≤
      (core.profile.eigenvalue i) ^ (2 : Nat) := by
  have hle : i ≤ j := by
    simpa using hij
  have hle_eigen : core.profile.eigenvalue j ≤ core.profile.eigenvalue i :=
    core.profile.lambda_antitone hle
  have hi : 0 ≤ core.profile.eigenvalue i := core.profile.lambda_nonneg i
  have hj : 0 ≤ core.profile.eigenvalue j := core.profile.lambda_nonneg j
  nlinarith

end Prim.Proofs
