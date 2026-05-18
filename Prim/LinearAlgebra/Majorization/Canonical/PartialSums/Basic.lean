import Prim.LinearAlgebra.Majorization.Canonical.Sets.Basic

namespace Prim.LinearAlgebra

open scoped BigOperators

/-- Sum of a value profile over the canonical leading index set. -/
def leadingPartialSum (d : Nat) (w : Prim.Idx d → ℝ) (k : Nat) : ℝ :=
  Finset.sum (leadingIndexSet d k) w

/-- Sum of a value profile over the canonical trailing index set. -/
def trailingPartialSum (d : Nat) (w : Prim.Idx d → ℝ) (k : Nat) : ℝ :=
  Finset.sum (trailingIndexSet d k) w

theorem leadingPartialSum_eq_sum (d : Nat) (w : Prim.Idx d → ℝ) (k : Nat) :
    leadingPartialSum d w k = Finset.sum (leadingIndexSet d k) w := by
  rfl

theorem trailingPartialSum_eq_sum (d : Nat) (w : Prim.Idx d → ℝ) (k : Nat) :
    trailingPartialSum d w k = Finset.sum (trailingIndexSet d k) w := by
  rfl

end Prim.LinearAlgebra
