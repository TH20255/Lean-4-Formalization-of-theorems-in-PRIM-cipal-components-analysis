import Prim.LinearAlgebra.MatrixMajorization.Base

namespace Prim.Proofs

open Prim.LinearAlgebra

/--
Cardinality-aware rotation optimality profile.

This is the theorem-facing version matched to Ky Fan / Schur-Horn statements:
the comparison only ranges over selected coordinate sets with the fixed
cardinality recorded in `bounds.k`.
-/
structure CardinalRotationOptimalityProfile (ρ : Type*) (d : Nat) where
  bounds : CardinalOrderedValueSelectionBounds ρ d
  preservedTrace : ρ → Finset (Prim.Idx d) → ℝ
  offset : ℝ
  coeff : ℝ
  coeff_nonpos : coeff ≤ 0
  trace_formula :
    ∀ r I, preservedTrace r I = offset + coeff * bounds.selectedSum r I

namespace CardinalRotationOptimalityProfile

variable {ρ : Type*} {d : Nat} (P : CardinalRotationOptimalityProfile ρ d)

/--
Among all admissible same-cardinality rotations and selections, the canonical
trailing set in the principal rotation preserves the most trace.
-/
theorem canonicalTrailing_preserves_most
    (r : ρ) {I : Finset (Prim.Idx d)} (hI : I.card = P.bounds.k) :
    P.preservedTrace r I ≤
      P.preservedTrace P.bounds.principalRotation (trailingIndexSet d P.bounds.k) := by
  rw [P.trace_formula r I,
    P.trace_formula P.bounds.principalRotation (trailingIndexSet d P.bounds.k)]
  have hBound :
      P.bounds.selectedSum P.bounds.principalRotation (trailingIndexSet d P.bounds.k) ≤
        P.bounds.selectedSum r I :=
    P.bounds.lower_bound r hI
  have hMul :
      P.coeff * P.bounds.selectedSum r I ≤
        P.coeff *
          P.bounds.selectedSum P.bounds.principalRotation (trailingIndexSet d P.bounds.k) :=
    mul_le_mul_of_nonpos_left hBound P.coeff_nonpos
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hMul P.offset

/--
Among all admissible same-cardinality rotations and selections, the canonical
leading set in the principal rotation preserves the least trace.
-/
theorem canonicalLeading_preserves_least
    (r : ρ) {I : Finset (Prim.Idx d)} (hI : I.card = P.bounds.k) :
    P.preservedTrace P.bounds.principalRotation (leadingIndexSet d P.bounds.k) ≤
      P.preservedTrace r I := by
  rw [P.trace_formula P.bounds.principalRotation (leadingIndexSet d P.bounds.k),
    P.trace_formula r I]
  have hBound :
      P.bounds.selectedSum r I ≤
        P.bounds.selectedSum P.bounds.principalRotation (leadingIndexSet d P.bounds.k) :=
    P.bounds.upper_bound r hI
  have hMul :
      P.coeff *
          P.bounds.selectedSum P.bounds.principalRotation (leadingIndexSet d P.bounds.k) ≤
        P.coeff * P.bounds.selectedSum r I :=
    mul_le_mul_of_nonpos_left hBound P.coeff_nonpos
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hMul P.offset

/-- Trace formula at the canonical trailing endpoint, expressed through a partial sum. -/
theorem trace_canonicalTrailing_eq :
    P.preservedTrace P.bounds.principalRotation (trailingIndexSet d P.bounds.k) =
      P.offset + P.coeff * trailingPartialSum d P.bounds.principalValue P.bounds.k := by
  rw [P.trace_formula, P.bounds.principal_selectedSum_eq_trailingPartialSum]

/-- Trace formula at the canonical leading endpoint, expressed through a partial sum. -/
theorem trace_canonicalLeading_eq :
    P.preservedTrace P.bounds.principalRotation (leadingIndexSet d P.bounds.k) =
      P.offset + P.coeff * leadingPartialSum d P.bounds.principalValue P.bounds.k := by
  rw [P.trace_formula, P.bounds.principal_selectedSum_eq_leadingPartialSum]

end CardinalRotationOptimalityProfile

end Prim.Proofs
