import Prim.LinearAlgebra.Majorization.Canonical.PartialSums.Basic

namespace Prim.LinearAlgebra

open scoped BigOperators

/--
Cardinality-aware ordered-value selection bounds.

The older `OrderedValueSelectionBounds` interface is convenient downstream, but
its bounds are intentionally very strong: they quantify over every `I`.  The
matrix Ky Fan / Schur-Horn bridge should instead apply to admissible selections
of a fixed cardinality `k`.  This structure records that mathematically sharper
interface.
-/
structure CardinalOrderedValueSelectionBounds (ρ : Type*) (d : Nat) where
  k : Nat
  principalValue : Prim.Idx d → ℝ
  principalValue_antitone : Antitone principalValue
  selectedSum : ρ → Finset (Prim.Idx d) → ℝ
  principalRotation : ρ
  principal_selectedSum_eq :
    ∀ I, selectedSum principalRotation I = Finset.sum I principalValue
  lower_bound :
    ∀ r {I : Finset (Prim.Idx d)}, I.card = k →
      selectedSum principalRotation (trailingIndexSet d k) ≤ selectedSum r I
  upper_bound :
    ∀ r {I : Finset (Prim.Idx d)}, I.card = k →
      selectedSum r I ≤ selectedSum principalRotation (leadingIndexSet d k)

namespace CardinalOrderedValueSelectionBounds

variable {ρ : Type*} {d : Nat} (B : CardinalOrderedValueSelectionBounds ρ d)

/-- Principal selected sum on the canonical trailing set as a trailing partial sum. -/
theorem principal_selectedSum_eq_trailingPartialSum :
    B.selectedSum B.principalRotation (trailingIndexSet d B.k) =
      trailingPartialSum d B.principalValue B.k := by
  rw [B.principal_selectedSum_eq]
  rfl

/-- Principal selected sum on the canonical leading set as a leading partial sum. -/
theorem principal_selectedSum_eq_leadingPartialSum :
    B.selectedSum B.principalRotation (leadingIndexSet d B.k) =
      leadingPartialSum d B.principalValue B.k := by
  rw [B.principal_selectedSum_eq]
  rfl

/-- The canonical trailing selection gives the lower endpoint for every admissible selection. -/
theorem trailingPartialSum_le_selectedSum
    (r : ρ) {I : Finset (Prim.Idx d)} (hI : I.card = B.k) :
    trailingPartialSum d B.principalValue B.k ≤ B.selectedSum r I := by
  rw [← B.principal_selectedSum_eq_trailingPartialSum]
  exact B.lower_bound r hI

/-- The canonical leading selection gives the upper endpoint for every admissible selection. -/
theorem selectedSum_le_leadingPartialSum
    (r : ρ) {I : Finset (Prim.Idx d)} (hI : I.card = B.k) :
    B.selectedSum r I ≤ leadingPartialSum d B.principalValue B.k := by
  rw [← B.principal_selectedSum_eq_leadingPartialSum]
  exact B.upper_bound r hI

/-- Cardinality-aware sandwich form of the ordered-value bounds. -/
theorem selectedSum_sandwich
    (r : ρ) {I : Finset (Prim.Idx d)} (hI : I.card = B.k) :
    trailingPartialSum d B.principalValue B.k ≤ B.selectedSum r I ∧
      B.selectedSum r I ≤ leadingPartialSum d B.principalValue B.k := by
  exact ⟨B.trailingPartialSum_le_selectedSum r hI,
    B.selectedSum_le_leadingPartialSum r hI⟩

end CardinalOrderedValueSelectionBounds

end Prim.LinearAlgebra
