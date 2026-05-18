import Prim.Proofs.RotationOptimality.Basic.Abstract.Cardinal
import Prim.LinearAlgebra.DoublyStochastic.Orthogonal.Rotation

namespace Prim.Proofs

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

namespace CardinalRotationOptimalityProfile

variable {d : Nat}

/--
Package a trace formula over concrete orthogonal diagonal conjugations as a
cardinality-aware rotation optimality profile.
-/
noncomputable def ofOrthogonalMatrixDiagonalConjugate
    (w : Prim.Idx d → ℝ) (hanti : Antitone w) (k : Nat)
    (preservedTrace : OrthogonalMatrixRotation d → Finset (Prim.Idx d) → ℝ)
    (offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ U I,
        preservedTrace U I =
          offset + coeff * OrthogonalMatrixRotation.selectedDiagonalSum w U I) :
    CardinalRotationOptimalityProfile (OrthogonalMatrixRotation d) d where
  bounds := OrthogonalMatrixRotation.toCardinalOrderedValueSelectionBounds w hanti k
  preservedTrace := preservedTrace
  offset := offset
  coeff := coeff
  coeff_nonpos := hcoeff
  trace_formula := htrace

/--
Concrete orthogonal-matrix version: for same-cardinality selected sets,
the identity rotation with the canonical trailing set maximizes preserved trace.
-/
theorem orthogonalMatrix_canonicalTrailing_preserves_most
    (w : Prim.Idx d → ℝ) (hanti : Antitone w) (k : Nat)
    (preservedTrace : OrthogonalMatrixRotation d → Finset (Prim.Idx d) → ℝ)
    (offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ U I,
        preservedTrace U I =
          offset + coeff * OrthogonalMatrixRotation.selectedDiagonalSum w U I)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    preservedTrace U I ≤
      preservedTrace (OrthogonalMatrixRotation.identity d) (trailingIndexSet d k) := by
  exact (ofOrthogonalMatrixDiagonalConjugate
    w hanti k preservedTrace offset coeff hcoeff htrace).canonicalTrailing_preserves_most U hI

/--
Concrete orthogonal-matrix version: for same-cardinality selected sets,
the identity rotation with the canonical leading set minimizes preserved trace.
-/
theorem orthogonalMatrix_canonicalLeading_preserves_least
    (w : Prim.Idx d → ℝ) (hanti : Antitone w) (k : Nat)
    (preservedTrace : OrthogonalMatrixRotation d → Finset (Prim.Idx d) → ℝ)
    (offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ U I,
        preservedTrace U I =
          offset + coeff * OrthogonalMatrixRotation.selectedDiagonalSum w U I)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    preservedTrace (OrthogonalMatrixRotation.identity d) (leadingIndexSet d k) ≤
      preservedTrace U I := by
  exact (ofOrthogonalMatrixDiagonalConjugate
    w hanti k preservedTrace offset coeff hcoeff htrace).canonicalLeading_preserves_least U hI

end CardinalRotationOptimalityProfile

end Prim.Proofs
