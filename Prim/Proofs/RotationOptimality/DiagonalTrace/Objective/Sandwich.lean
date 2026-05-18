import Prim.Proofs.RotationOptimality.DiagonalTrace.Objective.Basic

/-!
Same-cardinality leading/trailing bounds for the concrete orthogonal
diagonal-trace objective.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
For the concrete diagonal-covariance objective, the canonical trailing set
maximizes preserved trace among same-cardinality orthogonal rotations.
-/
theorem orthogonalMatrixDiagonalTraceObjective_canonicalTrailingSet_preserves_most
    (P : KDimensionalDiagonalProfile d) (k : Nat) (hcoeff : P.b - P.a ≤ 0)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    orthogonalMatrixDiagonalTraceObjective P U I ≤
      P.core.preservedTraceOn P.q (trailingIndexSet d k) := by
  calc
    orthogonalMatrixDiagonalTraceObjective P U I ≤
        orthogonalMatrixDiagonalTraceObjective P
          (OrthogonalMatrixRotation.identity d) (trailingIndexSet d k) := by
          exact CardinalRotationOptimalityProfile.orthogonalMatrix_canonicalTrailing_preserves_most
            P.core.profile.eigenvalue P.core.profile.lambda_antitone k
            (orthogonalMatrixDiagonalTraceObjective P)
            (P.a * (∑ j : Prim.Idx d, P.core.profile.eigenvalue j))
            (P.b - P.a) hcoeff (by intro U I; rfl) U hI
    _ = P.core.preservedTraceOn P.q (trailingIndexSet d k) := by
          exact orthogonalMatrixDiagonalTraceObjective_identity_eq_preservedTraceOn
            P (trailingIndexSet d k)

/--
For the concrete diagonal-covariance objective, the canonical leading set
minimizes preserved trace among same-cardinality orthogonal rotations.
-/
theorem orthogonalMatrixDiagonalTraceObjective_canonicalLeadingSet_preserves_least
    (P : KDimensionalDiagonalProfile d) (k : Nat) (hcoeff : P.b - P.a ≤ 0)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    P.core.preservedTraceOn P.q (leadingIndexSet d k) ≤
      orthogonalMatrixDiagonalTraceObjective P U I := by
  calc
    P.core.preservedTraceOn P.q (leadingIndexSet d k) =
        orthogonalMatrixDiagonalTraceObjective P
          (OrthogonalMatrixRotation.identity d) (leadingIndexSet d k) := by
          symm
          exact orthogonalMatrixDiagonalTraceObjective_identity_eq_preservedTraceOn
            P (leadingIndexSet d k)
    _ ≤ orthogonalMatrixDiagonalTraceObjective P U I := by
          exact CardinalRotationOptimalityProfile.orthogonalMatrix_canonicalLeading_preserves_least
            P.core.profile.eigenvalue P.core.profile.lambda_antitone k
            (orthogonalMatrixDiagonalTraceObjective P)
            (P.a * (∑ j : Prim.Idx d, P.core.profile.eigenvalue j))
            (P.b - P.a) hcoeff (by intro U I; rfl) U hI

/-- Sandwich form for the concrete diagonal-covariance trace objective. -/
theorem orthogonalMatrixDiagonalTraceObjective_sandwich
    (P : KDimensionalDiagonalProfile d) (k : Nat) (hcoeff : P.b - P.a ≤ 0)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    P.core.preservedTraceOn P.q (leadingIndexSet d k) ≤
        orthogonalMatrixDiagonalTraceObjective P U I ∧
      orthogonalMatrixDiagonalTraceObjective P U I ≤
        P.core.preservedTraceOn P.q (trailingIndexSet d k) :=
  ⟨orthogonalMatrixDiagonalTraceObjective_canonicalLeadingSet_preserves_least
      P k hcoeff U hI,
    orthogonalMatrixDiagonalTraceObjective_canonicalTrailingSet_preserves_most
      P k hcoeff U hI⟩

end CardinalOrderedValueKDimensionalRotationConExpProfile

end Prim.Proofs
