import Prim.Proofs.RotationOptimality.Basic.Abstract.Orthogonal
import Prim.Proofs.KDimensional.Diagonal.Formulas.Affine

/-!
Basic concrete orthogonal diagonal-trace objective.

This file contains only the objective definition and the identity-rotation
bridge back to the principal-basis preserved trace.  Matrix diagonal entries
and optimization bounds live in sibling files.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Concrete diagonal-covariance trace objective for orthogonal rotations.

If a diagonal covariance calculation has coefficients `a` off the peeled
coordinates and `b` on the peeled coordinates, then after an orthogonal change
of coordinates the selected-eigenvalue contribution is the selected diagonal
sum of `U * diagonal λ * Uᵀ`.
-/
noncomputable def orthogonalMatrixDiagonalTraceObjective
    (P : KDimensionalDiagonalProfile d) :
    OrthogonalMatrixRotation d → Finset (Prim.Idx d) → ℝ :=
  fun U I =>
    P.a * (∑ j : Prim.Idx d, P.core.profile.eigenvalue j) +
      (P.b - P.a) *
        OrthogonalMatrixRotation.selectedDiagonalSum
          P.core.profile.eigenvalue U I

/-- Definitional expansion of the concrete diagonal-covariance trace objective. -/
theorem orthogonalMatrixDiagonalTraceObjective_eq
    (P : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    orthogonalMatrixDiagonalTraceObjective P U I =
      P.a * (∑ j : Prim.Idx d, P.core.profile.eigenvalue j) +
        (P.b - P.a) *
          OrthogonalMatrixRotation.selectedDiagonalSum
            P.core.profile.eigenvalue U I := by
  rfl

/--
At the identity rotation, the diagonal-covariance trace objective recovers the
principal-basis preserved trace.
-/
theorem orthogonalMatrixDiagonalTraceObjective_identity_eq_preservedTraceOn
    (P : KDimensionalDiagonalProfile d) (I : Finset (Prim.Idx d)) :
    orthogonalMatrixDiagonalTraceObjective P (OrthogonalMatrixRotation.identity d) I =
      P.core.preservedTraceOn P.q I := by
  rw [P.preservedTraceOn_eq_affine_eigenSum I]
  unfold orthogonalMatrixDiagonalTraceObjective eigenSum
  rw [OrthogonalMatrixRotation.identity_selectedDiagonalSum_eq]

end CardinalOrderedValueKDimensionalRotationConExpProfile

end Prim.Proofs
