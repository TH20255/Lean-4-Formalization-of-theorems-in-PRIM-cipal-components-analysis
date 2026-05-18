import Prim.Proofs.RotationOptimality.CovarianceLanding.CardinalProfile.Data
import Prim.Proofs.RotationOptimality.CovarianceLanding.CovarianceTarget
import Prim.Proofs.RotationOptimality.CovarianceLanding.CardinalDiagonalCovariance
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Data

/-!
Covariance/profile constructors from compact centered-product moment targets.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

namespace CardinalRotatedPeelCenteredMomentTarget

variable (T : CardinalRotatedPeelCenteredMomentTarget d)

/--
Build the full diagonal-covariance witness encoded by the compact named
centered-moment target.

This packages the target's diagonal formula and upper-triangular vanishing as a
single `DiagonalPreservedCovariance` object, which can then be reused for
determinant, Frobenius-square, or matrix-level arguments.
-/
noncomputable def diagonalCovariance
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = T.k) :
    Prim.Probability.DiagonalPreservedCovariance d T.diagonal.core.μ
      (rotatedPeelEvent T.diagonal U I) T.diagonal.core.Y :=
  Prim.Probability.diagonalPreservedCovarianceOfCenteredProductMomentAndUpperCenteredProductMoment
    d T.diagonal.core.μ (rotatedPeelEvent T.diagonal U I) T.diagonal.core.Y
    (orthogonalMatrixDiagonalTraceDiagVal T.diagonal U I)
    (T.diag_formula U I hI) (T.upper_formula U I hI)

/-- The compact moment target constructs the cardinality-local covariance profile. -/
noncomputable def toCovarianceProfile :
    CardinalRotatedPeelCovarianceProfile d :=
  {
    diagonal := T.diagonal
    k := T.k
    coeff_nonpos := T.coeff_nonpos
    diagonal_entries := by
      intro U I hI
      exact Prim.Probability.PreservedCovarianceDiagonalEntries.ofCenteredProductMomentDiag
        (d := d) (μ := T.diagonal.core.μ)
        (s := rotatedPeelEvent T.diagonal U I) (X := T.diagonal.core.Y)
        (diagVal := orthogonalMatrixDiagonalTraceDiagVal T.diagonal U I)
        (hdiag := T.diag_formula U I hI)
    diagonal_entries_eq := by
      intro U I hI j
      simp [Prim.Probability.PreservedCovarianceDiagonalEntries.ofCenteredProductMomentDiag,
        Prim.Probability.PreservedCovarianceDiagonalEntries.ofDiagEq]
  }

/-- The compact moment target also constructs the stronger cardinal diagonal-covariance profile. -/
noncomputable def toDiagonalCovarianceProfile :
    CardinalRotatedPeelDiagonalCovarianceProfile d :=
  cardinalRotatedPeelDiagonalCovarianceProfileOfDiagonalCovariance
    T.diagonal T.k T.coeff_nonpos
    (fun U I hI => T.diagonalCovariance U hI)
    (fun U I hI j => by
      have hdiag :
          rotatedPeelPreservedCov T.diagonal U I j j =
            (T.diagonalCovariance U hI).diagVal j := by
        simpa [rotatedPeelPreservedCov] using (T.diagonalCovariance U hI).diag_eq j
      rw [← T.diag_formula U I hI j]
      exact hdiag.symm)

/-- The compact moment target recovers the explicit covariance target matrix. -/
theorem cov_eq_covTarget
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = T.k) :
    rotatedPeelPreservedCov T.diagonal U I =
      orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I :=
  rotatedPeelPreservedCov_eq_covTarget_of_cardinal_diag_and_upperOffDiag
    T.diagonal T.k
    (fun U I hI j => by
      rw [rotatedPeelPreservedCov_eq_centeredProductMoment]
      exact T.diag_formula U I hI j)
    (fun U I hI {j l} hjl => by
      rw [rotatedPeelPreservedCov_eq_centeredProductMoment]
      exact T.upper_formula U I hI (j := j) (l := l) hjl)
    U I hI

/-- The diagonal-covariance witness from the compact target recovers the explicit covariance target. -/
theorem diagonalCovariance_matrix_eq_covTarget
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = T.k) :
    rotatedPeelPreservedCov T.diagonal U I =
      orthogonalMatrixDiagonalTraceCovTarget T.diagonal U I := by
  simpa [rotatedPeelPreservedCov, orthogonalMatrixDiagonalTraceCovTarget] using
    (T.diagonalCovariance U hI).matrix_eq_diagonal

/-- The compact target's upper-triangular formula gives every off-diagonal moment. -/
theorem offDiag_formula
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = T.k)
    {j l : Prim.Idx d} (hjl : j ≠ l) :
    rotatedPeelCenteredProductMoment T.diagonal U I j l = 0 :=
  rotatedPeelCenteredProductMoment_offDiag_eq_zero_of_lt
    T.diagonal U I
    (fun {j l} hjl => T.upper_formula U I hI (j := j) (l := l) hjl)
    hjl

end CardinalRotatedPeelCenteredMomentTarget

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
