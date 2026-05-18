import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Blocks
import Prim.Proofs.RotationOptimality.CovarianceLanding.CardinalDiagonalCovariance

/-!
Basic formula extraction constructors for diagonal-covariance witnesses.

This public-leaning owner contains the diagonal and upper-triangular formula
blocks needed by the stochastic V0 path. Full off-diagonal extraction is kept
in `DiagonalCovariance.Formulas.OffDiag`.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Package a fixed-cardinality diagonal covariance witness into the named
diagonal centered-moment formula object.
-/
noncomputable def cardinalRotatedPeelCenteredMomentDiagFormulaOfDiagonalCovariance
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hdiagCov :
      forall U I, I.card = k ->
        Prim.Probability.DiagonalPreservedCovariance d diagonal.core.μ
          (rotatedPeelEvent diagonal U I) diagonal.core.Y)
    (hdiagVal :
      forall U I (hI : I.card = k) j,
        (hdiagCov U I hI).diagVal j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j) :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k where
  formula := by
    intro U I hI j
    have hdiag :
        rotatedPeelCenteredProductMoment diagonal U I j j =
          (hdiagCov U I hI).diagVal j := by
      simpa [rotatedPeelPreservedCov, rotatedPeelPreservedCov_eq_centeredProductMoment]
        using (hdiagCov U I hI).diag_eq j
    rw [hdiag, hdiagVal U I hI j]

/--
Package a fixed-cardinality diagonal covariance witness into the named
upper-triangular centered-moment formula object.
-/
noncomputable def cardinalRotatedPeelCenteredMomentUpperFormulaOfDiagonalCovariance
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hdiagCov :
      forall U I, I.card = k ->
        Prim.Probability.DiagonalPreservedCovariance d diagonal.core.μ
          (rotatedPeelEvent diagonal U I) diagonal.core.Y)
    (_hdiagVal :
      forall U I (hI : I.card = k) j,
        (hdiagCov U I hI).diagVal j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j) :
    CardinalRotatedPeelCenteredMomentUpperFormula diagonal k where
  formula := by
    intro U I hI j l hjl
    simpa [rotatedPeelPreservedCov, rotatedPeelPreservedCov_eq_centeredProductMoment]
      using (hdiagCov U I hI).offDiag_eq_zero (ne_of_lt hjl)

/--
Package a fixed-cardinality diagonal covariance witness into the raw diagonal
centered-integral formula object.
-/
noncomputable def cardinalRotatedPeelCenteredIntegralDiagFormulaOfDiagonalCovariance
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hdiagCov :
      forall U I, I.card = k ->
        Prim.Probability.DiagonalPreservedCovariance d diagonal.core.μ
          (rotatedPeelEvent diagonal U I) diagonal.core.Y)
    (hdiagVal :
      forall U I (hI : I.card = k) j,
        (hdiagCov U I hI).diagVal j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j) :
    CardinalRotatedPeelCenteredIntegralDiagFormula diagonal k where
  formula := by
    intro U I hI j
    rw [rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact
      (cardinalRotatedPeelCenteredMomentDiagFormulaOfDiagonalCovariance
        diagonal k hdiagCov hdiagVal).formula U I hI j

/--
Package a fixed-cardinality diagonal covariance witness into the raw
upper-triangular centered-integral formula object.
-/
noncomputable def cardinalRotatedPeelCenteredIntegralUpperFormulaOfDiagonalCovariance
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat)
    (hdiagCov :
      forall U I, I.card = k ->
        Prim.Probability.DiagonalPreservedCovariance d diagonal.core.μ
          (rotatedPeelEvent diagonal U I) diagonal.core.Y)
    (hdiagVal :
      forall U I (hI : I.card = k) j,
        (hdiagCov U I hI).diagVal j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j) :
    CardinalRotatedPeelCenteredIntegralUpperFormula diagonal k where
  formula := by
    intro U I hI j l hjl
    rw [rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact
      (cardinalRotatedPeelCenteredMomentUpperFormulaOfDiagonalCovariance
        diagonal k hdiagCov hdiagVal).formula U I hI hjl

/-- Extract the named diagonal centered-moment formula object from a stronger profile. -/
noncomputable def cardinalRotatedPeelCenteredMomentDiagFormulaOfDiagonalCovarianceProfile
    (P : CardinalRotatedPeelDiagonalCovarianceProfile d) :
    CardinalRotatedPeelCenteredMomentDiagFormula P.diagonal P.k :=
  cardinalRotatedPeelCenteredMomentDiagFormulaOfDiagonalCovariance
    P.diagonal P.k P.diagonal_covariance P.diagonal_covariance_eq

/-- Extract the named upper-triangular centered-moment formula object from a stronger profile. -/
noncomputable def cardinalRotatedPeelCenteredMomentUpperFormulaOfDiagonalCovarianceProfile
    (P : CardinalRotatedPeelDiagonalCovarianceProfile d) :
    CardinalRotatedPeelCenteredMomentUpperFormula P.diagonal P.k :=
  cardinalRotatedPeelCenteredMomentUpperFormulaOfDiagonalCovariance
    P.diagonal P.k P.diagonal_covariance P.diagonal_covariance_eq

/-- Extract the raw diagonal centered-integral formula object from a stronger profile. -/
noncomputable def cardinalRotatedPeelCenteredIntegralDiagFormulaOfDiagonalCovarianceProfile
    (P : CardinalRotatedPeelDiagonalCovarianceProfile d) :
    CardinalRotatedPeelCenteredIntegralDiagFormula P.diagonal P.k :=
  cardinalRotatedPeelCenteredIntegralDiagFormulaOfDiagonalCovariance
    P.diagonal P.k P.diagonal_covariance P.diagonal_covariance_eq

/-- Extract the raw upper-triangular centered-integral formula object from a stronger profile. -/
noncomputable def cardinalRotatedPeelCenteredIntegralUpperFormulaOfDiagonalCovarianceProfile
    (P : CardinalRotatedPeelDiagonalCovarianceProfile d) :
    CardinalRotatedPeelCenteredIntegralUpperFormula P.diagonal P.k :=
  cardinalRotatedPeelCenteredIntegralUpperFormulaOfDiagonalCovariance
    P.diagonal P.k P.diagonal_covariance P.diagonal_covariance_eq

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
