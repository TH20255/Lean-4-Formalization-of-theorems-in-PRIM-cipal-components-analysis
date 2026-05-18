import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Diagonal.Basic
import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Covariance.OffDiag
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Integral

/-!
Separated centered-moment and centered-integral diagonal/upper/off-diagonal formula blocks.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/-- The upper-triangular part of the cardinality-local named moment target. -/
structure CardinalRotatedPeelCenteredMomentUpperFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  formula :
    ∀ U I, I.card = k →
      ∀ {j l : Prim.Idx d}, j < l →
        rotatedPeelCenteredProductMoment diagonal U I j l = 0

/-- The full off-diagonal part of the cardinality-local named moment target. -/
structure CardinalRotatedPeelCenteredMomentOffDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  formula :
    ∀ U I, I.card = k →
      ∀ {j l : Prim.Idx d}, j ≠ l →
        rotatedPeelCenteredProductMoment diagonal U I j l = 0

namespace CardinalRotatedPeelCenteredMomentUpperFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalRotatedPeelCenteredMomentUpperFormula diagonal k)

/-- Symmetry promotes an upper-triangular named moment formula to full off-diagonal form. -/
def toOffDiagFormula :
    CardinalRotatedPeelCenteredMomentOffDiagFormula diagonal k where
  formula := fun U I hI {j l} hjl =>
    rotatedPeelCenteredProductMoment_offDiag_eq_zero_of_lt diagonal U I
      (fun {j l} hjl => F.formula U I hI (j := j) (l := l) hjl)
      (j := j) (l := l) hjl

end CardinalRotatedPeelCenteredMomentUpperFormula

namespace CardinalRotatedPeelCenteredMomentOffDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalRotatedPeelCenteredMomentOffDiagFormula diagonal k)

/-- A full off-diagonal formula provides the upper-triangular formula block. -/
def toUpperFormula :
    CardinalRotatedPeelCenteredMomentUpperFormula diagonal k where
  formula := fun U I hI {j l} hjl =>
    F.formula U I hI (j := j) (l := l) (ne_of_lt hjl)

end CardinalRotatedPeelCenteredMomentOffDiagFormula

/-- The diagonal part of the cardinality-local raw centered-integral target. -/
structure CardinalRotatedPeelCenteredIntegralDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  formula :
    ∀ U I, I.card = k →
      ∀ j,
        rotatedPeelCenteredIntegral diagonal U I j j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j

/-- The upper-triangular part of the raw centered-integral target. -/
structure CardinalRotatedPeelCenteredIntegralUpperFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  formula :
    ∀ U I, I.card = k →
      ∀ {j l : Prim.Idx d}, j < l →
        rotatedPeelCenteredIntegral diagonal U I j l = 0

/-- The full off-diagonal part of the raw centered-integral target. -/
structure CardinalRotatedPeelCenteredIntegralOffDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  formula :
    ∀ U I, I.card = k →
      ∀ {j l : Prim.Idx d}, j ≠ l →
        rotatedPeelCenteredIntegral diagonal U I j l = 0

namespace CardinalRotatedPeelCenteredIntegralUpperFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalRotatedPeelCenteredIntegralUpperFormula diagonal k)

/-- Symmetry promotes an upper-triangular raw integral formula to full off-diagonal form. -/
def toOffDiagFormula :
    CardinalRotatedPeelCenteredIntegralOffDiagFormula diagonal k where
  formula := by
    intro U I hI j l hjl
    rw [rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact rotatedPeelCenteredProductMoment_offDiag_eq_zero_of_lt diagonal U I
      (fun {j l} hjl => by
        rw [← rotatedPeelCenteredIntegral_eq_centeredProductMoment]
        exact F.formula U I hI (j := j) (l := l) hjl)
      hjl

end CardinalRotatedPeelCenteredIntegralUpperFormula

namespace CardinalRotatedPeelCenteredIntegralOffDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalRotatedPeelCenteredIntegralOffDiagFormula diagonal k)

/-- A full off-diagonal integral formula provides the upper-triangular block. -/
def toUpperFormula :
    CardinalRotatedPeelCenteredIntegralUpperFormula diagonal k where
  formula := fun U I hI {j l} hjl =>
    F.formula U I hI (j := j) (l := l) (ne_of_lt hjl)

end CardinalRotatedPeelCenteredIntegralOffDiagFormula

namespace CardinalRotatedPeelCenteredIntegralDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalRotatedPeelCenteredIntegralDiagFormula diagonal k)

/-- Raw diagonal integral formulas are named centered-moment diagonal formulas. -/
def toCenteredMomentDiagFormula :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k where
  formula := by
    intro U I hI j
    rw [← rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact F.formula U I hI j

end CardinalRotatedPeelCenteredIntegralDiagFormula

namespace CardinalRotatedPeelCenteredIntegralUpperFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalRotatedPeelCenteredIntegralUpperFormula diagonal k)

/-- Raw upper-triangular integral formulas are named centered-moment formulas. -/
def toCenteredMomentUpperFormula :
    CardinalRotatedPeelCenteredMomentUpperFormula diagonal k where
  formula := by
    intro U I hI j l hjl
    rw [← rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact F.formula U I hI hjl

end CardinalRotatedPeelCenteredIntegralUpperFormula

namespace CardinalRotatedPeelCenteredIntegralOffDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalRotatedPeelCenteredIntegralOffDiagFormula diagonal k)

/-- Raw off-diagonal integral formulas are named centered-moment formulas. -/
def toCenteredMomentOffDiagFormula :
    CardinalRotatedPeelCenteredMomentOffDiagFormula diagonal k where
  formula := by
    intro U I hI j l hjl
    rw [← rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact F.formula U I hI hjl

end CardinalRotatedPeelCenteredIntegralOffDiagFormula

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
