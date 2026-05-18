import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Covariance.Basic

/-!
Diagonal principal-representation formula packages for the rotated-peeling moment target.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
The diagonal part of the cardinality-local named centered-moment target.

This block lets the remaining analytic work prove diagonal centered moments
independently from the off-diagonal vanishing calculation.
-/
structure CardinalRotatedPeelCenteredMomentDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  formula :
    ∀ U I, I.card = k →
      ∀ j,
        rotatedPeelCenteredProductMoment diagonal U I j j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j

/--
The diagonal part of the cardinality-local centered-moment target, stated
directly for the explicit principal stochastic-representation vector.

This is the narrowest current post-representation analytic target: prove this
object from the stochastic representation, and the existing route layer can
convert it to the standard rotated-peeling diagonal block.
-/
structure CardinalPrincipalRepVectorCenteredMomentDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  formula :
    ∀ U I, I.card = k →
      ∀ j,
        Prim.Probability.preservedCenteredProductMoment d diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)
            (principalRepVector diagonal.core) j j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j

namespace CardinalPrincipalRepVectorCenteredMomentDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalPrincipalRepVectorCenteredMomentDiagFormula diagonal k)

/--
An explicit-principal-vector diagonal formula is the standard named diagonal
centered-moment formula block, after the a.e. representation transport.
-/
def toCenteredMomentDiagFormula :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k where
  formula := by
    intro U I hI j
    calc
      rotatedPeelCenteredProductMoment diagonal U I j j
          = rotatedRepPeelCenteredProductMoment diagonal U I j j := by
              rw [rotatedPeelCenteredProductMoment_eq_rep]
      _ = Prim.Probability.preservedCenteredProductMoment d diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)
            (principalRepVector diagonal.core) j j := by
              rw [rotatedRepPeelCenteredProductMoment_eq_principalRepVector]
      _ = orthogonalMatrixDiagonalTraceDiagVal diagonal U I j := F.formula U I hI j

end CardinalPrincipalRepVectorCenteredMomentDiagFormula

/--
Source-facing version of the explicit-principal-vector diagonal formula.

Many stochastic-representation calculations naturally first prove that the
conditioned coordinate means vanish and then compute raw conditional second
moments.  This object records exactly that lower-level handoff; the generic
probability lemma turns it into the centered-product formula above.
-/
structure CardinalPrincipalRepVectorRawSecondMomentDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  mean_zero :
    ∀ U I, I.card = k →
      ∀ j,
        Prim.Probability.meanVec d
            (Prim.Probability.condOn diagonal.core.μ
              (rotatedRepPeelEvent diagonal U I))
            (principalRepVector diagonal.core) j = 0
  second_moment :
    ∀ U I, I.card = k →
      ∀ j,
        (∫ ω,
            principalRepVector diagonal.core ω j *
              principalRepVector diagonal.core ω j ∂
            Prim.Probability.condOn diagonal.core.μ
              (rotatedRepPeelEvent diagonal U I)) =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j

namespace CardinalPrincipalRepVectorRawSecondMomentDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalPrincipalRepVectorRawSecondMomentDiagFormula diagonal k)

/--
Zero conditioned means plus raw second moments give the explicit-principal-vector
centered-product diagonal formula.
-/
def toCenteredMomentDiagFormula :
    CardinalPrincipalRepVectorCenteredMomentDiagFormula diagonal k where
  formula := by
    intro U I hI j
    exact
      Prim.Probability.preservedCenteredProductMoment_diag_eq_of_mean_zero_and_integral
        d diagonal.core.μ (rotatedRepPeelEvent diagonal U I)
        (principalRepVector diagonal.core) j
        (F.mean_zero U I hI j)
        (F.second_moment U I hI j)

/--
Zero conditioned means plus raw second moments also enter the standard
rotated-peeling centered-moment diagonal block.
-/
def toRotatedPeelCenteredMomentDiagFormula :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k :=
  F.toCenteredMomentDiagFormula.toCenteredMomentDiagFormula

end CardinalPrincipalRepVectorRawSecondMomentDiagFormula

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
