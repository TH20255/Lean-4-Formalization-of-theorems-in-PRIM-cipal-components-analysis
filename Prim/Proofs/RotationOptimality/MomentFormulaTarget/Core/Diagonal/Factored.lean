import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Diagonal.Basic
import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Representation.MomentIntegrals

/-!
Factored principal-vector diagonal source package.

This owner keeps the direct factored-to-raw/centered/rotated path used by the
public ambient-angular source, without importing expanded, scaled, or split
historical source variants.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}
/--
Source-facing factored version of the explicit-principal-vector raw
second-moment target.

This is the lightest current source target for the diagonal trace mainline:
the eigenvalue factor has been moved outside the conditional integral, and the
remaining integrand is `R^2 * O_j^2`.
-/
structure CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  mean_zero :
    ∀ U I, I.card = k →
      ∀ j,
        (∫ ω,
            diagonal.core.R ω * diagonal.core.O ω j ∂
            Prim.Probability.condOn diagonal.core.μ
              (rotatedRepPeelEvent diagonal U I)) = 0
  second_moment :
    ∀ U I, I.card = k →
      ∀ j,
        diagonal.core.profile.eigenvalue j *
            (∫ ω,
              (diagonal.core.R ω) ^ (2 : Nat) *
                (diagonal.core.O ω j) ^ (2 : Nat) ∂
              Prim.Probability.condOn diagonal.core.μ
                (rotatedRepPeelEvent diagonal U I)) =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j

namespace CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula diagonal k)

/-- Factored source formulas give the raw second-moment target. -/
def toRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorRawSecondMomentDiagFormula diagonal k where
  mean_zero := by
    intro U I hI j
    rw [meanVec_principalRepVector_eq_sqrt_mul_integral_RO_condOn_rotatedRepPeelEvent]
    rw [F.mean_zero U I hI j, mul_zero]
  second_moment := by
    intro U I hI j
    rw [principalRepVector_sq_integral_eq_weighted_RO_sq_condOn_rotatedRepPeelEvent]
    exact F.second_moment U I hI j

/-- Factored source formulas give the explicit-principal-vector centered formula. -/
def toCenteredMomentDiagFormula :
    CardinalPrincipalRepVectorCenteredMomentDiagFormula diagonal k :=
  F.toRawSecondMomentDiagFormula.toCenteredMomentDiagFormula

/-- Factored source formulas also enter the standard rotated-peeling diagonal block. -/
def toRotatedPeelCenteredMomentDiagFormula :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k :=
  F.toRawSecondMomentDiagFormula.toRotatedPeelCenteredMomentDiagFormula

end CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
