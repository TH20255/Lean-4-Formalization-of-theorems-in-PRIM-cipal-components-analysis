import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Diagonal.Factored

/-!
Weighted factored principal-vector diagonal source package.

This owner is the narrow public source shape needed by ambient-angular
stochastic representation packages.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}
/--
Unified weighted factored source target.

Compared with
`CardinalPrincipalRepVectorWeightedSplitFactoredRawSecondMomentDiagFormula`,
this asks analytic work for one second-moment formula with an explicit
membership `if`, rather than two separate `j ∈ I` / `j ∉ I` fields.  This is
closer to the conditional-expectation shape one expects before doing a final
case split.
-/
structure CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula
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
          diagonal.a * diagonal.core.profile.eigenvalue j +
            if j ∈ I then
              (diagonal.b - diagonal.a) *
                (∑ l : Prim.Idx d,
                  (U.matrix j l) ^ (2 : Nat) *
                    diagonal.core.profile.eigenvalue l)
            else 0

namespace CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula diagonal k)

/--
The unified weighted source formula is exactly the diagonal value used by the
orthogonal trace objective.
-/
theorem second_moment_eq_diagVal
    (F : CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula diagonal k)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) (hI : I.card = k)
    (j : Prim.Idx d) :
    diagonal.core.profile.eigenvalue j *
        (∫ ω,
          (diagonal.core.R ω) ^ (2 : Nat) *
            (diagonal.core.O ω j) ^ (2 : Nat) ∂
          Prim.Probability.condOn diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)) =
      orthogonalMatrixDiagonalTraceDiagVal diagonal U I j := by
  by_cases hj : j ∈ I
  · simpa [orthogonalMatrixDiagonalTraceDiagVal, hj, diagonal_conjugate_diagonal_apply] using
      F.second_moment U I hI j
  · simpa [orthogonalMatrixDiagonalTraceDiagVal, hj] using
      F.second_moment U I hI j

/-- The unified weighted formula gives the unified matrix factored target. -/
def toFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula diagonal k where
  mean_zero := F.mean_zero
  second_moment := by
    intro U I hI j
    exact second_moment_eq_diagVal F U I hI j

/-- The unified weighted formula gives the raw second-moment target. -/
def toRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorRawSecondMomentDiagFormula diagonal k :=
  F.toFactoredRawSecondMomentDiagFormula.toRawSecondMomentDiagFormula

/-- The unified weighted formula gives the explicit-principal-vector centered formula. -/
def toCenteredMomentDiagFormula :
    CardinalPrincipalRepVectorCenteredMomentDiagFormula diagonal k :=
  F.toRawSecondMomentDiagFormula.toCenteredMomentDiagFormula

/-- The unified weighted formula also enters the standard rotated-peeling diagonal block. -/
def toRotatedPeelCenteredMomentDiagFormula :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k :=
  F.toRawSecondMomentDiagFormula.toRotatedPeelCenteredMomentDiagFormula

end CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
