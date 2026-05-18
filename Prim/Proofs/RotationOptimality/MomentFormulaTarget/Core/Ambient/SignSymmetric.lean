import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Ambient.Symmetry

/-!
Sign-symmetric weighted factored source packages for ambient angular formulas.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Sign-symmetric version of the unified weighted factored source target.

This replaces the zero-mean integral hypothesis by the symmetry statement one
expects from the angular distribution: for each conditioned coordinate
integrand `R * O_j`, a measure-preserving sign flip turns it into its negative.
The generic probability lemma then derives the required mean-zero formula.
-/
structure CardinalPrincipalRepVectorSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  mean_symmetry :
    ∀ U I, I.card = k →
      ∀ j, rotatedRepPeelROSignSymmetry diagonal U I j
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

namespace CardinalPrincipalRepVectorSignSymmetricWeightedFactoredRawSecondMomentDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F : CardinalPrincipalRepVectorSignSymmetricWeightedFactoredRawSecondMomentDiagFormula diagonal k)

/-- Sign-symmetric source formulas give the unified weighted source target. -/
def toWeightedFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula diagonal k where
  mean_zero := by
    intro U I hI j
    rcases F.mean_symmetry U I hI j with ⟨τ, hτ, hodd⟩
    exact
      Prim.Probability.integral_eq_zero_of_measurePreserving_comp_eq_neg
        (Prim.Probability.condOn diagonal.core.μ
          (rotatedRepPeelEvent diagonal U I))
        τ hτ (fun ω => diagonal.core.R ω * diagonal.core.O ω j) hodd
  second_moment := F.second_moment

/-- Sign-symmetric source formulas give the factored source target. -/
def toFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula diagonal k :=
  F.toWeightedFactoredRawSecondMomentDiagFormula.toFactoredRawSecondMomentDiagFormula

/-- Sign-symmetric source formulas give the raw second-moment target. -/
def toRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorRawSecondMomentDiagFormula diagonal k :=
  F.toFactoredRawSecondMomentDiagFormula.toRawSecondMomentDiagFormula

/-- Sign-symmetric source formulas give the explicit-principal-vector centered formula. -/
def toCenteredMomentDiagFormula :
    CardinalPrincipalRepVectorCenteredMomentDiagFormula diagonal k :=
  F.toRawSecondMomentDiagFormula.toCenteredMomentDiagFormula

/-- Sign-symmetric source formulas also enter the standard rotated-peeling diagonal block. -/
def toRotatedPeelCenteredMomentDiagFormula :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k :=
  F.toRawSecondMomentDiagFormula.toRotatedPeelCenteredMomentDiagFormula

end CardinalPrincipalRepVectorSignSymmetricWeightedFactoredRawSecondMomentDiagFormula

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
