import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Ambient.SignSymmetric

/-!
Ambient sign-symmetric weighted factored source packages.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Ambient sign-symmetric version of the unified weighted factored source target.

This is one step closer to the analytic spherical proof than
`CardinalPrincipalRepVectorSignSymmetricWeightedFactoredRawSecondMomentDiagFormula`:
the zero-mean source is stated as an ambient measure-preserving sign flip plus
a.e. invariance of the rotated representation-coordinate event.
-/
structure CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  mean_ambient_symmetry :
    ∀ U I, I.card = k →
      ∀ j, rotatedRepPeelROAmbientSignSymmetry diagonal U I j
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

namespace CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F :
  CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    diagonal k)

/-- Ambient sign-symmetric formulas give the conditioned sign-symmetric source. -/
def toSignSymmetricWeightedFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
      diagonal k where
  mean_symmetry := by
    intro U I hI j
    exact rotatedRepPeelROSignSymmetry_of_ambientSymmetry
      diagonal U I j (F.mean_ambient_symmetry U I hI j)
  second_moment := F.second_moment

/-- Ambient sign-symmetric formulas give the unified weighted source target. -/
def toWeightedFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula diagonal k :=
  CardinalPrincipalRepVectorSignSymmetricWeightedFactoredRawSecondMomentDiagFormula.toWeightedFactoredRawSecondMomentDiagFormula
    (CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula.toSignSymmetricWeightedFactoredRawSecondMomentDiagFormula F)

/-- Ambient sign-symmetric formulas give the factored source target. -/
def toFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula diagonal k :=
  CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula.toFactoredRawSecondMomentDiagFormula
    (CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula.toWeightedFactoredRawSecondMomentDiagFormula F)

/-- Ambient sign-symmetric formulas give the raw second-moment target. -/
def toRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorRawSecondMomentDiagFormula diagonal k :=
  CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula.toRawSecondMomentDiagFormula
    (CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula.toFactoredRawSecondMomentDiagFormula F)

/-- Ambient sign-symmetric formulas give the explicit-principal-vector centered formula. -/
def toCenteredMomentDiagFormula :
    CardinalPrincipalRepVectorCenteredMomentDiagFormula diagonal k :=
  CardinalPrincipalRepVectorRawSecondMomentDiagFormula.toCenteredMomentDiagFormula
    (CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula.toRawSecondMomentDiagFormula F)

/-- Ambient sign-symmetric formulas also enter the standard rotated-peeling diagonal block. -/
def toRotatedPeelCenteredMomentDiagFormula :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k :=
  CardinalPrincipalRepVectorRawSecondMomentDiagFormula.toRotatedPeelCenteredMomentDiagFormula
    (CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula.toRawSecondMomentDiagFormula F)

end CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
