import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Ambient.AmbientSymmetric

/-!
Observed angular second-moment source package for ambient formulas.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Ambient sign-symmetric source with an explicit observed weighted angular
second-moment profile.

This is the next analytic-facing landing shape after ambient sign symmetry:
future spherical arguments may first identify a measured weighted moment with
the actual conditioned integral, then prove the closed-form expression for
that measured moment.  This object mechanically produces the final ambient
weighted source used by the trace chain.
-/
structure CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula
    (diagonal : KDimensionalDiagonalProfile d) (k : Nat) where
  weightedSecondMoment :
    OrthogonalMatrixRotation d -> Finset (Prim.Idx d) -> Prim.Idx d -> ℝ
  mean_ambient_symmetry :
    ∀ U I, I.card = k →
      ∀ j, rotatedRepPeelROAmbientSignSymmetry diagonal U I j
  weightedSecondMoment_eq_integral :
    ∀ U I, I.card = k →
      ∀ j,
        weightedSecondMoment U I j =
          diagonal.core.profile.eigenvalue j *
            (∫ ω,
              (diagonal.core.R ω) ^ (2 : Nat) *
                (diagonal.core.O ω j) ^ (2 : Nat) ∂
              Prim.Probability.condOn diagonal.core.μ
                (rotatedRepPeelEvent diagonal U I))
  weightedSecondMoment_formula :
    ∀ U I, I.card = k →
      ∀ j,
        weightedSecondMoment U I j =
          diagonal.a * diagonal.core.profile.eigenvalue j +
            if j ∈ I then
              (diagonal.b - diagonal.a) *
                (∑ l : Prim.Idx d,
                  (U.matrix j l) ^ (2 : Nat) *
                    diagonal.core.profile.eigenvalue l)
            else 0

namespace CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula

variable {diagonal : KDimensionalDiagonalProfile d} {k : Nat}
variable (F :
  CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula diagonal k)

/-- Observed weighted angular moments give the ambient weighted source target. -/
def toAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
      diagonal k where
  mean_ambient_symmetry := F.mean_ambient_symmetry
  second_moment := by
    intro U I hI j
    calc
      diagonal.core.profile.eigenvalue j *
          (∫ ω,
            (diagonal.core.R ω) ^ (2 : Nat) *
              (diagonal.core.O ω j) ^ (2 : Nat) ∂
            Prim.Probability.condOn diagonal.core.μ
              (rotatedRepPeelEvent diagonal U I)) =
          F.weightedSecondMoment U I j := by
            exact (F.weightedSecondMoment_eq_integral U I hI j).symm
      _ =
          diagonal.a * diagonal.core.profile.eigenvalue j +
            if j ∈ I then
              (diagonal.b - diagonal.a) *
                (∑ l : Prim.Idx d,
                  (U.matrix j l) ^ (2 : Nat) *
                    diagonal.core.profile.eigenvalue l)
            else 0 := F.weightedSecondMoment_formula U I hI j

/-- Observed weighted angular moments give the conditioned sign-symmetric source. -/
def toSignSymmetricWeightedFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
      diagonal k :=
  F.toAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    |>.toSignSymmetricWeightedFactoredRawSecondMomentDiagFormula

/-- Observed weighted angular moments give the unified weighted source target. -/
def toWeightedFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorWeightedFactoredRawSecondMomentDiagFormula diagonal k :=
  F.toAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    |>.toWeightedFactoredRawSecondMomentDiagFormula

/-- Observed weighted angular moments give the factored source target. -/
def toFactoredRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorFactoredRawSecondMomentDiagFormula diagonal k :=
  F.toAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    |>.toFactoredRawSecondMomentDiagFormula

/-- Observed weighted angular moments give the raw second-moment target. -/
def toRawSecondMomentDiagFormula :
    CardinalPrincipalRepVectorRawSecondMomentDiagFormula diagonal k :=
  F.toAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    |>.toRawSecondMomentDiagFormula

/-- Observed weighted angular moments give the explicit-principal-vector centered formula. -/
def toCenteredMomentDiagFormula :
    CardinalPrincipalRepVectorCenteredMomentDiagFormula diagonal k :=
  F.toAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    |>.toCenteredMomentDiagFormula

/-- Observed weighted angular moments enter the standard rotated-peeling diagonal block. -/
def toRotatedPeelCenteredMomentDiagFormula :
    CardinalRotatedPeelCenteredMomentDiagFormula diagonal k :=
  F.toAmbientSignSymmetricWeightedFactoredRawSecondMomentDiagFormula
    |>.toRotatedPeelCenteredMomentDiagFormula

end CardinalPrincipalRepVectorAmbientAngularSecondMomentDiagFormula

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
