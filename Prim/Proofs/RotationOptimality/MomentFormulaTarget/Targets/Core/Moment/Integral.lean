import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Covariance.Basic

/-!
Raw centered-integral objects for rotated-peeling conditioned measures.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/-- Raw centered integral for a rotated-peeling conditioned measure. -/
noncomputable def rotatedPeelCenteredIntegral
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) : ℝ :=
  ∫ ω, (diagonal.core.Y ω j -
        Prim.Probability.meanVec d
          (Prim.Probability.condOn diagonal.core.μ
            (rotatedPeelEvent diagonal U I)) diagonal.core.Y j) *
      (diagonal.core.Y ω l -
        Prim.Probability.meanVec d
          (Prim.Probability.condOn diagonal.core.μ
            (rotatedPeelEvent diagonal U I)) diagonal.core.Y l) ∂
      Prim.Probability.condOn diagonal.core.μ (rotatedPeelEvent diagonal U I)

/-- Raw centered integral using the stochastic-representation-coordinate event. -/
noncomputable def rotatedRepPeelCenteredIntegral
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) : ℝ :=
  ∫ ω, (diagonal.core.Y ω j -
        Prim.Probability.meanVec d
          (Prim.Probability.condOn diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)) diagonal.core.Y j) *
      (diagonal.core.Y ω l -
        Prim.Probability.meanVec d
          (Prim.Probability.condOn diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)) diagonal.core.Y l) ∂
      Prim.Probability.condOn diagonal.core.μ (rotatedRepPeelEvent diagonal U I)

/-- The raw integral target is definitionally the named centered product moment. -/
theorem rotatedPeelCenteredIntegral_eq_centeredProductMoment
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) :
    rotatedPeelCenteredIntegral diagonal U I j l =
      rotatedPeelCenteredProductMoment diagonal U I j l := by
  rfl

/-- The raw rotated-peeling integral can be computed on the representation event. -/
theorem rotatedPeelCenteredIntegral_eq_rep
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j l : Prim.Idx d) :
    rotatedPeelCenteredIntegral diagonal U I j l =
      rotatedRepPeelCenteredIntegral diagonal U I j l := by
  rw [rotatedPeelCenteredIntegral, rotatedRepPeelCenteredIntegral,
    condOn_rotatedPeelEvent_eq_rep diagonal U I]

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
