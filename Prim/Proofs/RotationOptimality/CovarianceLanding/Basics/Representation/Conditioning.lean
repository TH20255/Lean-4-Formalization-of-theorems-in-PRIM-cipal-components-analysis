import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Representation.Basic

/-!
Conditioning inheritance lemmas for rotated representation-coordinate peeling events.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open MeasureTheory

variable {d : Nat}

/-- The principal stochastic representation remains available after
conditioning on any rotated representation-coordinate peeling event. -/
theorem principal_rep_ae_condOn_rotatedRepPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    ∀ᵐ ω ∂ Prim.Probability.condOn diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I),
      ∀ j : Prim.Idx d,
        diagonal.core.Y ω j =
          diagonal.core.R ω *
            Real.sqrt (diagonal.core.profile.eigenvalue j) *
            diagonal.core.O ω j := by
  exact
    Prim.Probability.ae_condOn_of_ae diagonal.core.μ
      (rotatedRepPeelEvent diagonal U I)
      diagonal.core.principal_rep

/-- The named principal representation vector is still a.e.-equal to `Y`
under a rotated representation-coordinate conditioned measure. -/
theorem principalRepVector_ae_eq_condOn_rotatedRepPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    diagonal.core.Y =ᵐ[
      Prim.Probability.condOn diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I)]
      principalRepVector diagonal.core := by
  exact
    Prim.Probability.ae_eq_condOn_of_ae_eq diagonal.core.μ
      (rotatedRepPeelEvent diagonal U I)
      (principalRepVector_ae_eq diagonal.core)

/-- The rotated loading formula for `Y` remains available after conditioning on
the representation-coordinate event. -/
theorem rotatedVector_ae_eq_R_mul_rotatedLoading_condOn_rotatedRepPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    ∀ᵐ ω ∂ Prim.Probability.condOn diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I),
      ∀ i : Prim.Idx d,
        rotatedVector diagonal.core U ω i =
          diagonal.core.R ω * rotatedLoading diagonal.core U ω i := by
  exact
    Prim.Probability.ae_condOn_of_ae diagonal.core.μ
      (rotatedRepPeelEvent diagonal U I)
      (rotatedVector_ae_eq_R_mul_rotatedLoading diagonal.core U)

/-- The angular unit-sphere support property is inherited by every rotated
representation-coordinate conditioned measure. -/
theorem angular_unit_sphere_ae_condOn_rotatedRepPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    ∀ᵐ ω ∂ Prim.Probability.condOn diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I),
      ∑ i : Prim.Idx d, (diagonal.core.O ω i) ^ (2 : Nat) = 1 := by
  exact
    Prim.Probability.ae_condOn_of_ae diagonal.core.μ
      (rotatedRepPeelEvent diagonal U I)
      diagonal.core.angular_unit_sphere

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
