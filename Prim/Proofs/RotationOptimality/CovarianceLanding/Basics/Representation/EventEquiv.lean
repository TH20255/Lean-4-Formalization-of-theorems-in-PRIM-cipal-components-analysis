import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Representation.Basic

/-!
Event-equivalence and simple rotated-peeling event rewrites.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open MeasureTheory

variable {d : Nat}

/-- Almost surely, the rotated peeling event can be read directly from the
rotated stochastic representation coordinates. -/
theorem mem_rotatedPeelEvent_ae_rep
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    ∀ᵐ ω ∂ diagonal.core.μ,
      (ω ∈ rotatedPeelEvent diagonal U I ↔
        ∀ i ∈ I,
          |diagonal.core.R ω * rotatedLoading diagonal.core U ω i| ≤
            diagonal.core.halfWidth diagonal.q i) := by
  exact (rotatedVector_ae_eq_R_mul_rotatedLoading diagonal.core U).mono (by
    intro ω hrep
    rw [mem_rotatedPeelEvent]
    constructor
    · intro h i hi
      rw [← hrep i]
      exact h i hi
    · intro h i hi
      rw [hrep i]
      exact h i hi)

/-- The rotated-peeling event and its stochastic-representation version agree
outside a null set. -/
theorem rotatedPeelEvent_ae_eq_rep
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedPeelEvent diagonal U I =ᵐ[diagonal.core.μ]
      rotatedRepPeelEvent diagonal U I := by
  exact (mem_rotatedPeelEvent_ae_rep diagonal U I).mono (by
    intro ω hω
    apply propext
    change rotatedPeelEvent diagonal U I ω ↔
      ∀ i ∈ I,
        |diagonal.core.R ω * rotatedLoading diagonal.core U ω i| ≤
          diagonal.core.halfWidth diagonal.q i
    exact hω)

/-- Conditioning on the rotated-peeling event may equivalently use the
stochastic-representation event. -/
theorem condOn_rotatedPeelEvent_eq_rep
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Prim.Probability.condOn diagonal.core.μ (rotatedPeelEvent diagonal U I) =
      Prim.Probability.condOn diagonal.core.μ (rotatedRepPeelEvent diagonal U I) :=
  Prim.Probability.condOn_congr_set diagonal.core.μ
    (rotatedPeelEvent_ae_eq_rep diagonal U I)

@[simp] theorem rotatedPeelEvent_identity
    (diagonal : KDimensionalDiagonalProfile d) (I : Finset (Prim.Idx d)) :
    rotatedPeelEvent diagonal (OrthogonalMatrixRotation.identity d) I =
      diagonal.core.peelSetEvent diagonal.q I := by
  ext ω
  simp [rotatedPeelEvent, Prim.Elliptical.EllipticalCore.peelSetEvent]

@[simp] theorem rotatedPeelEvent_empty
    (diagonal : KDimensionalDiagonalProfile d) (U : OrthogonalMatrixRotation d) :
    rotatedPeelEvent diagonal U (∅ : Finset (Prim.Idx d)) =
      diagonal.core.peelSetEvent diagonal.q (∅ : Finset (Prim.Idx d)) := by
  ext ω
  simp [rotatedPeelEvent, Prim.Elliptical.EllipticalCore.peelSetEvent]

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
