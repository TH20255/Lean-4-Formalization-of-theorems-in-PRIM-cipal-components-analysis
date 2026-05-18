import Prim.Proofs.RotationOptimality.CovarianceLanding.Basics.Representation.Conditioning

/-!
Conditioned principal-representation integral identities for factored moment sources.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open MeasureTheory

variable {d : Nat}

/-- Under the representation-coordinate conditioned measure, the named
principal-vector coordinate mean is the square-root eigenvalue times the
source-facing `R * O_j` integral. -/
theorem meanVec_principalRepVector_eq_sqrt_mul_integral_RO_condOn_rotatedRepPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j : Prim.Idx d) :
    Prim.Probability.meanVec d
        (Prim.Probability.condOn diagonal.core.μ
          (rotatedRepPeelEvent diagonal U I))
        (principalRepVector diagonal.core) j =
      Real.sqrt (diagonal.core.profile.eigenvalue j) *
        (∫ ω, diagonal.core.R ω * diagonal.core.O ω j ∂
          Prim.Probability.condOn diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)) := by
  let ν := Prim.Probability.condOn diagonal.core.μ
    (rotatedRepPeelEvent diagonal U I)
  calc
    Prim.Probability.meanVec d
        (Prim.Probability.condOn diagonal.core.μ
          (rotatedRepPeelEvent diagonal U I))
        (principalRepVector diagonal.core) j =
        ∫ ω, diagonal.core.R ω *
          Real.sqrt (diagonal.core.profile.eigenvalue j) *
          diagonal.core.O ω j ∂ ν := by
          rfl
    _ = ∫ ω,
          Real.sqrt (diagonal.core.profile.eigenvalue j) *
            (diagonal.core.R ω * diagonal.core.O ω j) ∂ ν := by
          apply integral_congr_ae
          filter_upwards with ω
          ring
    _ = Real.sqrt (diagonal.core.profile.eigenvalue j) *
        (∫ ω, diagonal.core.R ω * diagonal.core.O ω j ∂ ν) := by
          rw [integral_const_mul]
    _ = Real.sqrt (diagonal.core.profile.eigenvalue j) *
        (∫ ω, diagonal.core.R ω * diagonal.core.O ω j ∂
          Prim.Probability.condOn diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)) := by
          rfl

/-- Under the representation-coordinate conditioned measure, the
principal-vector raw coordinate square is exactly the weighted `R^2 * O_j^2`
source integral. -/
theorem principalRepVector_sq_integral_eq_weighted_RO_sq_condOn_rotatedRepPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j : Prim.Idx d) :
    (∫ ω,
        principalRepVector diagonal.core ω j *
          principalRepVector diagonal.core ω j ∂
        Prim.Probability.condOn diagonal.core.μ
          (rotatedRepPeelEvent diagonal U I)) =
      diagonal.core.profile.eigenvalue j *
        (∫ ω,
          (diagonal.core.R ω) ^ (2 : Nat) *
            (diagonal.core.O ω j) ^ (2 : Nat) ∂
          Prim.Probability.condOn diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)) := by
  let ν := Prim.Probability.condOn diagonal.core.μ
    (rotatedRepPeelEvent diagonal U I)
  calc
    (∫ ω,
        principalRepVector diagonal.core ω j *
          principalRepVector diagonal.core ω j ∂
        Prim.Probability.condOn diagonal.core.μ
          (rotatedRepPeelEvent diagonal U I)) =
      (∫ ω,
        diagonal.core.profile.eigenvalue j *
          ((diagonal.core.R ω) ^ (2 : Nat) *
            (diagonal.core.O ω j) ^ (2 : Nat)) ∂ ν) := by
        apply integral_congr_ae
        filter_upwards with ω
        have hsqrt :
            (Real.sqrt (diagonal.core.profile.eigenvalue j)) ^ (2 : Nat) =
              diagonal.core.profile.eigenvalue j := by
          exact Real.sq_sqrt (diagonal.core.profile.lambda_nonneg j)
        simp only [principalRepVector_apply]
        ring_nf
        rw [hsqrt]
        ring
    _ = diagonal.core.profile.eigenvalue j *
        (∫ ω,
          (diagonal.core.R ω) ^ (2 : Nat) *
            (diagonal.core.O ω j) ^ (2 : Nat) ∂ ν) := by
        rw [integral_const_mul]
    _ = diagonal.core.profile.eigenvalue j *
        (∫ ω,
          (diagonal.core.R ω) ^ (2 : Nat) *
            (diagonal.core.O ω j) ^ (2 : Nat) ∂
          Prim.Probability.condOn diagonal.core.μ
            (rotatedRepPeelEvent diagonal U I)) := by
        rfl

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
