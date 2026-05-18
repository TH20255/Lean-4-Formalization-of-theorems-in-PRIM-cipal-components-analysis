import Prim.Proofs.KDimensional.Diagonal.Base
import Prim.Proofs.RotationOptimality.Basic.Abstract.Orthogonal

/-!
Rotated stochastic-representation vectors, rotated peeling events, and event transport lemmas.
-/

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open MeasureTheory

variable {d : Nat}

/-- Random vector after applying an orthogonal coordinate rotation. -/
noncomputable def rotatedVector
    (E : Prim.Elliptical.EllipticalCore d) (U : OrthogonalMatrixRotation d) :
    E.Ω → Prim.Vec d :=
  fun ω => Matrix.mulVec U.matrix (E.Y ω)

@[simp] theorem rotatedVector_apply
    (E : Prim.Elliptical.EllipticalCore d)
    (U : OrthogonalMatrixRotation d) (ω : E.Ω) (i : Prim.Idx d) :
    rotatedVector E U ω i = Matrix.mulVec U.matrix (E.Y ω) i := by
  rfl

@[simp] theorem rotatedVector_identity
    (E : Prim.Elliptical.EllipticalCore d) (ω : E.Ω) :
    rotatedVector E (OrthogonalMatrixRotation.identity d) ω = E.Y ω := by
  funext i
  change Matrix.mulVec (1 : Prim.Mat d) (E.Y ω) i = E.Y ω i
  rw [Matrix.one_mulVec]

/-- The deterministic angular/loading coordinate in the stochastic representation
of a rotated elliptical vector. -/
noncomputable def rotatedLoading
    (E : Prim.Elliptical.EllipticalCore d) (U : OrthogonalMatrixRotation d)
    (ω : E.Ω) (i : Prim.Idx d) : ℝ :=
  ∑ j : Prim.Idx d, U.matrix i j * (Real.sqrt (E.profile.eigenvalue j) * E.O ω j)

/- The principal-coordinate stochastic-representation vector
`R * sqrt(lambda) * O`, before applying any external rotation. -/
noncomputable def principalRepVector
    (E : Prim.Elliptical.EllipticalCore d) : E.Ω → Prim.Vec d :=
  fun ω i => E.R ω * Real.sqrt (E.profile.eigenvalue i) * E.O ω i

@[simp] theorem principalRepVector_apply
    (E : Prim.Elliptical.EllipticalCore d) (ω : E.Ω) (i : Prim.Idx d) :
    principalRepVector E ω i =
      E.R ω * Real.sqrt (E.profile.eigenvalue i) * E.O ω i := by
  rfl

/- The stochastic representation as an a.e. equality of vectors. -/
theorem principalRepVector_ae_eq
    (E : Prim.Elliptical.EllipticalCore d) :
    E.Y =ᵐ[E.μ] principalRepVector E := by
  exact E.principal_rep.mono (by
    intro ω hrep
    funext i
    exact hrep i)

@[simp] theorem rotatedLoading_identity
    (E : Prim.Elliptical.EllipticalCore d) (ω : E.Ω) (i : Prim.Idx d) :
    rotatedLoading E (OrthogonalMatrixRotation.identity d) ω i =
      Real.sqrt (E.profile.eigenvalue i) * E.O ω i := by
  change
    (∑ j : Prim.Idx d,
      (1 : Prim.Mat d) i j * (Real.sqrt (E.profile.eigenvalue j) * E.O ω j)) =
        Real.sqrt (E.profile.eigenvalue i) * E.O ω i
  simp [Matrix.one_apply]

theorem rotatedVector_eq_R_mul_rotatedLoading_of_principal_rep
    (E : Prim.Elliptical.EllipticalCore d) (U : OrthogonalMatrixRotation d)
    {ω : E.Ω}
    (hrep : ∀ j : Prim.Idx d,
      E.Y ω j = E.R ω * Real.sqrt (E.profile.eigenvalue j) * E.O ω j)
    (i : Prim.Idx d) :
    rotatedVector E U ω i = E.R ω * rotatedLoading E U ω i := by
  simp only [rotatedVector, Matrix.mulVec, rotatedLoading]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hrep j]
  ring_nf

/-- The principal stochastic representation transported through a fixed rotation. -/
theorem rotatedVector_ae_eq_R_mul_rotatedLoading
    (E : Prim.Elliptical.EllipticalCore d) (U : OrthogonalMatrixRotation d) :
    ∀ᵐ ω ∂ E.μ, ∀ i : Prim.Idx d,
      rotatedVector E U ω i = E.R ω * rotatedLoading E U ω i := by
  exact E.principal_rep.mono (by
    intro ω hrep i
    exact rotatedVector_eq_R_mul_rotatedLoading_of_principal_rep E U hrep i)

/--
Peeling event in the coordinates obtained by applying an orthogonal rotation to
the principal random vector.
-/
def rotatedPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Set diagonal.core.Ω :=
  Prim.Probability.peelEvent d (rotatedVector diagonal.core U)
    (diagonal.core.halfWidth diagonal.q) I

/-- The same rotated-peeling event, written in the stochastic-representation
coordinates supplied by `EllipticalCore.principal_rep`. -/
def rotatedRepPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    Set diagonal.core.Ω :=
  {ω | ∀ i ∈ I,
    |diagonal.core.R ω * rotatedLoading diagonal.core U ω i| ≤
      diagonal.core.halfWidth diagonal.q i}

@[simp] theorem rotatedPeelEvent_eq_peelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) :
    rotatedPeelEvent diagonal U I =
      Prim.Probability.peelEvent d (rotatedVector diagonal.core U)
        (diagonal.core.halfWidth diagonal.q) I := by
  rfl

@[simp] theorem mem_rotatedPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (ω : diagonal.core.Ω) :
    ω ∈ rotatedPeelEvent diagonal U I ↔
      ∀ i ∈ I, |rotatedVector diagonal.core U ω i| ≤
        diagonal.core.halfWidth diagonal.q i := by
  rfl

@[simp] theorem mem_rotatedRepPeelEvent
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (ω : diagonal.core.Ω) :
    ω ∈ rotatedRepPeelEvent diagonal U I ↔
      ∀ i ∈ I,
        |diagonal.core.R ω * rotatedLoading diagonal.core U ω i| ≤
          diagonal.core.halfWidth diagonal.q i := by
  rfl

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
