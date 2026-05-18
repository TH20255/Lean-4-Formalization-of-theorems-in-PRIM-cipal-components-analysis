import Prim.Probability.ConditionalCovariance.CentralBox.Core.Diagonal

open scoped BigOperators Matrix
open MeasureTheory

/-!
Upper-triangular constructors for central-box preserved covariance witnesses.
-/

namespace Prim.Probability

namespace CentralBoxData

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat} (B : CentralBoxData d)

/--
For central-box events, it suffices to prove vanishing cross-covariances on the
strictly upper triangle.
-/
theorem preservedCov_offDiag_eq_zero_of_lt
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d))
    (hupper : ∀ {i j : Prim.Idx d}, i < j → B.preservedCov μ X I i j = 0)
    {i j : Prim.Idx d} (hij : i ≠ j) :
    B.preservedCov μ X I i j = 0 := by
  exact Prim.Probability.preservedCov_offDiag_eq_zero_of_lt d μ
    (B.event X I) X hupper hij

/--
Build a central-box diagonal-covariance witness from diagonal values and
upper-triangular off-diagonal vanishing.
-/
def diagonalPreservedCovarianceOfDiagAndUpperOffDiag
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag : ∀ i, B.preservedCov μ X I i i = diagVal i)
    (hupper : ∀ {i j : Prim.Idx d}, i < j →
      B.preservedCov μ X I i j = 0) :
    B.DiagonalPreservedCovariance μ X I where
  diagVal := diagVal
  diag_eq := hdiag
  offDiag_eq_zero := B.preservedCov_offDiag_eq_zero_of_lt μ X I hupper

/--
Build a central-box diagonal-covariance witness from centered second-moment
integral formulas over the box-conditioned measure.
-/
def diagonalPreservedCovarianceOfCenteredIntegralAndUpperCenteredIntegral
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i,
        (∫ ω, (X ω i - meanVec d (condOn μ (B.event X I)) X i) *
            (X ω i - meanVec d (condOn μ (B.event X I)) X i) ∂
              condOn μ (B.event X I)) =
          diagVal i)
    (hupper :
      ∀ {i j : Prim.Idx d}, i < j →
        (∫ ω, (X ω i - meanVec d (condOn μ (B.event X I)) X i) *
            (X ω j - meanVec d (condOn μ (B.event X I)) X j) ∂
              condOn μ (B.event X I)) = 0) :
    B.DiagonalPreservedCovariance μ X I :=
  B.diagonalPreservedCovarianceOfDiagAndUpperOffDiag μ X I diagVal
    (fun i => by simpa [CentralBoxData.preservedCov] using hdiag i)
    (fun {i j} hij => by
      simpa [CentralBoxData.preservedCov] using hupper (i := i) (j := j) hij)

/--
Build a central-box diagonal-covariance witness from named centered product
moments over the box-conditioned measure.
-/
def diagonalPreservedCovarianceOfCenteredProductMomentAndUpperCenteredProductMoment
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i, B.preservedCenteredProductMoment μ X I i i = diagVal i)
    (hupper :
      ∀ {i j : Prim.Idx d}, i < j →
        B.preservedCenteredProductMoment μ X I i j = 0) :
    B.DiagonalPreservedCovariance μ X I :=
  B.diagonalPreservedCovarianceOfDiagAndUpperOffDiag μ X I diagVal
    (fun i => by rw [B.preservedCov_eq_centeredProductMoment]; exact hdiag i)
    (fun {i j} hij => by
      rw [B.preservedCov_eq_centeredProductMoment]
      exact hupper hij)

end CentralBoxData

end Prim.Probability
