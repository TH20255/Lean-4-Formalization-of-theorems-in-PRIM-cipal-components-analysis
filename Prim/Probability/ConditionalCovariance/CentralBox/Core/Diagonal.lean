import Prim.Probability.ConditionalCovariance.CentralBox.Core.Trace
import Prim.Probability.ConditionalCovariance.Preserved.Core.Diagonal

open scoped BigOperators Matrix
open MeasureTheory

/-!
Diagonal central-box preserved-covariance witnesses.
-/

namespace Prim.Probability

namespace CentralBoxData

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat} (B : CentralBoxData d)

/--
Diagonal covariance witness specialized to a central-box peeling event.
-/
structure DiagonalPreservedCovariance (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) where
  diagVal : Prim.Idx d → ℝ
  diag_eq : ∀ i, B.preservedCov μ X I i i = diagVal i
  offDiag_eq_zero : ∀ {i j}, i ≠ j → B.preservedCov μ X I i j = 0

namespace DiagonalPreservedCovariance

variable {μ : Measure Ω} {X : Ω → Prim.Vec d} {I : Finset (Fin d)}
variable (hD : B.DiagonalPreservedCovariance μ X I)

/-- Forget the off-diagonal-zero data when only a trace calculation is needed. -/
def toDiagonalEntries :
    B.PreservedCovarianceDiagonalEntries μ X I where
  diagVal := hD.diagVal
  diag_eq := hD.diag_eq

/-- Convert a box-event diagonal witness to the generic diagonal witness. -/
def toGeneric (hD : B.DiagonalPreservedCovariance μ X I) :
    Prim.Probability.DiagonalPreservedCovariance d μ (B.event X I) X where
  diagVal := hD.diagVal
  diag_eq := hD.diag_eq
  offDiag_eq_zero := hD.offDiag_eq_zero

/-- Recover the full preserved covariance matrix as a diagonal matrix. -/
theorem matrix_eq_diagonal :
    B.preservedCov μ X I = Matrix.diagonal hD.diagVal := by
  simpa [CentralBoxData.preservedCov] using
    (DiagonalPreservedCovariance.toGeneric (B := B) hD).matrix_eq_diagonal

/-- Trace formula for diagonal preserved covariance matrices on box events. -/
theorem preservedTrace_eq_sum_diagVal :
    B.preservedTrace μ X I = ∑ i, hD.diagVal i := by
  exact hD.toDiagonalEntries.preservedTrace_eq_sum_diagVal


end DiagonalPreservedCovariance


end CentralBoxData

end Prim.Probability
