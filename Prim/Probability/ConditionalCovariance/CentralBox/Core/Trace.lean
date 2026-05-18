import Prim.Probability.ConditionalCovariance.CentralBox.Core.Basic

open scoped BigOperators Matrix
open MeasureTheory

/-!
Trace-only central-box diagonal-entry witnesses.
-/

namespace Prim.Probability

namespace CentralBoxData

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat} (B : CentralBoxData d)

/--
Diagonal-entry witness specialized to a central-box peeling event.

This is the trace-only version: no off-diagonal claim is required.
-/
structure PreservedCovarianceDiagonalEntries (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) where
  diagVal : Prim.Idx d → ℝ
  diag_eq : ∀ i, B.preservedCov μ X I i i = diagVal i

namespace PreservedCovarianceDiagonalEntries

variable {μ : Measure Ω} {X : Ω → Prim.Vec d} {I : Finset (Fin d)}
variable (hD : B.PreservedCovarianceDiagonalEntries μ X I)

/-- Package a trace-only diagonal formula on a central-box event. -/
def ofDiagEq
    (diagVal : Prim.Idx d → ℝ)
    (hdiag : ∀ i, B.preservedCov μ X I i i = diagVal i) :
    B.PreservedCovarianceDiagonalEntries μ X I where
  diagVal := diagVal
  diag_eq := hdiag

/--
Package a trace-only diagonal formula on a central-box event from raw centered
integral identities.
-/
def ofCenteredIntegralDiag
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i,
        (∫ ω, (X ω i - meanVec d (condOn μ (B.event X I)) X i) *
            (X ω i - meanVec d (condOn μ (B.event X I)) X i) ∂
              condOn μ (B.event X I)) =
          diagVal i) :
    B.PreservedCovarianceDiagonalEntries μ X I :=
  ofDiagEq (B := B) diagVal (fun i => by
    simpa [CentralBoxData.preservedCov] using hdiag i)

/--
Package a trace-only diagonal formula on a central-box event from named
centered product moments.
-/
def ofCenteredProductMomentDiag
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i, B.preservedCenteredProductMoment μ X I i i = diagVal i) :
    B.PreservedCovarianceDiagonalEntries μ X I :=
  ofDiagEq (B := B) diagVal (fun i => by
    rw [B.preservedCov_eq_centeredProductMoment]
    exact hdiag i)

/-- Convert a box-event diagonal-entry witness to the generic witness. -/
def toGeneric :
    Prim.Probability.PreservedCovarianceDiagonalEntries d μ (B.event X I) X where
  diagVal := hD.diagVal
  diag_eq := hD.diag_eq

/-- Trace formula for central-box preserved covariance from diagonal entries alone. -/
theorem preservedTrace_eq_sum_diagVal :
    B.preservedTrace μ X I = ∑ i, hD.diagVal i := by
  simpa [CentralBoxData.preservedTrace] using hD.toGeneric.preservedTrace_eq_sum_diagVal

end PreservedCovarianceDiagonalEntries


end CentralBoxData

end Prim.Probability
