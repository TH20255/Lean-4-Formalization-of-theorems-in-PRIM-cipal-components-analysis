import Prim.Probability.ConditionalCovariance.Preserved.Core.Basic

open scoped BigOperators Matrix
open MeasureTheory

/-!
Trace and trace-only diagonal-entry witnesses for event-conditioned preserved covariance.
-/

namespace Prim.Probability


/-- Preserved total variance, represented as the matrix trace. -/
noncomputable def preservedTrace {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) : ℝ :=
  Matrix.trace (preservedCov d μ s X)

/-- Preserved traces are unchanged by replacing the event with an a.e.-equal event. -/
theorem preservedTrace_congr_set {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) {s t : Set Ω} (h : s =ᵐ[μ] t)
    (X : Ω → Prim.Vec d) :
    preservedTrace d μ s X = preservedTrace d μ t X := by
  simp [preservedTrace, preservedCov_congr_set d μ h X]

/-- Preserved traces are unchanged when the random vectors are a.e. equal. -/
theorem preservedTrace_congr_ae {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) {X Y : Ω → Prim.Vec d}
    (hXY : X =ᵐ[μ] Y) :
    preservedTrace d μ s X = preservedTrace d μ s Y := by
  simp [preservedTrace, preservedCov_congr_ae d μ s hXY]

/-- Accessor theorem for the conditioned covariance definition. -/
@[simp] theorem preservedCov_eq_covariance_condOn {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) :
    preservedCov d μ s X = covarianceMatrix d (condOn μ s) X := rfl

/-- Accessor theorem for the preserved trace definition. -/
@[simp] theorem preservedTrace_eq_trace_preservedCov {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) :
    preservedTrace d μ s X = Matrix.trace (preservedCov d μ s X) := rfl

/-- The trace of the preserved covariance is the sum of its diagonal entries. -/
@[simp] theorem preservedTrace_eq_sum_diag {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) :
    preservedTrace d μ s X = ∑ i, preservedCov d μ s X i i := by
  simp [preservedTrace, Matrix.trace]

/--
Witness that the diagonal entries of a preserved covariance matrix have a
prescribed form.

Unlike `DiagonalPreservedCovariance`, this does not require off-diagonal
entries to vanish.  It is the minimal data needed for trace calculations.
-/
structure PreservedCovarianceDiagonalEntries {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) where
  diagVal : Prim.Idx d → ℝ
  diag_eq : ∀ i, preservedCov d μ s X i i = diagVal i

namespace PreservedCovarianceDiagonalEntries

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat}
variable {μ : Measure Ω} {s : Set Ω} {X : Ω → Prim.Vec d}
variable (hD : PreservedCovarianceDiagonalEntries d μ s X)

/-- Package a trace-only preserved-covariance diagonal formula. -/
def ofDiagEq
    (diagVal : Prim.Idx d → ℝ)
    (hdiag : ∀ i, preservedCov d μ s X i i = diagVal i) :
    PreservedCovarianceDiagonalEntries d μ s X where
  diagVal := diagVal
  diag_eq := hdiag

/--
Package a trace-only preserved-covariance diagonal formula from raw centered
integral identities.
-/
def ofCenteredIntegralDiag
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i,
        (∫ ω, (X ω i - meanVec d (condOn μ s) X i) *
            (X ω i - meanVec d (condOn μ s) X i) ∂ condOn μ s) =
          diagVal i) :
    PreservedCovarianceDiagonalEntries d μ s X :=
  ofDiagEq diagVal (fun i => by
    simpa [preservedCov_apply, preservedCenteredProductMoment, centeredProductMoment] using hdiag i)

/--
Package a trace-only preserved-covariance diagonal formula from named centered
product moments.
-/
def ofCenteredProductMomentDiag
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i, preservedCenteredProductMoment d μ s X i i = diagVal i) :
    PreservedCovarianceDiagonalEntries d μ s X :=
  ofDiagEq diagVal (fun i => by
    rw [preservedCov_apply]
    exact hdiag i)

/-- Trace formula from diagonal entries alone. -/
theorem preservedTrace_eq_sum_diagVal :
    preservedTrace d μ s X = ∑ i, hD.diagVal i := by
  rw [preservedTrace_eq_sum_diag]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact hD.diag_eq i

end PreservedCovarianceDiagonalEntries


end Prim.Probability
