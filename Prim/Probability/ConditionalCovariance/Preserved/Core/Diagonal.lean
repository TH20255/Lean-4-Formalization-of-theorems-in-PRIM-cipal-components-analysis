import Prim.Probability.ConditionalCovariance.Preserved.Core.Trace

open scoped BigOperators Matrix
open MeasureTheory

/-!
Diagonal preserved-covariance witnesses and constructors.
-/

namespace Prim.Probability

/--
Witness that a preserved covariance matrix is diagonal with prescribed diagonal
entries. This is the shape produced by the paper's core theorems.
-/
structure DiagonalPreservedCovariance {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) where
  diagVal : Prim.Idx d → ℝ
  diag_eq : ∀ i, preservedCov d μ s X i i = diagVal i
  offDiag_eq_zero : ∀ {i j}, i ≠ j → preservedCov d μ s X i j = 0

namespace DiagonalPreservedCovariance

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat}
variable {μ : Measure Ω} {s : Set Ω} {X : Ω → Prim.Vec d}
variable (hD : DiagonalPreservedCovariance d μ s X)

/-- Forget the off-diagonal-zero data when only a trace calculation is needed. -/
def toDiagonalEntries :
    PreservedCovarianceDiagonalEntries d μ s X where
  diagVal := hD.diagVal
  diag_eq := hD.diag_eq

/-- Recover the full preserved covariance matrix as a diagonal matrix. -/
theorem matrix_eq_diagonal :
    preservedCov d μ s X = Matrix.diagonal hD.diagVal := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal, hD.diag_eq]
  · rw [hD.offDiag_eq_zero hij]
    simp [Matrix.diagonal, hij]

/-- Trace formula for diagonal preserved covariance matrices. -/
theorem preservedTrace_eq_sum_diagVal :
    preservedTrace d μ s X = ∑ i, hD.diagVal i := by
  exact hD.toDiagonalEntries.preservedTrace_eq_sum_diagVal


end DiagonalPreservedCovariance

/--
Build a full diagonal-covariance witness from diagonal values and
upper-triangular off-diagonal vanishing.
-/
def diagonalPreservedCovarianceOfDiagAndUpperOffDiag {Ω : Type*}
    [MeasurableSpace Ω] (d : Nat) (μ : Measure Ω) (s : Set Ω)
    (X : Ω → Prim.Vec d) (diagVal : Prim.Idx d → ℝ)
    (hdiag : ∀ i, preservedCov d μ s X i i = diagVal i)
    (hupper : ∀ {i j : Prim.Idx d}, i < j →
      preservedCov d μ s X i j = 0) :
    DiagonalPreservedCovariance d μ s X where
  diagVal := diagVal
  diag_eq := hdiag
  offDiag_eq_zero := preservedCov_offDiag_eq_zero_of_lt d μ s X hupper

/--
Build a full diagonal-covariance witness from centered second-moment integral
formulas. This is the probability-facing shape of the remaining covariance
calculation.
-/
def diagonalPreservedCovarianceOfCenteredIntegralAndUpperCenteredIntegral {Ω : Type*}
    [MeasurableSpace Ω] (d : Nat) (μ : Measure Ω) (s : Set Ω)
    (X : Ω → Prim.Vec d) (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i,
        (∫ ω, (X ω i - meanVec d (condOn μ s) X i) *
            (X ω i - meanVec d (condOn μ s) X i) ∂ condOn μ s) =
          diagVal i)
    (hupper :
      ∀ {i j : Prim.Idx d}, i < j →
        (∫ ω, (X ω i - meanVec d (condOn μ s) X i) *
            (X ω j - meanVec d (condOn μ s) X j) ∂ condOn μ s) = 0) :
    DiagonalPreservedCovariance d μ s X :=
  diagonalPreservedCovarianceOfDiagAndUpperOffDiag d μ s X diagVal
    (fun i => by simpa using hdiag i)
    (fun {i j} hij => by simpa using hupper (i := i) (j := j) hij)

/--
Build a full diagonal-covariance witness from named preserved centered product
moments.  This is the compact version of
`diagonalPreservedCovarianceOfCenteredIntegralAndUpperCenteredIntegral`.
-/
def diagonalPreservedCovarianceOfCenteredProductMomentAndUpperCenteredProductMoment
    {Ω : Type*} [MeasurableSpace Ω] (d : Nat) (μ : Measure Ω) (s : Set Ω)
    (X : Ω → Prim.Vec d) (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i, preservedCenteredProductMoment d μ s X i i = diagVal i)
    (hupper :
      ∀ {i j : Prim.Idx d}, i < j →
        preservedCenteredProductMoment d μ s X i j = 0) :
    DiagonalPreservedCovariance d μ s X :=
  diagonalPreservedCovarianceOfDiagAndUpperOffDiag d μ s X diagVal
    (fun i => by rw [preservedCov_apply]; exact hdiag i)
    (fun {i j} hij => by rw [preservedCov_apply]; exact hupper hij)


end Prim.Probability
