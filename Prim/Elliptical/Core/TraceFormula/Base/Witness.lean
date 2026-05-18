import Prim.Elliptical.Core.BoxOps.Basic
import Prim.Probability.ConditionalCovariance.CentralBox.Core.Trace

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/--
Trace formula from a prescribed diagonal formula for the preserved covariance.

This is the lightest route from a covariance calculation to a trace formula:
off-diagonal entries do not matter for `Matrix.trace`.
-/
theorem preservedTraceOn_eq_sum_diagVal
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag : ∀ i, E.preservedCovOn q hq I i i = diagVal i) :
    E.preservedTraceOn q I = ∑ i, diagVal i := by
  rw [E.preservedTraceOn_eq_sum_diag q hq I]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact hdiag i

/--
Package principal-box diagonal covariance identities as a trace-only diagonal-entry witness.

This is the lightest analytic landing object on the box side: only diagonal
covariance identities are required.
-/
noncomputable def principalBoxDiagonalEntriesOfDiagEq
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag : ∀ i, E.preservedCovOn q hq I i i = diagVal i) :
    (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I :=
  Prim.Probability.CentralBoxData.PreservedCovarianceDiagonalEntries.ofDiagEq
    (B := E.principalBoxData q hq) diagVal (fun i => by
      simpa [EllipticalCore.preservedCovOn_eq (E := E) q hq I] using hdiag i)

/--
Package principal-box diagonal centered integral formulas as a trace-only
diagonal-entry witness.
-/
noncomputable def principalBoxDiagonalEntriesOfCenteredIntegralDiag
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i,
        (∫ ω, (E.Y ω i -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y i) *
            (E.Y ω i -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y i) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) =
          diagVal i) :
    (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I :=
  Prim.Probability.CentralBoxData.PreservedCovarianceDiagonalEntries.ofCenteredIntegralDiag
    (B := E.principalBoxData q hq) diagVal hdiag

/--
Package principal-box diagonal named centered-product formulas as a trace-only
diagonal-entry witness.
-/
noncomputable def principalBoxDiagonalEntriesOfCenteredProductMomentDiag
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i,
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I i i =
          diagVal i) :
    (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I :=
  Prim.Probability.CentralBoxData.PreservedCovarianceDiagonalEntries.ofCenteredProductMomentDiag
    (B := E.principalBoxData q hq) diagVal hdiag

/-- Trace formula on a principal box from diagonal covariance identities alone. -/
theorem preservedTraceOn_eq_sum_diagVal_ofDiagEq
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag : ∀ i, E.preservedCovOn q hq I i i = diagVal i) :
    E.preservedTraceOn q I = ∑ i, diagVal i := by
  let hD := E.principalBoxDiagonalEntriesOfDiagEq q hq I diagVal hdiag
  rw [E.preservedTraceOn_eq q hq I]
  exact hD.preservedTrace_eq_sum_diagVal

/-- Trace formula on a principal box from diagonal centered integral formulas alone. -/
theorem preservedTraceOn_eq_sum_diagVal_ofCenteredIntegralDiag
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i,
        (∫ ω, (E.Y ω i -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y i) *
            (E.Y ω i -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y i) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) =
          diagVal i) :
    E.preservedTraceOn q I = ∑ i, diagVal i := by
  let hD := E.principalBoxDiagonalEntriesOfCenteredIntegralDiag q hq I diagVal hdiag
  rw [E.preservedTraceOn_eq q hq I]
  exact hD.preservedTrace_eq_sum_diagVal

/-- Trace formula on a principal box from diagonal named centered-product formulas alone. -/
theorem preservedTraceOn_eq_sum_diagVal_ofCenteredProductMomentDiag
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d))
    (diagVal : Prim.Idx d → ℝ)
    (hdiag :
      ∀ i,
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I i i =
          diagVal i) :
    E.preservedTraceOn q I = ∑ i, diagVal i := by
  let hD := E.principalBoxDiagonalEntriesOfCenteredProductMomentDiag q hq I diagVal hdiag
  rw [E.preservedTraceOn_eq q hq I]
  exact hD.preservedTrace_eq_sum_diagVal

end EllipticalCore

end Prim.Elliptical
