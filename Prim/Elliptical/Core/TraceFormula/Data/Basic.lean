import Prim.Elliptical.Core.TraceFormula.Base.Witness

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/--
Source-facing package for principal-box affine trace formulas.

This is meant to be the handoff object from the analytic stochastic-
representation layer: once that layer proves the diagonal box covariance
formula, all trace monotonicity and leading-vs-trailing comparisons can be
attached by importing the comparison owner.
-/
structure PrincipalBoxTraceFormulaData (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) where
  a : ℝ
  b : ℝ
  coeff_nonpos : b - a ≤ 0
  diagonalEntries :
    ∀ I, (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I
  diagVal_eq :
    ∀ I j, (diagonalEntries I).diagVal j =
      (if j ∈ I then b else a) * E.profile.eigenvalue j

namespace PrincipalBoxTraceFormulaData

variable {d : Nat} {E : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}

/-- Build the package directly from already-packaged diagonal-entry witnesses. -/
noncomputable def ofDiagonalEntries
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ I, (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I)
    (hdiag :
      ∀ I j, (hentries I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxTraceFormulaData E q hq where
  a := a
  b := b
  coeff_nonpos := hcoeff
  diagonalEntries := hentries
  diagVal_eq := hdiag

/-- Build the package from raw diagonal covariance identities. -/
noncomputable def ofDiagEq
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        E.preservedCovOn q hq I j j =
          (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxTraceFormulaData E q hq where
  a := a
  b := b
  coeff_nonpos := hcoeff
  diagonalEntries := fun I =>
    E.principalBoxDiagonalEntriesOfDiagEq q hq I
      (fun j => (if j ∈ I then b else a) * E.profile.eigenvalue j)
      (hdiag I)
  diagVal_eq := by
    intro I j
    rfl

/-- Build the package from diagonal box-centered integral formulas. -/
noncomputable def ofCenteredIntegralDiag
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        (∫ ω, (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) *
            (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) =
          (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxTraceFormulaData E q hq where
  a := a
  b := b
  coeff_nonpos := hcoeff
  diagonalEntries := fun I =>
    E.principalBoxDiagonalEntriesOfCenteredIntegralDiag q hq I
      (fun j => (if j ∈ I then b else a) * E.profile.eigenvalue j)
      (hdiag I)
  diagVal_eq := by
    intro I j
    rfl

/-- Build the package from diagonal named centered-product formulas. -/
noncomputable def ofCenteredProductMomentDiag
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j j =
          (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxTraceFormulaData E q hq where
  a := a
  b := b
  coeff_nonpos := hcoeff
  diagonalEntries := fun I =>
    E.principalBoxDiagonalEntriesOfCenteredProductMomentDiag q hq I
      (fun j => (if j ∈ I then b else a) * E.profile.eigenvalue j)
      (hdiag I)
  diagVal_eq := by
    intro I j
    rfl

/-- Stronger centered-integral diagonal-plus-upper families also supply the trace package. -/
noncomputable def ofCenteredIntegralAndUpperCenteredIntegral
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        (∫ ω, (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) *
            (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) =
          (if j ∈ I then b else a) * E.profile.eigenvalue j)
    (_hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (∫ ω, (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) *
            (E.Y ω l -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y l) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) = 0) :
    PrincipalBoxTraceFormulaData E q hq :=
  ofCenteredIntegralDiag E q hq a b hcoeff hdiag

/-- Stronger centered-product diagonal-plus-upper families also supply the trace package. -/
noncomputable def ofCenteredProductMomentAndUpperCenteredProductMoment
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j j =
          (if j ∈ I then b else a) * E.profile.eigenvalue j)
    (_hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j l = 0) :
    PrincipalBoxTraceFormulaData E q hq :=
  ofCenteredProductMomentDiag E q hq a b hcoeff hdiag

end PrincipalBoxTraceFormulaData

end EllipticalCore

end Prim.Elliptical
