import Prim.Elliptical.Core.CenteredFormula.IntegralDiagUpper.Basic
import Prim.Elliptical.Core.CenteredFormula.ProductDiagUpper.Basic

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

/--
Source-facing package for the post-representation principal-box covariance
calculation.

It says that every principal-box preserved covariance matrix is diagonal and
that its diagonal entries have the standard affine-eigenvalue form.  From this
single package Lean can recover both centered-product and centered-integral
diagonal+upper formula objects used by the canonical theorem chain.
-/
structure PrincipalBoxDiagonalCovarianceFamily
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) where
  a : ℝ
  b : ℝ
  coeff_nonpos : b - a ≤ 0
  diagonal :
    ∀ I, (E.principalBoxData q hq).DiagonalPreservedCovariance E.μ E.Y I
  diagVal :
    ∀ I j, (diagonal I).diagVal j =
      (if j ∈ I then b else a) * E.profile.eigenvalue j

namespace PrincipalBoxDiagonalCovarianceFamily

variable {d : Nat} {E : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}

/-- Package an already-proved diagonal covariance family. -/
noncomputable def ofDiagonalPreservedCovarianceFamily
    (a b : ℝ) (hcoeff : b - a ≤ 0)
    (D :
      ∀ I,
        (E.principalBoxData q hq).DiagonalPreservedCovariance E.μ E.Y I)
    (hdiagVal :
      ∀ I j, (D I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxDiagonalCovarianceFamily E q hq where
  a := a
  b := b
  coeff_nonpos := hcoeff
  diagonal := D
  diagVal := hdiagVal

/-- Convert the diagonal covariance family to the centered-product formula package. -/
noncomputable def toProductMomentDiagUpperFormula
    (F : PrincipalBoxDiagonalCovarianceFamily E q hq) :
    PrincipalBoxCenteredProductMomentDiagUpperFormula E q hq :=
  PrincipalBoxCenteredProductMomentDiagUpperFormula.ofDiagonalPreservedCovarianceFamily
    F.a F.b F.coeff_nonpos F.diagonal F.diagVal

/-- Convert the diagonal covariance family to the centered-integral formula package. -/
noncomputable def toIntegralDiagUpperFormula
    (F : PrincipalBoxDiagonalCovarianceFamily E q hq) :
    PrincipalBoxCenteredIntegralDiagUpperFormula E q hq :=
  PrincipalBoxCenteredIntegralDiagUpperFormula.ofDiagonalPreservedCovarianceFamily
    F.a F.b F.coeff_nonpos F.diagonal F.diagVal

@[simp] theorem toProductMomentDiagUpperFormula_diag_a
    (F : PrincipalBoxDiagonalCovarianceFamily E q hq) :
    F.toProductMomentDiagUpperFormula.diag.a = F.a := rfl

@[simp] theorem toProductMomentDiagUpperFormula_diag_b
    (F : PrincipalBoxDiagonalCovarianceFamily E q hq) :
    F.toProductMomentDiagUpperFormula.diag.b = F.b := rfl

@[simp] theorem toIntegralDiagUpperFormula_diag_a
    (F : PrincipalBoxDiagonalCovarianceFamily E q hq) :
    F.toIntegralDiagUpperFormula.diag.a = F.a := rfl

@[simp] theorem toIntegralDiagUpperFormula_diag_b
    (F : PrincipalBoxDiagonalCovarianceFamily E q hq) :
    F.toIntegralDiagUpperFormula.diag.b = F.b := rfl

end PrincipalBoxDiagonalCovarianceFamily

end EllipticalCore

end Prim.Elliptical
