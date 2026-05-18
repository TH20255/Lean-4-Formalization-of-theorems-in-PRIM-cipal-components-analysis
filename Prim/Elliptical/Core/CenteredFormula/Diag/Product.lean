import Prim.Elliptical.Core.TraceFormula.Data.Comparisons

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/--
Source-facing package for principal-box diagonal centered-product trace
formulas.
-/
structure PrincipalBoxCenteredProductMomentDiagFormula
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) where
  a : ℝ
  b : ℝ
  coeff_nonpos : b - a ≤ 0
  formula :
    ∀ I j,
      (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j

namespace PrincipalBoxCenteredProductMomentDiagFormula

variable {d : Nat} {E : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}

/-- Build the centered-product formula object from its raw diagonal formula. -/
noncomputable def ofFormula
    (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j j =
          (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxCenteredProductMomentDiagFormula E q hq where
  a := a
  b := b
  coeff_nonpos := hcoeff
  formula := hdiag

/--
Build the centered-product diagonal formula object from conditioned mean-zero
identities and raw second-moment identities.
-/
noncomputable def ofMeanZeroAndRawSecondMoment
    (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hmean :
      ∀ I j,
        Prim.Probability.meanVec d
          (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I))
          E.Y j = 0)
    (hsecond :
      ∀ I j,
        (∫ ω, E.Y ω j * E.Y ω j ∂
          Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) =
          (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxCenteredProductMomentDiagFormula E q hq :=
  ofFormula a b hcoeff
    (fun I j => by
      simpa [Prim.Probability.CentralBoxData.preservedCenteredProductMoment] using
        Prim.Probability.preservedCenteredProductMoment_diag_eq_of_mean_zero_and_integral
          d E.μ ((E.principalBoxData q hq).event E.Y I) E.Y j
          (hmean I j) (hsecond I j))

/--
Stronger centered-product diagonal-plus-upper families also supply the
diagonal formula object used by the trace/profile routes.
-/
noncomputable def ofCenteredProductMomentAndUpperCenteredProductMoment
    (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j j =
          (if j ∈ I then b else a) * E.profile.eigenvalue j)
    (_hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j l = 0) :
    PrincipalBoxCenteredProductMomentDiagFormula E q hq :=
  ofFormula a b hcoeff hdiag

/-- Convert the centered-product formula object to the reusable affine trace package. -/
noncomputable def toTraceFormulaData
    (D : PrincipalBoxCenteredProductMomentDiagFormula E q hq) :
    PrincipalBoxTraceFormulaData E q hq :=
  PrincipalBoxTraceFormulaData.ofCenteredProductMomentDiag E q hq
    D.a D.b D.coeff_nonpos D.formula

/-- The packaged diagonal centered-product formula gives the affine trace formula. -/
theorem preservedTraceOn_eq_affine_eigenSum
    (D : PrincipalBoxCenteredProductMomentDiagFormula E q hq) (I : Finset (Prim.Idx d)) :
    E.preservedTraceOn q I =
      D.a * (∑ j, E.profile.eigenvalue j) +
        (D.b - D.a) * E.selectedEigenSum I :=
  D.toTraceFormulaData.preservedTraceOn_eq_affine_eigenSum I

/-- The centered-product formula object makes singleton preserved trace monotone. -/
theorem singlePreservedTrace_monotone
    (D : PrincipalBoxCenteredProductMomentDiagFormula E q hq) :
    Monotone (fun i => E.singlePreservedTrace q i) :=
  D.toTraceFormulaData.singlePreservedTrace_monotone

/-- The first principal coordinate minimizes singleton preserved trace. -/
theorem singlePreservedTrace_first_le
    {n : Nat} {E : EllipticalCore (n + 1)} {q : ℝ} {hq : 0 ≤ q}
    (D : PrincipalBoxCenteredProductMomentDiagFormula E q hq) (i : Prim.Idx (n + 1)) :
    E.singlePreservedTrace q 0 ≤ E.singlePreservedTrace q i :=
  D.toTraceFormulaData.singlePreservedTrace_first_le i

/-- The last principal coordinate maximizes singleton preserved trace. -/
theorem singlePreservedTrace_le_last
    {n : Nat} {E : EllipticalCore (n + 1)} {q : ℝ} {hq : 0 ≤ q}
    (D : PrincipalBoxCenteredProductMomentDiagFormula E q hq) (i : Prim.Idx (n + 1)) :
    E.singlePreservedTrace q i ≤ E.singlePreservedTrace q (Fin.last n) :=
  D.toTraceFormulaData.singlePreservedTrace_le_last i

/-- Canonical fixed-cardinality leading-vs-trailing trace comparison. -/
theorem leadingIndexSet_trace_le_trailingIndexSet_trace
    (D : PrincipalBoxCenteredProductMomentDiagFormula E q hq) {k : Nat} (hk : k ≤ d) :
    E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) :=
  D.toTraceFormulaData.leadingIndexSet_trace_le_trailingIndexSet_trace hk

/-- Principal-basis fixed-cardinality leading-vs-trailing trace comparison. -/
theorem leadingSet_trace_le_trailingSet_trace
    (D : PrincipalBoxCenteredProductMomentDiagFormula E q hq)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k : Nat} (hk : k ≤ d) :
    E.preservedTraceOn q (basis.leadingSet k) ≤
      E.preservedTraceOn q (basis.trailingSet k) :=
  D.toTraceFormulaData.leadingSet_trace_le_trailingSet_trace basis hbasis hk

end PrincipalBoxCenteredProductMomentDiagFormula

end EllipticalCore

end Prim.Elliptical
