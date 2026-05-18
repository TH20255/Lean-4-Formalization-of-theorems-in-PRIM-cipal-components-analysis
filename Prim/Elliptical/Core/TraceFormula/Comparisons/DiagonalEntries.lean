import Prim.Elliptical.Core.TraceFormula.Base.Affine
import Prim.Elliptical.Core.TraceFormula.Comparisons.Generic

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/-- Packaged diagonal-entry witnesses imply canonical leading-set trace
anti-monotonicity. -/
theorem preservedTraceOn_leadingIndexSet_anti_mono_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ I,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I)
    (hdiag :
      ∀ I j, (hentries I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d l) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) := by
  exact E.preservedTraceOn_leadingIndexSet_anti_mono_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun I =>
      E.preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries q hq I a b
        (hentries I) (fun j => hdiag I j))
    hkl

/-- Packaged diagonal-entry witnesses imply canonical trailing-set trace
anti-monotonicity. -/
theorem preservedTraceOn_trailingIndexSet_anti_mono_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ I,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I)
    (hdiag :
      ∀ I j, (hentries I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d l) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  exact E.preservedTraceOn_trailingIndexSet_anti_mono_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun I =>
      E.preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries q hq I a b
        (hentries I) (fun j => hdiag I j))
    hkl

/-- Packaged diagonal-entry witnesses imply principal-basis leading-set trace
anti-monotonicity. -/
theorem preservedTraceOn_leadingSet_anti_mono_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ I,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I)
    (hdiag :
      ∀ I j, (hentries I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (basis.leadingSet l) ≤
      E.preservedTraceOn q (basis.leadingSet k) := by
  exact E.preservedTraceOn_leadingSet_anti_mono_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun I =>
      E.preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries q hq I a b
        (hentries I) (fun j => hdiag I j))
    basis hbasis hkl

/-- Packaged diagonal-entry witnesses imply principal-basis trailing-set trace
anti-monotonicity. -/
theorem preservedTraceOn_trailingSet_anti_mono_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ I,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I)
    (hdiag :
      ∀ I j, (hentries I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (basis.trailingSet l) ≤
      E.preservedTraceOn q (basis.trailingSet k) := by
  exact E.preservedTraceOn_trailingSet_anti_mono_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun I =>
      E.preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries q hq I a b
        (hentries I) (fun j => hdiag I j))
    basis hbasis hkl

/-- Packaged diagonal-entry witnesses imply canonical leading-versus-trailing
trace comparison. -/
theorem leadingIndexSet_trace_le_trailingIndexSet_trace_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ I,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I)
    (hdiag :
      ∀ I j, (hentries I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j)
    {k : Nat} (hk : k ≤ d) :
    E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  exact E.leadingIndexSet_trace_le_trailingIndexSet_trace_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun I =>
      E.preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries q hq I a b
        (hentries I) (fun j => hdiag I j))
    hk

/-- Packaged diagonal-entry witnesses imply principal-basis
leading-versus-trailing trace comparison. -/
theorem leadingSet_trace_le_trailingSet_trace_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ I,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I)
    (hdiag :
      ∀ I j, (hentries I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k : Nat} (hk : k ≤ d) :
    E.preservedTraceOn q (basis.leadingSet k) ≤
      E.preservedTraceOn q (basis.trailingSet k) := by
  exact E.leadingSet_trace_le_trailingSet_trace_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun I =>
      E.preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries q hq I a b
        (hentries I) (fun j => hdiag I j))
    basis hbasis hk



end EllipticalCore

end Prim.Elliptical
