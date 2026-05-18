import Prim.Elliptical.Core.TraceFormula.Data.Basic
import Prim.Elliptical.Core.TraceFormula.Singleton.Basic
import Prim.Elliptical.Core.TraceFormula.Comparisons.DiagonalEntries

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

namespace PrincipalBoxTraceFormulaData

variable {d : Nat} {E : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}

/-- The packaged diagonal formulas give the affine trace formula on every principal box. -/
theorem preservedTraceOn_eq_affine_eigenSum
    (P : PrincipalBoxTraceFormulaData E q hq) (I : Finset (Prim.Idx d)) :
    E.preservedTraceOn q I =
      P.a * (∑ j, E.profile.eigenvalue j) +
        (P.b - P.a) * E.selectedEigenSum I := by
  exact E.preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries q hq I P.a P.b
    (P.diagonalEntries I) (fun j => P.diagVal_eq I j)

/-- The packaged diagonal formulas give the affine singleton trace formula. -/
theorem singlePreservedTrace_eq_affine_eigenvalue
    (P : PrincipalBoxTraceFormulaData E q hq) (i : Prim.Idx d) :
    E.singlePreservedTrace q i =
      P.a * (∑ j, E.profile.eigenvalue j) +
        (P.b - P.a) * E.profile.eigenvalue i := by
  exact E.singlePreservedTrace_eq_affine_eigenvalue_ofDiagonalEntries q hq i P.a P.b
    (P.diagonalEntries ({i} : Finset (Prim.Idx d)))
    (fun j => by
      simpa using P.diagVal_eq ({i} : Finset (Prim.Idx d)) j)

/-- The packaged trace formula makes singleton preserved trace monotone. -/
theorem singlePreservedTrace_monotone
    (P : PrincipalBoxTraceFormulaData E q hq) :
    Monotone (fun i => E.singlePreservedTrace q i) := by
  exact E.singlePreservedTrace_monotone_ofDiagonalEntries q hq P.a P.b P.coeff_nonpos
    (fun i => P.diagonalEntries ({i} : Finset (Prim.Idx d)))
    (fun i j => by
      simpa using P.diagVal_eq ({i} : Finset (Prim.Idx d)) j)

/-- The first principal coordinate minimizes singleton preserved trace. -/
theorem singlePreservedTrace_first_le
    {n : Nat} {E : EllipticalCore (n + 1)} {q : ℝ} {hq : 0 ≤ q}
    (P : PrincipalBoxTraceFormulaData E q hq) (i : Prim.Idx (n + 1)) :
    E.singlePreservedTrace q 0 ≤ E.singlePreservedTrace q i := by
  exact E.singlePreservedTrace_first_le_ofDiagonalEntries q hq P.a P.b P.coeff_nonpos
    (fun j => P.diagonalEntries ({j} : Finset (Prim.Idx (n + 1))))
    (fun j k => by
      simpa using P.diagVal_eq ({j} : Finset (Prim.Idx (n + 1))) k)
    i

/-- The last principal coordinate maximizes singleton preserved trace. -/
theorem singlePreservedTrace_le_last
    {n : Nat} {E : EllipticalCore (n + 1)} {q : ℝ} {hq : 0 ≤ q}
    (P : PrincipalBoxTraceFormulaData E q hq) (i : Prim.Idx (n + 1)) :
    E.singlePreservedTrace q i ≤ E.singlePreservedTrace q (Fin.last n) := by
  exact E.singlePreservedTrace_le_last_ofDiagonalEntries q hq P.a P.b P.coeff_nonpos
    (fun j => P.diagonalEntries ({j} : Finset (Prim.Idx (n + 1))))
    (fun j k => by
      simpa using P.diagVal_eq ({j} : Finset (Prim.Idx (n + 1))) k)
    i

/-- Canonical leading-set trace anti-monotonicity from the packaged formula. -/
theorem preservedTraceOn_leadingIndexSet_anti_mono
    (P : PrincipalBoxTraceFormulaData E q hq) {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d l) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) := by
  exact E.preservedTraceOn_leadingIndexSet_anti_mono_ofDiagonalEntries q hq P.a P.b
    P.coeff_nonpos P.diagonalEntries P.diagVal_eq hkl

/-- Canonical trailing-set trace anti-monotonicity from the packaged formula. -/
theorem preservedTraceOn_trailingIndexSet_anti_mono
    (P : PrincipalBoxTraceFormulaData E q hq) {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d l) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  exact E.preservedTraceOn_trailingIndexSet_anti_mono_ofDiagonalEntries q hq P.a P.b
    P.coeff_nonpos P.diagonalEntries P.diagVal_eq hkl

/-- Principal-basis leading-set trace anti-monotonicity from the packaged formula. -/
theorem preservedTraceOn_leadingSet_anti_mono
    (P : PrincipalBoxTraceFormulaData E q hq)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (basis.leadingSet l) ≤
      E.preservedTraceOn q (basis.leadingSet k) := by
  exact E.preservedTraceOn_leadingSet_anti_mono_ofDiagonalEntries q hq P.a P.b
    P.coeff_nonpos P.diagonalEntries P.diagVal_eq basis hbasis hkl

/-- Principal-basis trailing-set trace anti-monotonicity from the packaged formula. -/
theorem preservedTraceOn_trailingSet_anti_mono
    (P : PrincipalBoxTraceFormulaData E q hq)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (basis.trailingSet l) ≤
      E.preservedTraceOn q (basis.trailingSet k) := by
  exact E.preservedTraceOn_trailingSet_anti_mono_ofDiagonalEntries q hq P.a P.b
    P.coeff_nonpos P.diagonalEntries P.diagVal_eq basis hbasis hkl

/-- Canonical fixed-cardinality leading-vs-trailing trace comparison. -/
theorem leadingIndexSet_trace_le_trailingIndexSet_trace
    (P : PrincipalBoxTraceFormulaData E q hq) {k : Nat} (hk : k ≤ d) :
    E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  exact E.leadingIndexSet_trace_le_trailingIndexSet_trace_ofDiagonalEntries q hq P.a P.b
    P.coeff_nonpos P.diagonalEntries P.diagVal_eq hk

/-- Principal-basis fixed-cardinality leading-vs-trailing trace comparison. -/
theorem leadingSet_trace_le_trailingSet_trace
    (P : PrincipalBoxTraceFormulaData E q hq)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k : Nat} (hk : k ≤ d) :
    E.preservedTraceOn q (basis.leadingSet k) ≤
      E.preservedTraceOn q (basis.trailingSet k) := by
  exact E.leadingSet_trace_le_trailingSet_trace_ofDiagonalEntries q hq P.a P.b
    P.coeff_nonpos P.diagonalEntries P.diagVal_eq basis hbasis hk

end PrincipalBoxTraceFormulaData

end EllipticalCore

end Prim.Elliptical
