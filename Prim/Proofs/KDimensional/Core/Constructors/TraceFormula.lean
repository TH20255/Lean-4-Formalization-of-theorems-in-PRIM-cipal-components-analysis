import Prim.Elliptical.Core.CenteredFormula.Diag.Integral
import Prim.Elliptical.Core.CenteredFormula.Diag.Product
import Prim.LinearAlgebra.PrincipalBasis.Sets
import Prim.Proofs.KDimensional.Core.Base.Basic

namespace Prim.Proofs

open scoped BigOperators
open Prim.Elliptical

/--
Construct a `k`-dimensional trace profile directly from the principal-box
affine trace package.

This is the shortest proof-side landing point for the downstream theorem
chain after the stochastic-representation layer has packaged the principal-box
diagonal trace formula.
-/
noncomputable def KDimensionalProfile.ofPrincipalBoxTraceFormulaData
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (P : EllipticalCore.PrincipalBoxTraceFormulaData core q hq) :
    KDimensionalProfile d where
  core := core
  q := q
  offset := P.a * ∑ j, core.profile.eigenvalue j
  coeff := P.b - P.a
  coeff_nonpos := P.coeff_nonpos
  trace_formula := by
    intro I
    simpa [eigenSum, EllipticalCore.selectedEigenSum] using
      P.preservedTraceOn_eq_affine_eigenSum I

/-- Construct a trace profile directly from a principal-box centered-integral formula object. -/
noncomputable def KDimensionalProfile.ofPrincipalBoxCenteredIntegralDiagFormula
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (D : EllipticalCore.PrincipalBoxCenteredIntegralDiagFormula core q hq) :
    KDimensionalProfile d :=
  KDimensionalProfile.ofPrincipalBoxTraceFormulaData D.toTraceFormulaData

/-- Construct a trace profile directly from a principal-box centered-product formula object. -/
noncomputable def KDimensionalProfile.ofPrincipalBoxCenteredProductMomentDiagFormula
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (D : EllipticalCore.PrincipalBoxCenteredProductMomentDiagFormula core q hq) :
    KDimensionalProfile d :=
  KDimensionalProfile.ofPrincipalBoxTraceFormulaData D.toTraceFormulaData

/-- Direct affine trace formula from the principal-box trace package. -/
theorem KDimensionalProfile.preservedTraceOn_eq_affine_eigenSum_ofPrincipalBoxTraceFormulaData
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (P : EllipticalCore.PrincipalBoxTraceFormulaData core q hq)
    (I : Finset (Prim.Idx d)) :
    core.preservedTraceOn q I =
      P.a * ∑ j, core.profile.eigenvalue j + (P.b - P.a) * eigenSum core I := by
  simpa [eigenSum, EllipticalCore.selectedEigenSum] using
    P.preservedTraceOn_eq_affine_eigenSum I

/-- Direct canonical leading-set anti-monotonicity from the principal-box trace package. -/
theorem KDimensionalProfile.preservedTraceOn_leadingIndexSet_anti_mono_ofPrincipalBoxTraceFormulaData
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (P : EllipticalCore.PrincipalBoxTraceFormulaData core q hq)
    {k l : Nat} (hkl : k ≤ l) :
    core.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d l) ≤
      core.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) := by
  exact P.preservedTraceOn_leadingIndexSet_anti_mono hkl

/-- Direct canonical trailing-set anti-monotonicity from the principal-box trace package. -/
theorem KDimensionalProfile.preservedTraceOn_trailingIndexSet_anti_mono_ofPrincipalBoxTraceFormulaData
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (P : EllipticalCore.PrincipalBoxTraceFormulaData core q hq)
    {k l : Nat} (hkl : k ≤ l) :
    core.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d l) ≤
      core.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  exact P.preservedTraceOn_trailingIndexSet_anti_mono hkl

/-- Direct principal-basis leading-set anti-monotonicity from the principal-box trace package. -/
theorem KDimensionalProfile.preservedTraceOn_leadingSet_anti_mono_ofPrincipalBoxTraceFormulaData
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (P : EllipticalCore.PrincipalBoxTraceFormulaData core q hq)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = core.profile.eigenvalue i)
    {k l : Nat} (hkl : k ≤ l) :
    core.preservedTraceOn q (basis.leadingSet l) ≤
      core.preservedTraceOn q (basis.leadingSet k) := by
  exact P.preservedTraceOn_leadingSet_anti_mono basis hbasis hkl

/-- Direct principal-basis trailing-set anti-monotonicity from the principal-box trace package. -/
theorem KDimensionalProfile.preservedTraceOn_trailingSet_anti_mono_ofPrincipalBoxTraceFormulaData
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (P : EllipticalCore.PrincipalBoxTraceFormulaData core q hq)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = core.profile.eigenvalue i)
    {k l : Nat} (hkl : k ≤ l) :
    core.preservedTraceOn q (basis.trailingSet l) ≤
      core.preservedTraceOn q (basis.trailingSet k) := by
  exact P.preservedTraceOn_trailingSet_anti_mono basis hbasis hkl

/-- Direct canonical leading-vs-trailing comparison from the principal-box trace package. -/
theorem KDimensionalProfile.leadingIndexSet_trace_le_trailingIndexSet_trace_ofPrincipalBoxTraceFormulaData
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (P : EllipticalCore.PrincipalBoxTraceFormulaData core q hq)
    {k : Nat} (hk : k ≤ d) :
    core.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) ≤
      core.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  exact P.leadingIndexSet_trace_le_trailingIndexSet_trace hk

/-- Direct principal-basis leading-vs-trailing comparison from the principal-box trace package. -/
theorem KDimensionalProfile.leadingSet_trace_le_trailingSet_trace_ofPrincipalBoxTraceFormulaData
    {d : Nat} {core : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}
    (P : EllipticalCore.PrincipalBoxTraceFormulaData core q hq)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (hbasis : ∀ i, basis.eigenvalue i = core.profile.eigenvalue i)
    {k : Nat} (hk : k ≤ d) :
    core.preservedTraceOn q (basis.leadingSet k) ≤
      core.preservedTraceOn q (basis.trailingSet k) := by
  exact P.leadingSet_trace_le_trailingSet_trace basis hbasis hk

end Prim.Proofs
