import Prim.Elliptical.Core.BoxOps.Basic
import Prim.Elliptical.Core.PrincipalBasis
import Prim.LinearAlgebra.Majorization.Finite
import Prim.LinearAlgebra.PrincipalBasis.Sets

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)


/--
Selected ordered principal eigenvalue sums are monotone under inclusion.
-/
theorem selectedEigenSum_le_of_subset
    {I J : Finset (Prim.Idx d)} (hIJ : I ⊆ J) :
    E.selectedEigenSum I ≤ E.selectedEigenSum J := by
  dsimp [selectedEigenSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hIJ
    (fun i _ _ => E.profile.lambda_nonneg i)

/--
Selected ordered principal squared-eigenvalue sums are monotone under
inclusion.
-/
theorem selectedEigenSqSum_le_of_subset
    {I J : Finset (Prim.Idx d)} (hIJ : I ⊆ J) :
    E.selectedEigenSqSum I ≤ E.selectedEigenSqSum J := by
  dsimp [selectedEigenSqSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hIJ
    (fun i _ _ => sq_nonneg (E.profile.eigenvalue i))

/-- Squaring preserves the antitone ordering of the nonnegative principal eigenvalues. -/
theorem eigenvalue_sq_antitone {i j : Prim.Idx d} (hij : i ≤ j) :
    (E.profile.eigenvalue j) ^ (2 : Nat) ≤ (E.profile.eigenvalue i) ^ (2 : Nat) := by
  have hle : E.profile.eigenvalue j ≤ E.profile.eigenvalue i :=
    E.profile.lambda_antitone hij
  have hi : 0 ≤ E.profile.eigenvalue i := E.profile.lambda_nonneg i
  have hj : 0 ≤ E.profile.eigenvalue j := E.profile.lambda_nonneg j
  nlinarith

/--
If preserved trace is affine in the selected ordered principal eigenvalue sum
with nonpositive coefficient, then larger selected-eigenvalue sums preserve no
more trace.
-/
theorem preservedTraceOn_le_of_selectedEigenSum_le_of_formula
    (q offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ I, E.preservedTraceOn q I = offset + coeff * E.selectedEigenSum I)
    {I J : Finset (Prim.Idx d)} (hIJ : E.selectedEigenSum J ≤ E.selectedEigenSum I) :
    E.preservedTraceOn q I ≤ E.preservedTraceOn q J := by
  rw [htrace I, htrace J]
  have hMul :
      coeff * E.selectedEigenSum I ≤ coeff * E.selectedEigenSum J :=
    mul_le_mul_of_nonpos_left hIJ hcoeff
  linarith

/-- Larger canonical leading sets preserve no more trace under an affine
selected-eigenvalue trace formula with nonpositive coefficient. -/
theorem preservedTraceOn_leadingIndexSet_anti_mono_of_formula
    (q offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ I, E.preservedTraceOn q I = offset + coeff * E.selectedEigenSum I)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d l) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) := by
  apply E.preservedTraceOn_le_of_selectedEigenSum_le_of_formula q offset coeff hcoeff htrace
  exact E.selectedEigenSum_le_of_subset
    (Prim.LinearAlgebra.leadingIndexSet_subset_leadingIndexSet hkl)

/-- Larger canonical trailing sets preserve no more trace under an affine
selected-eigenvalue trace formula with nonpositive coefficient. -/
theorem preservedTraceOn_trailingIndexSet_anti_mono_of_formula
    (q offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ I, E.preservedTraceOn q I = offset + coeff * E.selectedEigenSum I)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d l) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  apply E.preservedTraceOn_le_of_selectedEigenSum_le_of_formula q offset coeff hcoeff htrace
  exact E.selectedEigenSum_le_of_subset
    (Prim.LinearAlgebra.trailingIndexSet_subset_trailingIndexSet hkl)

/-- Principal-basis leading-set anti-monotonicity under an affine selected-
eigenvalue trace formula with nonpositive coefficient. -/
theorem preservedTraceOn_leadingSet_anti_mono_of_formula
    (q offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ I, E.preservedTraceOn q I = offset + coeff * E.selectedEigenSum I)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (_hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (basis.leadingSet l) ≤
      E.preservedTraceOn q (basis.leadingSet k) := by
  rw [basis.leadingSet_eq_leadingIndexSet, basis.leadingSet_eq_leadingIndexSet]
  exact E.preservedTraceOn_leadingIndexSet_anti_mono_of_formula q offset coeff hcoeff htrace hkl

/-- Principal-basis trailing-set anti-monotonicity under an affine selected-
eigenvalue trace formula with nonpositive coefficient. -/
theorem preservedTraceOn_trailingSet_anti_mono_of_formula
    (q offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ I, E.preservedTraceOn q I = offset + coeff * E.selectedEigenSum I)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (_hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k l : Nat} (hkl : k ≤ l) :
    E.preservedTraceOn q (basis.trailingSet l) ≤
      E.preservedTraceOn q (basis.trailingSet k) := by
  rw [basis.trailingSet_eq_trailingIndexSet, basis.trailingSet_eq_trailingIndexSet]
  exact E.preservedTraceOn_trailingIndexSet_anti_mono_of_formula
    q offset coeff hcoeff htrace hkl

/-- At fixed cardinality, the canonical leading set preserves no more trace
than the canonical trailing set under an affine selected-eigenvalue trace
formula with nonpositive coefficient. -/
theorem leadingIndexSet_trace_le_trailingIndexSet_trace_of_formula
    (q offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ I, E.preservedTraceOn q I = offset + coeff * E.selectedEigenSum I)
    {k : Nat} (hk : k ≤ d) :
    E.preservedTraceOn q (Prim.LinearAlgebra.leadingIndexSet d k) ≤
      E.preservedTraceOn q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  apply E.preservedTraceOn_le_of_selectedEigenSum_le_of_formula q offset coeff hcoeff htrace
  simpa [selectedEigenSum, Prim.LinearAlgebra.leadingPartialSum] using
    (Prim.LinearAlgebra.sum_le_leadingPartialSum_of_card_eq
      E.profile.eigenvalue E.profile.lambda_antitone
      (I := Prim.LinearAlgebra.trailingIndexSet d k)
      (Prim.LinearAlgebra.trailingIndexSet_card hk))

/-- Principal-basis fixed-cardinality leading-versus-trailing trace comparison
under an affine selected-eigenvalue trace formula with nonpositive
coefficient. -/
theorem leadingSet_trace_le_trailingSet_trace_of_formula
    (q offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ I, E.preservedTraceOn q I = offset + coeff * E.selectedEigenSum I)
    (basis : Prim.LinearAlgebra.PrincipalBasisData d)
    (_hbasis : ∀ i, basis.eigenvalue i = E.profile.eigenvalue i)
    {k : Nat} (hk : k ≤ d) :
    E.preservedTraceOn q (basis.leadingSet k) ≤
      E.preservedTraceOn q (basis.trailingSet k) := by
  rw [basis.leadingSet_eq_leadingIndexSet, basis.trailingSet_eq_trailingIndexSet]
  exact E.leadingIndexSet_trace_le_trailingIndexSet_trace_of_formula
    q offset coeff hcoeff htrace hk


end EllipticalCore

end Prim.Elliptical
