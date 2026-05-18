import Prim.Elliptical.Core.TraceFormula.Base.Affine

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/-- Explicit affine singleton trace formula from a packaged diagonal-entry
witness. -/
theorem singlePreservedTrace_eq_affine_eigenvalue_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (i : Prim.Idx d) (a b : ℝ)
    (D :
      (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y
        ({i} : Finset (Prim.Idx d)))
    (hdiag :
      ∀ j, D.diagVal j = (if j = i then b else a) * E.profile.eigenvalue j) :
    E.singlePreservedTrace q i =
      a * (∑ j, E.profile.eigenvalue j) + (b - a) * E.profile.eigenvalue i := by
  calc
    E.singlePreservedTrace q i = E.preservedTraceOn q ({i} : Finset (Prim.Idx d)) := by
      rw [E.singlePreservedTrace_eq_preservedTraceOn_singleton q i]
    _ = a * (∑ j, E.profile.eigenvalue j) +
          (b - a) * E.selectedEigenSum ({i} : Finset (Prim.Idx d)) := by
      exact E.preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries
        q hq ({i} : Finset (Prim.Idx d)) a b D (by
          intro j
          simpa using hdiag j)
    _ = a * (∑ j, E.profile.eigenvalue j) + (b - a) * E.profile.eigenvalue i := by
      simp [selectedEigenSum]

/--
Single-coordinate preserved trace is monotone whenever it is affine in the
ordered principal eigenvalue profile with nonpositive coefficient.
-/
theorem singlePreservedTrace_monotone_of_formula
    (q offset coeff : ℝ) (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ i, E.singlePreservedTrace q i = offset + coeff * E.profile.eigenvalue i) :
    Monotone (fun i => E.singlePreservedTrace q i) := by
  intro i j hij
  dsimp
  rw [htrace i, htrace j]
  have hEig : E.profile.eigenvalue j ≤ E.profile.eigenvalue i :=
    E.profile.lambda_antitone hij
  have hMul :
      coeff * E.profile.eigenvalue i ≤ coeff * E.profile.eigenvalue j :=
    mul_le_mul_of_nonpos_left hEig hcoeff
  linarith

/-- The first principal coordinate minimizes any affine singleton trace profile
with nonpositive coefficient. -/
theorem singlePreservedTrace_first_le_of_formula
    {n : Nat} (E : EllipticalCore (n + 1)) (q offset coeff : ℝ)
    (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ i, E.singlePreservedTrace q i = offset + coeff * E.profile.eigenvalue i)
    (i : Prim.Idx (n + 1)) :
    E.singlePreservedTrace q 0 ≤ E.singlePreservedTrace q i := by
  exact E.singlePreservedTrace_monotone_of_formula q offset coeff hcoeff htrace
    (Fin.zero_le i)

/-- The last principal coordinate maximizes any affine singleton trace profile
with nonpositive coefficient. -/
theorem singlePreservedTrace_le_last_of_formula
    {n : Nat} (E : EllipticalCore (n + 1)) (q offset coeff : ℝ)
    (hcoeff : coeff ≤ 0)
    (htrace :
      ∀ i, E.singlePreservedTrace q i = offset + coeff * E.profile.eigenvalue i)
    (i : Prim.Idx (n + 1)) :
    E.singlePreservedTrace q i ≤ E.singlePreservedTrace q (Fin.last n) := by
  exact E.singlePreservedTrace_monotone_of_formula q offset coeff hcoeff htrace
    (Fin.le_last i)

/-- Packaged diagonal-entry witnesses imply monotonicity of the singleton box
trace profile. -/
theorem singlePreservedTrace_monotone_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ i,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y
          ({i} : Finset (Prim.Idx d)))
    (hdiag :
      ∀ i j, (hentries i).diagVal j =
        (if j = i then b else a) * E.profile.eigenvalue j) :
    Monotone (fun i => E.singlePreservedTrace q i) := by
  exact E.singlePreservedTrace_monotone_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun i =>
      E.singlePreservedTrace_eq_affine_eigenvalue_ofDiagonalEntries q hq i a b
        (hentries i) (fun j => hdiag i j))

/-- Packaged diagonal-entry witnesses make the first principal coordinate
minimize singleton preserved trace. -/
theorem singlePreservedTrace_first_le_ofDiagonalEntries
    {n : Nat} (E : EllipticalCore (n + 1)) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ i,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y
          ({i} : Finset (Prim.Idx (n + 1))))
    (hdiag :
      ∀ i j, (hentries i).diagVal j =
        (if j = i then b else a) * E.profile.eigenvalue j)
    (i : Prim.Idx (n + 1)) :
    E.singlePreservedTrace q 0 ≤ E.singlePreservedTrace q i := by
  exact E.singlePreservedTrace_first_le_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun j =>
      E.singlePreservedTrace_eq_affine_eigenvalue_ofDiagonalEntries q hq j a b
        (hentries j) (fun k => hdiag j k))
    i

/-- Packaged diagonal-entry witnesses make the last principal coordinate
maximize singleton preserved trace. -/
theorem singlePreservedTrace_le_last_ofDiagonalEntries
    {n : Nat} (E : EllipticalCore (n + 1)) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (hcoeff : b - a ≤ 0)
    (hentries :
      ∀ i,
        (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y
          ({i} : Finset (Prim.Idx (n + 1))))
    (hdiag :
      ∀ i j, (hentries i).diagVal j =
        (if j = i then b else a) * E.profile.eigenvalue j)
    (i : Prim.Idx (n + 1)) :
    E.singlePreservedTrace q i ≤ E.singlePreservedTrace q (Fin.last n) := by
  exact E.singlePreservedTrace_le_last_of_formula q
    (a * ∑ j, E.profile.eigenvalue j) (b - a) hcoeff
    (fun j =>
      E.singlePreservedTrace_eq_affine_eigenvalue_ofDiagonalEntries q hq j a b
        (hentries j) (fun k => hdiag j k))
    i


end EllipticalCore

end Prim.Elliptical
