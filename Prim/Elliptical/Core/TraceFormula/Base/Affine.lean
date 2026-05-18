import Prim.Elliptical.Core.PrincipalBasis
import Prim.Elliptical.Core.TraceFormula.Base.Witness

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/--
Explicit affine trace formula on a principal box from diagonal covariance
identities alone.
-/
theorem preservedTraceOn_eq_affine_eigenSum_ofDiagEq
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) (a b : ℝ)
    (hdiag :
      ∀ i,
        E.preservedCovOn q hq I i i =
          (if i ∈ I then b else a) * E.profile.eigenvalue i) :
    E.preservedTraceOn q I =
      a * (∑ j, E.profile.eigenvalue j) +
        (b - a) * Finset.sum I (fun j => E.profile.eigenvalue j) := by
  calc
    E.preservedTraceOn q I
        = ∑ i, ((if i ∈ I then b else a) * E.profile.eigenvalue i) := by
            exact E.preservedTraceOn_eq_sum_diagVal_ofDiagEq q hq I
              (fun i => (if i ∈ I then b else a) * E.profile.eigenvalue i) hdiag
    _ = a * (∑ j, E.profile.eigenvalue j) +
          (b - a) * Finset.sum I (fun j => E.profile.eigenvalue j) := by
          simp_rw [show ∀ j : Prim.Idx d,
              (if j ∈ I then b else a) * E.profile.eigenvalue j =
                a * E.profile.eigenvalue j +
                  (b - a) * if j ∈ I then E.profile.eigenvalue j else 0
              from fun j => by split_ifs <;> ring,
            Finset.sum_add_distrib, ← Finset.mul_sum]
          have hsum :
              (∑ j, if j ∈ I then E.profile.eigenvalue j else 0) =
                Finset.sum I (fun j => E.profile.eigenvalue j) := by
            exact Finset.sum_ite_mem_eq I (fun j => E.profile.eigenvalue j)
          simp [hsum]

/--
Explicit affine trace formula on a principal box from diagonal centered
integral formulas alone.
-/
theorem preservedTraceOn_eq_affine_eigenSum_ofCenteredIntegralDiag
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) (a b : ℝ)
    (hdiag :
      ∀ i,
        (∫ ω, (E.Y ω i -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y i) *
            (E.Y ω i -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y i) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) =
          (if i ∈ I then b else a) * E.profile.eigenvalue i) :
    E.preservedTraceOn q I =
      a * (∑ j, E.profile.eigenvalue j) +
        (b - a) * Finset.sum I (fun j => E.profile.eigenvalue j) := by
  calc
    E.preservedTraceOn q I
        = ∑ i, ((if i ∈ I then b else a) * E.profile.eigenvalue i) := by
            exact E.preservedTraceOn_eq_sum_diagVal_ofCenteredIntegralDiag q hq I
              (fun i => (if i ∈ I then b else a) * E.profile.eigenvalue i) hdiag
    _ = a * (∑ j, E.profile.eigenvalue j) +
          (b - a) * Finset.sum I (fun j => E.profile.eigenvalue j) := by
          simp_rw [show ∀ j : Prim.Idx d,
              (if j ∈ I then b else a) * E.profile.eigenvalue j =
                a * E.profile.eigenvalue j +
                  (b - a) * if j ∈ I then E.profile.eigenvalue j else 0
              from fun j => by split_ifs <;> ring,
            Finset.sum_add_distrib, ← Finset.mul_sum]
          have hsum :
              (∑ j, if j ∈ I then E.profile.eigenvalue j else 0) =
                Finset.sum I (fun j => E.profile.eigenvalue j) := by
            exact Finset.sum_ite_mem_eq I (fun j => E.profile.eigenvalue j)
          simp [hsum]

/--
Explicit affine trace formula on a principal box from diagonal named
centered-product formulas alone.
-/
theorem preservedTraceOn_eq_affine_eigenSum_ofCenteredProductMomentDiag
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) (a b : ℝ)
    (hdiag :
      ∀ i,
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I i i =
          (if i ∈ I then b else a) * E.profile.eigenvalue i) :
    E.preservedTraceOn q I =
      a * (∑ j, E.profile.eigenvalue j) +
        (b - a) * Finset.sum I (fun j => E.profile.eigenvalue j) := by
  calc
    E.preservedTraceOn q I
        = ∑ i, ((if i ∈ I then b else a) * E.profile.eigenvalue i) := by
            exact E.preservedTraceOn_eq_sum_diagVal_ofCenteredProductMomentDiag q hq I
              (fun i => (if i ∈ I then b else a) * E.profile.eigenvalue i) hdiag
    _ = a * (∑ j, E.profile.eigenvalue j) +
          (b - a) * Finset.sum I (fun j => E.profile.eigenvalue j) := by
          simp_rw [show ∀ j : Prim.Idx d,
              (if j ∈ I then b else a) * E.profile.eigenvalue j =
                a * E.profile.eigenvalue j +
                  (b - a) * if j ∈ I then E.profile.eigenvalue j else 0
              from fun j => by split_ifs <;> ring,
            Finset.sum_add_distrib, ← Finset.mul_sum]
          have hsum :
              (∑ j, if j ∈ I then E.profile.eigenvalue j else 0) =
                Finset.sum I (fun j => E.profile.eigenvalue j) := by
            exact Finset.sum_ite_mem_eq I (fun j => E.profile.eigenvalue j)
          simp [hsum]

/--
Explicit affine trace formula on a principal box from a packaged diagonal-entry
witness.
-/
theorem preservedTraceOn_eq_affine_eigenSum_ofDiagonalEntries
    (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) (a b : ℝ)
    (D : (E.principalBoxData q hq).PreservedCovarianceDiagonalEntries E.μ E.Y I)
    (hdiag :
      ∀ i, D.diagVal i = (if i ∈ I then b else a) * E.profile.eigenvalue i) :
    E.preservedTraceOn q I =
      a * (∑ j, E.profile.eigenvalue j) +
        (b - a) * E.selectedEigenSum I := by
  calc
    E.preservedTraceOn q I = (E.principalBoxData q hq).preservedTrace E.μ E.Y I := by
      rw [E.preservedTraceOn_eq q hq I]
    _ = ∑ i, D.diagVal i := by
      exact D.preservedTrace_eq_sum_diagVal
    _ = ∑ i, ((if i ∈ I then b else a) * E.profile.eigenvalue i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hdiag i
    _ = a * (∑ j, E.profile.eigenvalue j) +
          (b - a) * E.selectedEigenSum I := by
      simp_rw [show ∀ j : Prim.Idx d,
          (if j ∈ I then b else a) * E.profile.eigenvalue j =
            a * E.profile.eigenvalue j +
              (b - a) * if j ∈ I then E.profile.eigenvalue j else 0
          from fun j => by split_ifs <;> ring,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      have hsum :
          (∑ j, if j ∈ I then E.profile.eigenvalue j else 0) =
            E.selectedEigenSum I := by
        exact Finset.sum_ite_mem_eq I (fun j => E.profile.eigenvalue j)
      simp [selectedEigenSum, hsum]

end EllipticalCore

end Prim.Elliptical
