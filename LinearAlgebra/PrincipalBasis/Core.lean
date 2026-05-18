import Prim.Basic
import Mathlib.Data.Real.Sqrt

namespace Prim.LinearAlgebra

open scoped BigOperators

/--
Principal-basis data for the covariance structure under study.

At this layer we only record the ordered eigenvalue profile together with an
abstract change-of-basis matrix witnessing that we have moved into principal
coordinates.
-/
structure PrincipalBasisData (d : Nat) where
  eigenvalue : Prim.Idx d → ℝ
  lambda_nonneg : ∀ i, 0 ≤ eigenvalue i
  lambda_antitone : Antitone eigenvalue
  basisMatrix : Prim.Mat d
  orthogonalBasis : Prop
  diagonalizesCovariance : Prop

namespace PrincipalBasisData

variable {d : Nat} (B : PrincipalBasisData d)

/-- Sum of the eigenvalues selected by a finite coordinate set. -/
def selectedEigenSum (B : PrincipalBasisData d) (I : Finset (Prim.Idx d)) : ℝ :=
  Finset.sum I (fun i => B.eigenvalue i)

/-- Product of the selected eigenvalues. -/
def selectedEigenProd (B : PrincipalBasisData d) (I : Finset (Prim.Idx d)) : ℝ :=
  Finset.prod I (fun i => B.eigenvalue i)

/-- Product of the square roots of the selected eigenvalues. -/
noncomputable def selectedEigenSqrtProd (B : PrincipalBasisData d) (I : Finset (Prim.Idx d)) : ℝ :=
  Finset.prod I (fun i => Real.sqrt (B.eigenvalue i))

/-- Sum of squared selected eigenvalues. -/
def selectedEigenSqSum (B : PrincipalBasisData d) (I : Finset (Prim.Idx d)) : ℝ :=
  Finset.sum I (fun i => (B.eigenvalue i) ^ (2 : Nat))

/-- First `k` principal coordinates, i.e. the largest ordered eigenvalues. -/
def leadingSet (_ : PrincipalBasisData d) (k : Nat) : Finset (Prim.Idx d) :=
  Finset.univ.filter (fun i => i.1 < k)

/-- Last `k` principal coordinates, i.e. the smallest ordered eigenvalues. -/
def trailingSet (_ : PrincipalBasisData d) (k : Nat) : Finset (Prim.Idx d) :=
  Finset.univ.filter (fun i => d - k ≤ i.1)

theorem mem_leadingSet {k : Nat} {i : Prim.Idx d} :
    i ∈ B.leadingSet k ↔ i.1 < k := by
  simp [PrincipalBasisData.leadingSet]

theorem mem_trailingSet {k : Nat} {i : Prim.Idx d} :
    i ∈ B.trailingSet k ↔ d - k ≤ i.1 := by
  simp [PrincipalBasisData.trailingSet]

theorem selectedEigenSum_empty :
    B.selectedEigenSum ∅ = 0 := by
  simp [PrincipalBasisData.selectedEigenSum]

theorem selectedEigenProd_empty :
    B.selectedEigenProd ∅ = 1 := by
  simp [PrincipalBasisData.selectedEigenProd]

theorem selectedEigenSqrtProd_empty :
    B.selectedEigenSqrtProd ∅ = 1 := by
  simp [PrincipalBasisData.selectedEigenSqrtProd]

theorem selectedEigenSqSum_empty :
    B.selectedEigenSqSum ∅ = 0 := by
  simp [PrincipalBasisData.selectedEigenSqSum]

theorem selectedEigenSum_singleton (i : Prim.Idx d) :
    B.selectedEigenSum ({i} : Finset (Prim.Idx d)) = B.eigenvalue i := by
  simp [PrincipalBasisData.selectedEigenSum]

end PrincipalBasisData

end Prim.LinearAlgebra
