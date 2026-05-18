import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Core.Diagonal.Weighted

/-!
Ambient sign-symmetry and angular-second-moment formula packages.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}
/-- A sign-flip symmetry for the source-facing `R * O_j` integrand under a
fixed rotated representation-coordinate conditioned measure. -/
def rotatedRepPeelROSignSymmetry
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j : Prim.Idx d) : Prop :=
  ∃ τ : MeasurableEquiv diagonal.core.Ω diagonal.core.Ω,
    MeasurePreserving τ
      (Prim.Probability.condOn diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I))
      (Prim.Probability.condOn diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I)) ∧
    Filter.EventuallyEq
      (ae
        (Prim.Probability.condOn diagonal.core.μ
          (rotatedRepPeelEvent diagonal U I)))
      (fun ω => diagonal.core.R (τ ω) * diagonal.core.O (τ ω) j)
      (fun ω => - (diagonal.core.R ω * diagonal.core.O ω j))

/-- Ambient version of the source-facing `R * O_j` sign symmetry.

This is the shape future analytic proofs should normally produce: a symmetry
of the original measure, an a.e.-invariant rotated-representation peeling
event, and an ambient oddness statement for the integrand.  It can be
transported mechanically to `rotatedRepPeelROSignSymmetry`.
-/
def rotatedRepPeelROAmbientSignSymmetry
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j : Prim.Idx d) : Prop :=
  ∃ τ : MeasurableEquiv diagonal.core.Ω diagonal.core.Ω,
    MeasurePreserving τ diagonal.core.μ diagonal.core.μ ∧
    Filter.EventuallyEq (ae diagonal.core.μ)
      (Set.preimage τ (rotatedRepPeelEvent diagonal U I))
      (rotatedRepPeelEvent diagonal U I) ∧
    Filter.EventuallyEq (ae diagonal.core.μ)
      (fun ω => diagonal.core.R (τ ω) * diagonal.core.O (τ ω) j)
      (fun ω => - (diagonal.core.R ω * diagonal.core.O ω j))

/--
Build the conditioned `R * O_j` sign symmetry from ambient symmetry data.

Future spherical arguments can now work with the natural ambient facts:
the sign flip preserves the original measure, preserves the rotated
representation-coordinate peeling event up to a.e. equality, and flips the
`R * O_j` integrand a.e.  This lemma transports those facts to the conditioned
measure required by `rotatedRepPeelROSignSymmetry`.
-/
theorem rotatedRepPeelROSignSymmetry_of_ambient
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j : Prim.Idx d)
    (τ : MeasurableEquiv diagonal.core.Ω diagonal.core.Ω)
    (hτ : MeasurePreserving τ diagonal.core.μ diagonal.core.μ)
    (hevent :
      Filter.EventuallyEq (ae diagonal.core.μ)
        (Set.preimage τ (rotatedRepPeelEvent diagonal U I))
        (rotatedRepPeelEvent diagonal U I))
    (hodd :
      Filter.EventuallyEq (ae diagonal.core.μ)
        (fun ω => diagonal.core.R (τ ω) * diagonal.core.O (τ ω) j)
        (fun ω => - (diagonal.core.R ω * diagonal.core.O ω j))) :
    rotatedRepPeelROSignSymmetry diagonal U I j := by
  refine ⟨τ, ?_, ?_⟩
  · exact
      Prim.Probability.measurePreserving_condOn_of_measurePreserving_of_preimage_ae_eq
        diagonal.core.μ (rotatedRepPeelEvent diagonal U I) τ hτ hevent
  · exact
      Prim.Probability.ae_condOn_of_ae diagonal.core.μ
        (rotatedRepPeelEvent diagonal U I) hodd

/-- Packaged ambient sign symmetry gives the conditioned sign symmetry. -/
theorem rotatedRepPeelROSignSymmetry_of_ambientSymmetry
    (diagonal : KDimensionalDiagonalProfile d)
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d))
    (j : Prim.Idx d)
    (h : rotatedRepPeelROAmbientSignSymmetry diagonal U I j) :
    rotatedRepPeelROSignSymmetry diagonal U I j := by
  rcases h with ⟨τ, hτ, hevent, hodd⟩
  exact rotatedRepPeelROSignSymmetry_of_ambient diagonal U I j τ hτ hevent hodd

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
