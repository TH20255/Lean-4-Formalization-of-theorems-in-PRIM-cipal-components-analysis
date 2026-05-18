import Prim.Proofs.BoxVolume.Handoff.AssumptionBasic

/-!
Lightweight quantile/radius source constructors.

`Prim.Proofs.BoxVolume` owns the heavy principal-box and volume machinery.
This leaf keeps paper-facing quantile source constructors out of that hot
module, so final theorem assembly can evolve without repeatedly recompiling the
box-volume stack.
-/

namespace Prim.Proofs

open MeasureTheory
open Prim.Elliptical

namespace PrincipalQuantileRadiusAssumption

variable {d : Nat} {core : EllipticalCore d}

/--
Build the concrete quantile/radius package from the named scalar-radius
central-quantile source.  This is the canonical proof-side endpoint for a
paper-level quantile lemma that has already identified the principal scalar
radius and proved the two coordinate tail-mass bounds.
-/
noncomputable def ofPrincipalCentralQuantileSource
    (S : EllipticalCore.PrincipalCentralQuantileSource core) :
    PrincipalQuantileRadiusAssumption core where
  Q := S.toCentralQuantileBoxData
  radius := S.radius
  hradius := S.hradius
  halfWidth_eq := fun _i => rfl

@[simp] theorem ofPrincipalCentralQuantileSource_Q
    (S : EllipticalCore.PrincipalCentralQuantileSource core) :
    (ofPrincipalCentralQuantileSource S).Q = S.toCentralQuantileBoxData := rfl

@[simp] theorem ofPrincipalCentralQuantileSource_radius
    (S : EllipticalCore.PrincipalCentralQuantileSource core) :
    (ofPrincipalCentralQuantileSource S).radius = S.radius := rfl

@[simp] theorem ofPrincipalCentralQuantileSource_hradius
    (S : EllipticalCore.PrincipalCentralQuantileSource core) :
    (ofPrincipalCentralQuantileSource S).hradius = S.hradius := rfl

@[simp] theorem ofPrincipalCentralQuantileSource_halfWidth_eq
    (S : EllipticalCore.PrincipalCentralQuantileSource core) (i : Prim.Idx d) :
    (ofPrincipalCentralQuantileSource S).Q.q i =
      core.halfWidth (ofPrincipalCentralQuantileSource S).radius i := rfl

end PrincipalQuantileRadiusAssumption

end Prim.Proofs
