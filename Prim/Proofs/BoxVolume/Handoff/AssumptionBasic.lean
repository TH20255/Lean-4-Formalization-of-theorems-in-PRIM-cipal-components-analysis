import Prim.Elliptical.Core.BoxOps.Basic

namespace Prim.Proofs

open MeasureTheory
open Prim.Elliptical

/--
Paper-facing package for a central quantile box whose symmetric half-widths
come from one scalar principal radius.

This is the distributional quantile/radius input shape expected by the final
assembly: the actual quantile-side box data is kept, while the scalar-radius
matching proof supplies the source object consumed by the checked
principal-box chain.
-/
structure PrincipalQuantileRadiusAssumption (core : EllipticalCore d) where
  Q : Prim.Probability.CentralQuantileBoxData d core.μ core.Y
  radius : Real
  hradius : 0 ≤ radius
  halfWidth_eq : forall i, Q.q i = core.halfWidth radius i

namespace PrincipalQuantileRadiusAssumption

variable {d : Nat} {core : EllipticalCore d}
  (A : PrincipalQuantileRadiusAssumption core)

/-- The quantile/radius package supplies the named scalar-radius tail-mass source. -/
noncomputable def toPrincipalCentralQuantileSource :
    EllipticalCore.PrincipalCentralQuantileSource core where
  tailAlpha := A.Q.alpha
  radius := A.radius
  hradius := A.hradius
  lower_tail_mass := by
    intro i
    simpa [A.Q.lower_eq_neg_q i, A.halfWidth_eq i] using A.Q.lower_tail_mass i
  upper_tail_mass := by
    intro i
    simpa [A.Q.upper_eq_q i, A.halfWidth_eq i] using A.Q.upper_tail_mass i

/-- The packaged quantile interval event is the core principal-box event. -/
theorem intervalEvent_eq_principalBoxData_event
    (I : Finset (Prim.Idx d)) :
    A.Q.intervalEvent I =
      (core.principalBoxData A.radius A.hradius).event core.Y I := by
  calc
    A.Q.intervalEvent I = (A.Q.toCentralBoxData).event core.Y I := by
      rw [A.Q.intervalEvent_eq_peelEvent I]
      rfl
    _ = (core.principalBoxData A.radius A.hradius).event core.Y I := by
      exact (A.Q.toCentralBoxData).event_congr_all
        (core.principalBoxData A.radius A.hradius) core.Y
        (fun i => by
          simpa [Prim.Probability.CentralQuantileBoxData.toCentralBoxData,
            EllipticalCore.principalBoxData] using A.halfWidth_eq i)
        I

/-- Preserved trace over the packaged quantile interval uses the core principal box. -/
theorem intervalPreservedTrace_eq_principalBoxData_preservedTrace
    (I : Finset (Prim.Idx d)) :
    Prim.Probability.preservedTrace d core.μ (A.Q.intervalEvent I) core.Y =
      (core.principalBoxData A.radius A.hradius).preservedTrace core.μ core.Y I := by
  rw [A.intervalEvent_eq_principalBoxData_event I]
  rfl

end PrincipalQuantileRadiusAssumption

end Prim.Proofs
