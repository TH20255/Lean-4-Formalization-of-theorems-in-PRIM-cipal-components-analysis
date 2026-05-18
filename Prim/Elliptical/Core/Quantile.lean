import Prim.Elliptical.Core.Base
import Prim.Probability.QuantileBox.Quantile

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/-- Simultaneous peeling event on a finite set of principal coordinates. -/
def peelSetEvent (q : ℝ) (I : Finset (Prim.Idx d)) : Set E.Ω :=
  by
    let _ := E.instMeasurableSpace
    exact Prim.Probability.peelEvent d E.Y (E.halfWidth q) I

/--
Distributional central-quantile data whose symmetric half-widths are the
principal-coordinate half-widths of the core.

The remaining source obligations are the lower and upper tail-mass inequalities
for the proposed scalar radius.  Once those are supplied, this object is a
ready-made quantile-side source for the principal-box handoff.
-/
noncomputable def principalCentralQuantileBoxData
    (tailAlpha radius : ℝ) (hradius : 0 ≤ radius)
    (hlower :
      ∀ i, ENNReal.ofReal tailAlpha ≤
        E.μ {ω | E.Y ω i ≤ -E.halfWidth radius i})
    (hupper :
      ∀ i, ENNReal.ofReal tailAlpha ≤
        E.μ {ω | E.halfWidth radius i ≤ E.Y ω i}) :
    Prim.Probability.CentralQuantileBoxData d E.μ E.Y where
  alpha := tailAlpha
  lower := fun i => -E.halfWidth radius i
  upper := E.halfWidth radius
  q := E.halfWidth radius
  q_nonneg := by
    intro i
    exact mul_nonneg (Real.sqrt_nonneg _) hradius
  lower_eq_neg_q := fun _i => rfl
  upper_eq_q := fun _i => rfl
  lower_tail_mass := hlower
  upper_tail_mass := hupper

@[simp] theorem principalCentralQuantileBoxData_q
    (tailAlpha radius : ℝ) (hradius : 0 ≤ radius)
    (hlower :
      ∀ i, ENNReal.ofReal tailAlpha ≤
        E.μ {ω | E.Y ω i ≤ -E.halfWidth radius i})
    (hupper :
      ∀ i, ENNReal.ofReal tailAlpha ≤
        E.μ {ω | E.halfWidth radius i ≤ E.Y ω i})
    (i : Prim.Idx d) :
    (E.principalCentralQuantileBoxData tailAlpha radius hradius hlower hupper).q i =
      E.halfWidth radius i := rfl

/--
The interval event of the core principal quantile box is definitionally the
principal-coordinate peeling event after the symmetric-interval rewrite.
-/
theorem principalCentralQuantileBoxData_intervalEvent_eq_peelSetEvent
    (tailAlpha radius : ℝ) (hradius : 0 ≤ radius)
    (hlower :
      ∀ i, ENNReal.ofReal tailAlpha ≤
        E.μ {ω | E.Y ω i ≤ -E.halfWidth radius i})
    (hupper :
      ∀ i, ENNReal.ofReal tailAlpha ≤
        E.μ {ω | E.halfWidth radius i ≤ E.Y ω i})
    (I : Finset (Prim.Idx d)) :
    (E.principalCentralQuantileBoxData tailAlpha radius hradius hlower hupper).intervalEvent I =
      Prim.Probability.peelEvent d E.Y (E.halfWidth radius) I := by
  let Q := E.principalCentralQuantileBoxData tailAlpha radius hradius hlower hupper
  calc
    Q.intervalEvent I = Prim.Probability.peelEvent d E.Y Q.q I := by
      exact Q.intervalEvent_eq_peelEvent I
    _ = Prim.Probability.peelEvent d E.Y (E.halfWidth radius) I := by
      rfl

/-- Core-facing version of the principal quantile interval event rewrite. -/
theorem principalCentralQuantileBoxData_intervalEvent_eq_corePeelSetEvent
    (tailAlpha radius : ℝ) (hradius : 0 ≤ radius)
    (hlower :
      ∀ i, ENNReal.ofReal tailAlpha ≤
        E.μ {ω | E.Y ω i ≤ -E.halfWidth radius i})
    (hupper :
      ∀ i, ENNReal.ofReal tailAlpha ≤
        E.μ {ω | E.halfWidth radius i ≤ E.Y ω i})
    (I : Finset (Prim.Idx d)) :
    (E.principalCentralQuantileBoxData tailAlpha radius hradius hlower hupper).intervalEvent I =
      E.peelSetEvent radius I := by
  simpa [EllipticalCore.peelSetEvent] using
    E.principalCentralQuantileBoxData_intervalEvent_eq_peelSetEvent
      tailAlpha radius hradius hlower hupper I

/--
Named source object for the scalar-radius central-quantile assumptions used by
the principal-box chain.

This is the paper-facing shape left after accepting the stochastic
representation: a scalar radius and coordinate tail-mass lower bounds at the
principal half-widths.
-/
structure PrincipalCentralQuantileSource (E : EllipticalCore d) where
  tailAlpha : ℝ
  radius : ℝ
  hradius : 0 ≤ radius
  lower_tail_mass :
    ∀ i, ENNReal.ofReal tailAlpha ≤
      E.μ {ω | E.Y ω i ≤ -E.halfWidth radius i}
  upper_tail_mass :
    ∀ i, ENNReal.ofReal tailAlpha ≤
      E.μ {ω | E.halfWidth radius i ≤ E.Y ω i}

namespace PrincipalCentralQuantileSource

variable {d : Nat} {E : EllipticalCore d} (S : PrincipalCentralQuantileSource E)

/-- Convert a scalar-radius quantile source into the reusable central-quantile box data. -/
noncomputable def toCentralQuantileBoxData :
    Prim.Probability.CentralQuantileBoxData d E.μ E.Y :=
  E.principalCentralQuantileBoxData
    S.tailAlpha S.radius S.hradius S.lower_tail_mass S.upper_tail_mass

/-- The source half-widths are exactly the principal half-widths at `S.radius`. -/
@[simp] theorem toCentralQuantileBoxData_q (i : Prim.Idx d) :
    S.toCentralQuantileBoxData.q i = E.halfWidth S.radius i := rfl

/-- Source interval events rewrite to the raw principal peeling event. -/
theorem intervalEvent_eq_peelSetEvent (I : Finset (Prim.Idx d)) :
    S.toCentralQuantileBoxData.intervalEvent I =
      Prim.Probability.peelEvent d E.Y (E.halfWidth S.radius) I :=
  E.principalCentralQuantileBoxData_intervalEvent_eq_peelSetEvent
    S.tailAlpha S.radius S.hradius S.lower_tail_mass S.upper_tail_mass I

/-- Source interval events rewrite to the core-facing principal peeling event. -/
theorem intervalEvent_eq_corePeelSetEvent (I : Finset (Prim.Idx d)) :
    S.toCentralQuantileBoxData.intervalEvent I = E.peelSetEvent S.radius I :=
  E.principalCentralQuantileBoxData_intervalEvent_eq_corePeelSetEvent
    S.tailAlpha S.radius S.hradius S.lower_tail_mass S.upper_tail_mass I

end PrincipalCentralQuantileSource

end EllipticalCore

end Prim.Elliptical
