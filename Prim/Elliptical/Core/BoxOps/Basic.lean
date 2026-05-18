import Prim.Elliptical.Core.Quantile
import Prim.Probability.ConditionalMeasure.CentralBox
import Prim.Probability.ConditionalCovariance.CentralBox.Core.Basic

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/-- Single-coordinate peeling event. -/
def singlePeelEvent (q : ℝ) (i : Prim.Idx d) : Set E.Ω :=
  E.peelSetEvent q ({i} : Finset (Prim.Idx d))

/-- Conditioned measure associated with a principal-coordinate peeling event. -/
noncomputable def condMeasureOn (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) :
    Measure E.Ω :=
  (E.principalBoxData q hq).condMeasure E.μ E.Y I

/-- Conditioned expectation associated with a principal-coordinate peeling event. -/
noncomputable def condIntegralOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) (f : E.Ω → F) : F :=
  (E.principalBoxData q hq).condIntegral E.μ E.Y I f

/-- Preserved covariance after peeling a set of principal coordinates. -/
noncomputable def preservedCovOn (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) :
    Prim.Mat d :=
  (E.principalBoxData q hq).preservedCov E.μ E.Y I

/-- Preserved trace after peeling a set of principal coordinates. -/
noncomputable def preservedTraceOn (q : ℝ) (I : Finset (Prim.Idx d)) : ℝ :=
  by
    let _ := E.instMeasurableSpace
    exact Prim.Probability.preservedTrace d E.μ (E.peelSetEvent q I) E.Y

/-- Preserved trace after peeling a single principal coordinate. -/
noncomputable def singlePreservedTrace (q : ℝ) (i : Prim.Idx d) : ℝ :=
  E.preservedTraceOn q ({i} : Finset (Prim.Idx d))

@[simp] theorem mem_peelSetEvent {q : ℝ} {I : Finset (Prim.Idx d)} {ω : E.Ω} :
    ω ∈ E.peelSetEvent q I ↔ ∀ i ∈ I, |E.Y ω i| ≤ E.halfWidth q i := by
  let _ := E.instMeasurableSpace
  rfl

@[simp] theorem principalBoxData_event_eq_peelSetEvent (q : ℝ) (hq : 0 ≤ q)
    (I : Finset (Prim.Idx d)) :
    (E.principalBoxData q hq).event E.Y I = E.peelSetEvent q I := by
  let _ := E.instMeasurableSpace
  rfl

@[simp] theorem condMeasureOn_eq (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) :
    E.condMeasureOn q hq I = Prim.Probability.condOn E.μ (E.peelSetEvent q I) := by
  rw [EllipticalCore.condMeasureOn, Prim.Probability.CentralBoxData.condMeasure]
  rw [E.principalBoxData_event_eq_peelSetEvent q hq I]

@[simp] theorem condIntegralOn_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) (f : E.Ω → F) :
    E.condIntegralOn q hq I f = Prim.Probability.condOnIntegral E.μ (E.peelSetEvent q I) f := by
  rw [EllipticalCore.condIntegralOn, Prim.Probability.CentralBoxData.condIntegral]
  rw [E.principalBoxData_event_eq_peelSetEvent q hq I]

@[simp] theorem preservedCovOn_eq (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) :
    E.preservedCovOn q hq I = Prim.Probability.preservedCov d E.μ (E.peelSetEvent q I) E.Y := by
  rw [EllipticalCore.preservedCovOn, Prim.Probability.CentralBoxData.preservedCov]
  rw [E.principalBoxData_event_eq_peelSetEvent q hq I]

@[simp] theorem singlePreservedTrace_eq_preservedTraceOn_singleton (q : ℝ)
    (i : Prim.Idx d) :
    E.singlePreservedTrace q i = E.preservedTraceOn q ({i} : Finset (Prim.Idx d)) := by
  rfl

@[simp] theorem preservedTraceOn_eq (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) :
    E.preservedTraceOn q I = (E.principalBoxData q hq).preservedTrace E.μ E.Y I := by
  rw [EllipticalCore.preservedTraceOn, Prim.Probability.CentralBoxData.preservedTrace]
  rw [E.principalBoxData_event_eq_peelSetEvent q hq I]
@[simp] theorem preservedTraceOn_eq_sum_diag (q : ℝ) (hq : 0 ≤ q) (I : Finset (Prim.Idx d)) :
    E.preservedTraceOn q I = ∑ i, E.preservedCovOn q hq I i i := by
  rw [EllipticalCore.preservedTraceOn_eq (E := E) q hq I]
  rw [EllipticalCore.preservedCovOn_eq (E := E) q hq I]
  simpa using Prim.Probability.preservedTrace_eq_sum_diag d E.μ (E.peelSetEvent q I) E.Y

end EllipticalCore

end Prim.Elliptical
