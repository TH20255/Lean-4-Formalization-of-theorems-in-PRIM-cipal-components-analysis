import Prim.Probability.QuantileBox.Event

namespace Prim.Probability

open MeasureTheory

/--
Distributional central-quantile data for coordinate peeling boxes.

The tail inequalities record the actual quantile-side source facts.  The
symmetry equalities identify the quantile interval with the absolute-value
central box used by the downstream proof architecture.
-/
structure CentralQuantileBoxData {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (X : Ω → Prim.Vec d) where
  alpha : Real
  lower : Fin d → Real
  upper : Fin d → Real
  q : Fin d → Real
  q_nonneg : ∀ i, 0 ≤ q i
  lower_eq_neg_q : ∀ i, lower i = -q i
  upper_eq_q : ∀ i, upper i = q i
  lower_tail_mass : ∀ i, ENNReal.ofReal alpha ≤ μ {ω | X ω i ≤ lower i}
  upper_tail_mass : ∀ i, ENNReal.ofReal alpha ≤ μ {ω | upper i ≤ X ω i}

namespace CentralQuantileBoxData

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat} {μ : Measure Ω}
  {X : Ω → Prim.Vec d} (Q : CentralQuantileBoxData d μ X)

/-- Forget quantile tail data to the central-box object used downstream. -/
def toCentralBoxData : CentralBoxData d where
  alpha := Q.alpha
  q := Q.q
  q_nonneg := Q.q_nonneg

/-- The interval event attached to quantile cutoffs. -/
def intervalEvent (I : Finset (Fin d)) : Set Ω :=
  intervalPeelEvent d X Q.lower Q.upper I

/-- The central-box event attached to the symmetric quantile half-widths. -/
def event (I : Finset (Fin d)) : Set Ω :=
  peelEvent d X Q.q I

/-- Quantile interval events agree with the central absolute-value peeling events. -/
theorem intervalEvent_eq_event (I : Finset (Fin d)) :
    Q.intervalEvent I = Q.event I := by
  unfold intervalEvent event
  exact intervalPeelEvent_eq_peelEvent_of_symmetric d X
    Q.lower Q.upper Q.q Q.lower_eq_neg_q Q.upper_eq_q I

/-- Quantile interval events agree with the raw absolute-value peeling event. -/
theorem intervalEvent_eq_peelEvent (I : Finset (Fin d)) :
    Q.intervalEvent I = peelEvent d X Q.q I := by
  simpa [event] using Q.intervalEvent_eq_event I

/-- The lower-tail quantile mass condition for a coordinate. -/
theorem lower_tail_mass_at_least (i : Fin d) :
    ENNReal.ofReal Q.alpha ≤ μ {ω | X ω i ≤ Q.lower i} :=
  Q.lower_tail_mass i

/-- The upper-tail quantile mass condition for a coordinate. -/
theorem upper_tail_mass_at_least (i : Fin d) :
    ENNReal.ofReal Q.alpha ≤ μ {ω | Q.upper i ≤ X ω i} :=
  Q.upper_tail_mass i

end CentralQuantileBoxData

end Prim.Probability
