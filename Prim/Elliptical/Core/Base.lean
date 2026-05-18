import Prim.Basic
import Prim.Probability.QuantileBox.Basic
import Prim.LinearAlgebra.PrincipalProfile
import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.Independence.Basic

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

/--
Core stochastic-representation interface for the proofs in principal
coordinates.

This is intentionally closer to the representation actually used in the paper's
proofs than to the characteristic-function definition of elliptical
distributions. The later bridge file can connect the two.
-/
structure EllipticalCore (d : Nat) where
  Ω : Type
  instMeasurableSpace : MeasurableSpace Ω
  μ : Measure Ω
  Y : Ω → Prim.Vec d
  R : Ω → ℝ
  O : Ω → Prim.Vec d
  profile : PrincipalProfile d
  measurable_Y : Measurable Y
  measurable_R : Measurable R
  measurable_O : Measurable O
  indep_R_O : ProbabilityTheory.IndepFun R O μ
  angular_unit_sphere : ∀ᵐ ω ∂ μ, ∑ i, (O ω i) ^ (2 : Nat) = 1
  principal_rep :
    ∀ᵐ ω ∂ μ, ∀ i, Y ω i = R ω * Real.sqrt (profile.eigenvalue i) * O ω i

attribute [instance] EllipticalCore.instMeasurableSpace

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/-- Coordinate half-widths induced by a common scalar quantile parameter `q`. -/
noncomputable def halfWidth (q : ℝ) : Prim.Idx d → ℝ :=
  fun i => Real.sqrt (E.profile.eigenvalue i) * q

/-- Central-box data attached to the principal-coordinate half-widths. -/
noncomputable def principalBoxData (q : ℝ) (hq : 0 ≤ q) : Prim.Probability.CentralBoxData d where
  alpha := q
  q := E.halfWidth q
  q_nonneg := by
    intro i
    exact mul_nonneg (Real.sqrt_nonneg _) hq

end EllipticalCore

end Prim.Elliptical
