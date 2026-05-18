import Prim.Probability.ConditionalMeasure.Basic
import Prim.Probability.ConditionalCovariance.Base

open scoped BigOperators Matrix
open MeasureTheory

/-!
Event-conditioned preserved covariance and centered-product moment API.
-/

namespace Prim.Probability
/-- Preserved covariance after conditioning on an event. -/
noncomputable def preservedCov {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) : Prim.Mat d :=
  covarianceMatrix d (condOn μ s) X

/-- Centered product moment under the event-conditioned measure. -/
noncomputable def preservedCenteredProductMoment {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) (i j : Prim.Idx d) : ℝ :=
  centeredProductMoment d (condOn μ s) X i j

/-- Entrywise accessor for preserved covariance as a conditioned centered second moment. -/
theorem preservedCov_apply {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) (i j : Prim.Idx d) :
    preservedCov d μ s X i j =
      preservedCenteredProductMoment d μ s X i j := by
  rfl

/-- Preserved covariance is unchanged by replacing the event with an a.e.-equal event. -/
theorem preservedCov_congr_set {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) {s t : Set Ω} (h : s =ᵐ[μ] t)
    (X : Ω → Prim.Vec d) :
    preservedCov d μ s X = preservedCov d μ t X := by
  exact covarianceMatrix_congr_measure d (condOn_congr_set μ h) X

/-- Preserved centered moments are unchanged by replacing the event with an a.e.-equal event. -/
theorem preservedCenteredProductMoment_congr_set {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (μ : Measure Ω) {s t : Set Ω} (h : s =ᵐ[μ] t)
    (X : Ω → Prim.Vec d) (i j : Prim.Idx d) :
    preservedCenteredProductMoment d μ s X i j =
      preservedCenteredProductMoment d μ t X i j := by
  exact centeredProductMoment_congr_measure d (condOn_congr_set μ h) X i j

/-- Preserved covariance is unchanged when the random vectors are a.e. equal. -/
theorem preservedCov_congr_ae {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) {X Y : Ω → Prim.Vec d}
    (hXY : X =ᵐ[μ] Y) :
    preservedCov d μ s X = preservedCov d μ s Y := by
  exact covarianceMatrix_congr_ae d (condOn μ s) (ae_eq_condOn_of_ae_eq μ s hXY)

/-- Preserved centered moments are unchanged when the random vectors are a.e. equal. -/
theorem preservedCenteredProductMoment_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (μ : Measure Ω) (s : Set Ω) {X Y : Ω → Prim.Vec d}
    (hXY : X =ᵐ[μ] Y) (i j : Prim.Idx d) :
    preservedCenteredProductMoment d μ s X i j =
      preservedCenteredProductMoment d μ s Y i j := by
  exact centeredProductMoment_congr_ae d (condOn μ s)
    (ae_eq_condOn_of_ae_eq μ s hXY) i j

/-- Preserved centered product moments are symmetric. -/
theorem preservedCenteredProductMoment_comm {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) (i j : Prim.Idx d) :
    preservedCenteredProductMoment d μ s X i j =
      preservedCenteredProductMoment d μ s X j i := by
  exact centeredProductMoment_comm d (condOn μ s) X i j

/--
If the conditioned coordinate mean is zero, a diagonal centered product moment
is the corresponding raw second moment.
-/
theorem preservedCenteredProductMoment_diag_eq_integral_mul_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) (i : Prim.Idx d)
    (hmean : meanVec d (condOn μ s) X i = 0) :
    preservedCenteredProductMoment d μ s X i i =
      ∫ ω, X ω i * X ω i ∂ condOn μ s := by
  unfold preservedCenteredProductMoment centeredProductMoment
  rw [hmean]
  simp

/--
Raw conditional second moments imply diagonal centered product moments once the
corresponding conditioned means vanish.
-/
theorem preservedCenteredProductMoment_diag_eq_of_mean_zero_and_integral
    {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) (i : Prim.Idx d)
    {v : ℝ}
    (hmean : meanVec d (condOn μ s) X i = 0)
    (hsecond : (∫ ω, X ω i * X ω i ∂ condOn μ s) = v) :
    preservedCenteredProductMoment d μ s X i i = v := by
  rw [preservedCenteredProductMoment_diag_eq_integral_mul_of_mean_zero
    d μ s X i hmean, hsecond]


/-- Preserved covariance matrices are symmetric. -/
theorem preservedCov_comm {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d) (i j : Prim.Idx d) :
    preservedCov d μ s X i j = preservedCov d μ s X j i := by
  simpa [preservedCov_apply] using
    preservedCenteredProductMoment_comm d μ s X i j

/--
To prove all off-diagonal preserved covariances vanish, it suffices to prove
the strictly upper-triangular entries vanish.
-/
theorem preservedCov_offDiag_eq_zero_of_lt {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (μ : Measure Ω) (s : Set Ω) (X : Ω → Prim.Vec d)
    (hupper : ∀ {i j : Prim.Idx d}, i < j → preservedCov d μ s X i j = 0)
    {i j : Prim.Idx d} (hij : i ≠ j) :
    preservedCov d μ s X i j = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hupper hlt
  · rw [preservedCov_comm d μ s X i j]
    exact hupper hgt

end Prim.Probability
