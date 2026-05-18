import Prim.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped BigOperators Matrix
open MeasureTheory

/-!
Basic mean, covariance, and centered-product moment definitions.
-/

namespace Prim.Probability

/--
Coordinate-wise mean vector with respect to a measure.
-/
noncomputable def meanVec {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (X : Ω → Prim.Vec d) : Prim.Vec d :=
  fun i => ∫ ω, X ω i ∂ μ

/-- Covariance matrix defined coordinatewise from a random vector. -/
noncomputable def covarianceMatrix {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (X : Ω → Prim.Vec d) : Prim.Mat d :=
  fun i j => ∫ ω, (X ω i - meanVec d μ X i) * (X ω j - meanVec d μ X j) ∂ μ

/-- Centered second product moment of two coordinates. -/
noncomputable def centeredProductMoment {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (i j : Prim.Idx d) : ℝ :=
  ∫ ω, (X ω i - meanVec d μ X i) * (X ω j - meanVec d μ X j) ∂ μ

/-- Entrywise accessor for the covariance definition. -/
theorem covarianceMatrix_apply {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (i j : Prim.Idx d) :
    covarianceMatrix d μ X i j = centeredProductMoment d μ X i j := by
  rfl

/-- Centered product moments are symmetric. -/
theorem centeredProductMoment_comm {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (i j : Prim.Idx d) :
    centeredProductMoment d μ X i j = centeredProductMoment d μ X j i := by
  simp [centeredProductMoment, mul_comm]

/-- Covariance matrices are symmetric by commutativity of multiplication. -/
theorem covarianceMatrix_comm {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (i j : Prim.Idx d) :
    covarianceMatrix d μ X i j = covarianceMatrix d μ X j i := by
  simpa [covarianceMatrix_apply] using centeredProductMoment_comm d μ X i j

/-- Mean vectors are unchanged when the ambient measure is definitionally equal. -/
theorem meanVec_congr_measure {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    {μ ν : Measure Ω} (hμ : μ = ν) (X : Ω → Prim.Vec d) :
    meanVec d μ X = meanVec d ν X := by
  subst hμ
  rfl

/-- Mean vectors are unchanged when the random vectors are a.e. equal. -/
theorem meanVec_congr_ae {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) {X Y : Ω → Prim.Vec d} (hXY : X =ᵐ[μ] Y) :
    meanVec d μ X = meanVec d μ Y := by
  funext i
  exact integral_congr_ae (hXY.mono fun ω hω => congrArg (fun v => v i) hω)

/-- Covariance matrices are unchanged when the ambient measure is equal. -/
theorem covarianceMatrix_congr_measure {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    {μ ν : Measure Ω} (hμ : μ = ν) (X : Ω → Prim.Vec d) :
    covarianceMatrix d μ X = covarianceMatrix d ν X := by
  subst hμ
  rfl

/-- Covariance matrices are unchanged when the random vectors are a.e. equal. -/
theorem covarianceMatrix_congr_ae {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) {X Y : Ω → Prim.Vec d} (hXY : X =ᵐ[μ] Y) :
    covarianceMatrix d μ X = covarianceMatrix d μ Y := by
  have hmean : meanVec d μ X = meanVec d μ Y := meanVec_congr_ae d μ hXY
  ext i j
  apply integral_congr_ae
  exact hXY.mono fun ω hω => by
    have hi : X ω i = Y ω i := congrArg (fun v => v i) hω
    have hj : X ω j = Y ω j := congrArg (fun v => v j) hω
    have hmeani : meanVec d μ X i = meanVec d μ Y i := congrArg (fun v => v i) hmean
    have hmeanj : meanVec d μ X j = meanVec d μ Y j := congrArg (fun v => v j) hmean
    simp [hi, hj, hmeani, hmeanj]

/-- Centered product moments are unchanged when the ambient measure is equal. -/
theorem centeredProductMoment_congr_measure {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    {μ ν : Measure Ω} (hμ : μ = ν) (X : Ω → Prim.Vec d)
    (i j : Prim.Idx d) :
    centeredProductMoment d μ X i j = centeredProductMoment d ν X i j := by
  subst hμ
  rfl

/-- Centered product moments are unchanged when the random vectors are a.e. equal. -/
theorem centeredProductMoment_congr_ae {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (μ : Measure Ω) {X Y : Ω → Prim.Vec d} (hXY : X =ᵐ[μ] Y)
    (i j : Prim.Idx d) :
    centeredProductMoment d μ X i j = centeredProductMoment d μ Y i j := by
  have hmean : meanVec d μ X = meanVec d μ Y := meanVec_congr_ae d μ hXY
  apply integral_congr_ae
  exact hXY.mono fun ω hω => by
    have hi : X ω i = Y ω i := congrArg (fun v => v i) hω
    have hj : X ω j = Y ω j := congrArg (fun v => v j) hω
    have hmeani : meanVec d μ X i = meanVec d μ Y i := congrArg (fun v => v i) hmean
    have hmeanj : meanVec d μ X j = meanVec d μ Y j := congrArg (fun v => v j) hmean
    simp [hi, hj, hmeani, hmeanj]

end Prim.Probability
