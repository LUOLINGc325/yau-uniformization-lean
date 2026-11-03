import Yau.LeafProofs.L05AutonomousAveragePairing
import Yau.LeafProofs.L05AutonomousBallMoments

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual pushforward of normalized unit-ball volume by an invertible linear map. -/
def autoLinearBallProbability {n : ℕ} (B : Space n ≃L[ℝ] Space n) : Measure (Space n) :=
  Measure.map B (autoBallProbability n 1)

theorem autoLinearBallProbability_isProbability {n : ℕ} (B : Space n ≃L[ℝ] Space n) :
    IsProbabilityMeasure (autoLinearBallProbability B) := by
  let : IsProbabilityMeasure (autoBallProbability n 1) := autoBallProbability_isProbability n (by norm_num)
  exact (Measure.isProbabilityMeasure_map_iff B.continuous.measurable.aemeasurable).mpr inferInstance

theorem autoLinearBallProbability_integral {n : ℕ} (B : Space n ≃L[ℝ] Space n) (f : Space n → ℝ) :
    (∫ x, f x ∂autoLinearBallProbability B)=∫ y, f (B y) ∂autoBallProbability n 1 :=
  B.toHomeomorph.measurableEmbedding.integral_map f

theorem autoLinearBallProbability_integral_neg {n : ℕ} (B : Space n ≃L[ℝ] Space n) (f : Space n → ℝ) :
    (∫ x, f (-x) ∂autoLinearBallProbability B)=∫ x, f x ∂autoLinearBallProbability B := by
  rw [autoLinearBallProbability_integral,autoLinearBallProbability_integral]
  have hh := autoBallProbability_integral_neg n 1 (fun y => f (B y))
  simpa only [map_neg] using hh

theorem autoLinearBallProbability_linear_zero {n : ℕ} (B : Space n ≃L[ℝ] Space n) (L : Space n →L[ℝ] ℝ) :
    (∫ x, L x ∂autoLinearBallProbability B)=0 := by
  rw [autoLinearBallProbability_integral]
  exact autoBallProbability_linear_zero n 1 (L.comp B.toContinuousLinearMap)

theorem autoLinearBallProbability_norm_ae {n : ℕ} (B : Space n ≃L[ℝ] Space n) :
    ∀ᵐ x ∂autoLinearBallProbability B, ‖x‖≤ ‖B.toContinuousLinearMap‖ := by
  apply (ae_map_iff B.continuous.measurable.aemeasurable
    (isClosed_le continuous_norm continuous_const).measurableSet).mpr
  filter_upwards [autoBallProbability_closedBall_ae n 1] with y hy
  have hy' : ‖y‖≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
  exact (B.toContinuousLinearMap.le_opNorm y).trans (by nlinarith only [hy',norm_nonneg B.toContinuousLinearMap])

/-- This is precisely the normalized literal ellipsoid average used in the trace estimate. -/
theorem autoLinearBallProbability_average {n : ℕ} (B : Space n ≃L[ℝ] Space n) (f : Space n → ℝ)
    (x : Space n) : autoSpatialAverage (autoLinearBallProbability B) f x=
      (∫ y in Metric.ball (0 : Space n) 1, f (x+B y))/((volume : Measure (Space n)).real (Metric.ball 0 1)) := by
  rw [autoSpatialAverage,autoLinearBallProbability_integral,autoBallProbability_integral]

/-- The symmetric commutator identity is instantiated with the actual elliptipsoid measure. -/
theorem auto_ellipsoid_average_commutator {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    {φ f : Space n → ℝ} (hφ : Continuous φ) (hf : Continuous f)
    (hcφ : HasCompactSupport φ) (hcf : HasCompactSupport f) :
    Integrable (fun x => φ x*(autoSpatialAverage (autoLinearBallProbability B) f x-f x)) ∧
      Integrable (fun x => f x*(autoSpatialAverage (autoLinearBallProbability B) φ x-φ x)) ∧
      (∫ x, φ x*(autoSpatialAverage (autoLinearBallProbability B) f x-f x))=
        ∫ x, f x*(autoSpatialAverage (autoLinearBallProbability B) φ x-φ x) := by
  let : IsProbabilityMeasure (autoLinearBallProbability B) := autoLinearBallProbability_isProbability B
  exact auto_symmetric_average_commutator (autoLinearBallProbability B)
    (autoLinearBallProbability_integral_neg B) hφ hf hcφ hcf

/-- A compact extension in space-time has an actual compact spatial slice at every time. -/
theorem auto_compact_spatial_slice {n : ℕ} {w : Point n → ℝ} (hw : HasCompactSupport w) (t : ℝ) :
    HasCompactSupport (fun x : Space n => w (x,t)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hw.image continuous_fst)
  intro x hx
  exact ⟨(x,t),subset_tsupport w hx,rfl⟩

/-- The cutoff commutator vanishes outside the actual uniformly enlarged support. -/
theorem auto_ellipsoid_cutoff_vanish {n : ℕ} {φ : Space n → ℝ} {R b : ℝ}
    (hsupp : tsupport φ⊆Metric.closedBall (0 : Space n) R) (hb : 0≤ b)
    (B : Space n ≃L[ℝ] Space n) (hB : ‖B.toContinuousLinearMap‖≤ b)
    {x : Space n} (hx : x∉Metric.closedBall (0 : Space n) (R+b)) :
    autoSpatialAverage (autoLinearBallProbability B) φ x-φ x=0 := by
  have hnorm : R+b<‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  have hφx : φ x=0 := image_eq_zero_of_notMem_tsupport (fun hxφ => by
    have hh : ‖x‖≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hsupp hxφ
    linarith only [hh,hb,hnorm])
  have hAE : ∀ᵐ y ∂autoLinearBallProbability B, φ (x+y)=0 := by
    filter_upwards [autoLinearBallProbability_norm_ae B] with y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hxy
    have hh : ‖x+y‖≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hsupp hxy
    have htri : ‖x‖≤ ‖x+y‖+‖y‖ := by
      simpa only [add_neg_cancel_right,norm_neg] using norm_add_le (x+y) (-y)
    linarith only [htri,hh,hy,hB,hnorm]
  rw [autoSpatialAverage,integral_eq_zero_of_ae hAE,hφx,sub_zero]

/-- The actual invertible displacement map is exactly `y ↦ r • S y`. -/
def autoRadiusLinearEquiv {n : ℕ} (S : Space n ≃L[ℝ] Space n) (r : ℝ) (hr : 0< r) :
    Space n ≃L[ℝ] Space n :=
  S.trans (LinearEquiv.smulOfNeZero ℝ (Space n) r hr.ne').toContinuousLinearEquiv

theorem autoRadiusLinearEquiv_apply {n : ℕ} (S : Space n ≃L[ℝ] Space n) (r : ℝ) (hr : 0< r)
    (y : Space n) : autoRadiusLinearEquiv S r hr y=r • S y := rfl

theorem autoRadiusLinearEquiv_clm {n : ℕ} (S : Space n ≃L[ℝ] Space n) (r : ℝ) (hr : 0< r) :
    (autoRadiusLinearEquiv S r hr).toContinuousLinearMap=r • S.toContinuousLinearMap := by
  ext y
  rfl

theorem autoRadiusLinearEquiv_norm {n : ℕ} (S : Space n ≃L[ℝ] Space n) (r : ℝ) (hr : 0< r) :
    ‖(autoRadiusLinearEquiv S r hr).toContinuousLinearMap‖=r*‖S.toContinuousLinearMap‖ := by
  rw [autoRadiusLinearEquiv_clm,norm_smul,Real.norm_eq_abs,abs_of_pos hr]

theorem autoRadiusLinearEquiv_elliptic_bounds {n : ℕ} {L : ℝ} (hL : 0≤ L)
    (S : Space n ≃L[ℝ] Space n) (hS : ‖S.toContinuousLinearMap‖≤ Real.sqrt L)
    (r : ℝ) (hr : 0< r) :
    ‖(autoRadiusLinearEquiv S r hr).toContinuousLinearMap‖≤ r*Real.sqrt L ∧
      ‖(autoRadiusLinearEquiv S r hr).toContinuousLinearMap‖^2≤ r^2*L := by
  rw [autoRadiusLinearEquiv_norm]
  constructor
  · exact mul_le_mul_of_nonneg_left hS hr.le
  · have hs : ‖S.toContinuousLinearMap‖^2≤ L := by
      rw [← Real.sq_sqrt hL]
      exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hS
    nlinarith only [mul_le_mul_of_nonneg_left hs (sq_nonneg r)]

end Yau.LeafProofs.L05AutonomousAux
