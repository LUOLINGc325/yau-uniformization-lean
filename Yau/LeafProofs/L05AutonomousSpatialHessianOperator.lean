import Yau.LeafProofs.L05AutonomousSpatialHessianTime
import Yau.LeafProofs.L05AutonomousSymmetricBilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic
local instance autoSpatialHessianOperator_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoSpatialHessianOperator_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance autoSpatialHessianOperator_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance autoSpatialHessianOperator_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The genuine spatial smoothing Hessian equals the Bochner average of a
symmetric continuous bilinear representative. Only actual unit-direction
finite differences and their full space-time a.e. limits are used. -/
theorem auto_spatial_mollify_hessian_operator {n : ℕ} {O : Set (Space n)}
    (hO : MeasurableSet O) {a b : ℝ} (hab : a < b)
    {eps : ℝ} (heps : 0 < eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ))
    (H : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ)) (hH : StronglyMeasurable H)
    (hHC : ContinuousOn H (O ×ˢ Icc a b))
    (hSym : ∀ p, ∀ v z, H p v z=H p z v)
    (x : Space n) (hRegion : ∀ q∈Metric.closedBall (0 : Space n) eps, x-q∈O)
    (h : ℕ → ℝ) (hpos : ∀ j, 0 < h j) (hzero : Tendsto h atTop (𝓝 0))
    {B D : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ e : Space n, ‖e‖=1 → ∀ j, ∀ p∈O ×ˢ Ioo a b, |autoSecond w e (h j) p| ≤ B)
    (hLimit : ∀ e : Space n, ‖e‖=1 → ∀ᵐ p ∂((volume : Measure (Point n)).restrict (O ×ˢ Ioo a b)),
      Tendsto (fun j => autoSecond w e (h j) p) atTop (𝓝 (H p e e)))
    (hHBound : ∀ p∈O ×ˢ Icc a b, ‖H p‖ ≤ D) :
    ∀ t∈Icc a b,
      fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify eps heps w (y,t))) x=
        ∫ q, H (x-q,t) ∂autoMollifierMeasure n eps heps := by
  intro t ht
  let nu := autoMollifierMeasure n eps heps
  let : IsProbabilityMeasure nu := autoMollifierMeasure_isProbability n eps heps
  have hInt : Integrable (fun q => H (x-q,t)) nu := by
    apply Integrable.of_bound
      (hH.comp_measurable ((continuous_const.sub continuous_id).prodMk continuous_const).measurable).aestronglyMeasurable D
    filter_upwards [autoMollifierMeasure_closedBall_ae n eps heps] with q hq
    exact hHBound (x-q,t) ⟨hRegion q hq,ht⟩
  let ev (v z : Space n) : (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ z).comp
      (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) v)
  have hEval (v z : Space n) : (∫ q, H (x-q,t) ∂nu) v z=∫ q, H (x-q,t) v z ∂nu := by
    exact ((ev v z).integral_comp_comm hInt).symm
  apply auto_symmetric_bilinear_eq_of_unit_diagonal
  · exact ((autoSpatialMollify_spatial_contDiff eps heps w hw t).contDiffAt.isSymmSndFDerivAt
      (by simp))
  · intro v z
    rw [hEval,hEval]
    exact integral_congr_ae (ae_of_all nu fun q => hSym (x-q,t) v z)
  · intro e he
    have hScalarMeas : Measurable (fun p => H p e e) :=
      ((ev e e).continuous.comp_stronglyMeasurable hH).measurable
    have hScalarCont : ContinuousOn (fun p => H p e e) (O ×ˢ Icc a b) :=
      (ev e e).continuous.comp_continuousOn hHC
    have hScalarBound : ∀ p∈O ×ˢ Icc a b, |H p e e| ≤ D := by
      intro p hp
      calc
        _ = ‖H p e e‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖H p e‖*‖e‖ := (H p e).le_opNorm e
        _ ≤ ‖H p‖*‖e‖*‖e‖ := mul_le_mul_of_nonneg_right ((H p).le_opNorm e) (norm_nonneg e)
        _ ≤ D := by simpa only [he,mul_one] using hHBound p hp
    rw [hEval]
    exact auto_spatial_mollify_second_all_time hO hab heps w hw hScalarMeas hScalarCont e x hRegion
      h hpos hzero hB (hBound e he) (hLimit e he) hScalarBound t ht

end Yau.LeafProofs.L05AutonomousAux
