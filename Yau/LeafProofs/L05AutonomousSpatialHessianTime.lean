import Yau.LeafProofs.L05AutonomousSpatialHessianRepresentation
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- Evaluation at a fixed time preserves the actual second Frechet derivative,
for arbitrary real spatial directions, not only chosen basis entries. -/
theorem auto_bcf_slice_second_apply {n : ℕ} {g : Space n → ℝ →ᵇ ℝ}
    (hg : ContDiff ℝ ∞ g) (x : Space n) (t : ℝ) (v z : Space n) :
    fderiv ℝ (fderiv ℝ (fun y => g y t)) x v z=
      (fderiv ℝ (fderiv ℝ g) x v z) t := by
  have hh := (BoundedContinuousFunction.evalCLM ℝ t).iteratedFDeriv_comp_left
    (x := x) hg.contDiffAt (i := 2) (by simp)
  have hval := congrArg (fun A => A ![v,z]) hh
  simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe,Function.comp_def,
    iteratedFDeriv_two_apply,BoundedContinuousFunction.evalCLM_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] using hval

/-- The actual smoothed directional Hessian is continuous in time, including
any terminal face of a closed time interval. -/
theorem autoSpatialMollify_second_direction_continuous {n : ℕ}
    (eps : ℝ) (heps : 0 < eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) (e x : Space n) :
    Continuous (fun t : ℝ =>
      fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify eps heps w (y,t))) x e e) := by
  have hm := autoSpatialMollifyBCF_contDiff eps heps w hw
  have hc : Continuous (fun t : ℝ =>
      (fderiv ℝ (fderiv ℝ (autoSpatialMollifyBCF eps heps w)) x e e) t) :=
    (fderiv ℝ (fderiv ℝ (autoSpatialMollifyBCF eps heps w)) x e e).continuous
  have heq : (fun t : ℝ =>
      fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify eps heps w (y,t))) x e e)=
      (fun t : ℝ => (fderiv ℝ (fderiv ℝ (autoSpatialMollifyBCF eps heps w)) x e e) t) := by
    funext t
    exact auto_bcf_slice_second_apply hm x t e e
  rwa [heq]

/-- Full space-time a.e. directional limits and a continuous representative
identify the ACTUAL spatially smoothed Hessian at EVERY closed time, including
both endpoints. The intermediate Fubini conclusion is used only a.e. in time. -/
theorem auto_spatial_mollify_second_all_time {n : ℕ} {O : Set (Space n)}
    (hO : MeasurableSet O) {a b : ℝ} (hab : a < b)
    {eps : ℝ} (heps : 0 < eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ))
    {H : Point n → ℝ} (hH : Measurable H)
    (hHC : ContinuousOn H (O ×ˢ Icc a b)) (e x : Space n)
    (hRegion : ∀ q∈Metric.closedBall (0 : Space n) eps, x-q∈O)
    (h : ℕ → ℝ) (hpos : ∀ j, 0 < h j) (hzero : Tendsto h atTop (𝓝 0))
    {B D : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ j, ∀ p∈O ×ˢ Ioo a b, |autoSecond w e (h j) p| ≤ B)
    (hLimit : ∀ᵐ p ∂((volume : Measure (Point n)).restrict (O ×ˢ Ioo a b)),
      Tendsto (fun j => autoSecond w e (h j) p) atTop (𝓝 (H p)))
    (hHBound : ∀ p∈O ×ˢ Icc a b, |H p| ≤ D) :
    ∀ t∈Icc a b,
      fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify eps heps w (y,t))) x e e=
        ∫ q, H (x-q,t) ∂autoMollifierMeasure n eps heps := by
  let nu := autoMollifierMeasure n eps heps
  let : IsProbabilityMeasure nu := autoMollifierMeasure_isProbability n eps heps
  have hAverage : ContinuousOn (fun t : ℝ => ∫ q, H (x-q,t) ∂nu) (Icc a b) := by
    apply continuousOn_of_dominated (bound := fun _ : Space n => D)
    · intro t _
      exact (hH.comp ((continuous_const.sub continuous_id).prodMk continuous_const).measurable).aestronglyMeasurable
    · intro t ht
      filter_upwards [autoMollifierMeasure_closedBall_ae n eps heps] with q hq
      simpa only [Real.norm_eq_abs] using hHBound (x-q,t) ⟨hRegion q hq,ht⟩
    · exact integrable_const D
    · filter_upwards [autoMollifierMeasure_closedBall_ae n eps heps] with q hq
      exact hHC.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hRegion q hq,ht⟩)
  have hLeft := autoSpatialMollify_second_direction_continuous eps heps w hw e x
  have hAE := auto_spatial_mollify_second_ae_time hO measurableSet_Ioo heps w hw hH e x hRegion
    h hpos hzero hB hBound hLimit
  have hEq := Measure.eqOn_open_of_ae_eq hAE isOpen_Ioo hLeft.continuousOn
    (hAverage.mono Ioo_subset_Icc_self)
  exact hEq.of_subset_closure hLeft.continuousOn hAverage Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])

end Yau.LeafProofs.L05AutonomousAux
