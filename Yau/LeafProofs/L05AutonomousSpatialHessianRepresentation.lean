import Yau.LeafProofs.L05AutonomousMollifierSecond
import Yau.LeafProofs.L05AutonomousSecondCoefficient
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- At a legitimate a.e. time slice, Haar translation and the actual positive
spatial smoothing measure transfer the a.e. spatial limit to the smoothing integral. -/
theorem autoMollifierMeasure_ae_sub {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    {O : Set (Space n)} (hO : MeasurableSet O) (x : Space n)
    (hRegion : ∀ q∈Metric.closedBall (0 : Space n) eps, x-q∈O)
    {P : Space n → Prop} (hP : ∀ᵐ y ∂((volume : Measure (Space n)).restrict O), P y) :
    ∀ᵐ q ∂autoMollifierMeasure n eps heps, P (x-q) := by
  have hGlobal := (ae_restrict_iff' hO).mp hP
  have hShift := ((volume : Measure (Space n)).measurePreserving_sub_left x).quasiMeasurePreserving.ae hGlobal
  have hAC : autoMollifierMeasure n eps heps ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  have hShiftNu := hShift.filter_mono hAC.ae_le
  filter_upwards [hShiftNu,autoMollifierMeasure_closedBall_ae n eps heps] with q hq hball
  exact hq (hRegion q hball)

/-- The actual spatial Hessian at a valid time slice is the literal positive
spatial average of the measurable directional limit. -/
theorem auto_spatial_mollify_second_representation_along {n : ℕ} {O : Set (Space n)}
    (hO : MeasurableSet O) {eps : ℝ} (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    (H : Space n → ℝ) (hH : Measurable H)
    (e x : Space n) (t : ℝ)
    (hRegion : ∀ q∈Metric.closedBall (0 : Space n) eps, x-q∈O)
    (h : ℕ → ℝ) (hpos : ∀ j, 0 < h j) (hzero : Tendsto h atTop (𝓝 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ j, ∀ z∈O, |autoSecond w e (h j) (z,t)| ≤ B)
    (hLimit : ∀ᵐ z ∂((volume : Measure (Space n)).restrict O),
      Tendsto (fun j => autoSecond w e (h j) (z,t)) atTop (𝓝 (H z))) :
    Integrable (fun q => H (x-q)) (autoMollifierMeasure n eps heps) ∧
      fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify eps heps w (y,t))) x e e=
        ∫ q, H (x-q) ∂autoMollifierMeasure n eps heps := by
  let nu := autoMollifierMeasure n eps heps
  let : IsProbabilityMeasure nu := autoMollifierMeasure_isProbability n eps heps
  have hLimitNu := autoMollifierMeasure_ae_sub heps hO x hRegion hLimit
  have hBoundNu (j : ℕ) : ∀ᵐ q ∂nu, ‖autoSecond w e (h j) (x-q,t)‖ ≤ B := by
    filter_upwards [autoMollifierMeasure_closedBall_ae n eps heps] with q hq
    simpa only [Real.norm_eq_abs] using hBound j _ (hRegion q hq)
  have hBoundAll : ∀ᵐ q ∂nu, ∀ j, ‖autoSecond w e (h j) (x-q,t)‖ ≤ B :=
    ae_all_iff.mpr hBoundNu
  have hInt : Integrable (fun q => H (x-q)) nu := by
    apply (integrable_const B).mono' (hH.comp (continuous_const.sub continuous_id).measurable).aestronglyMeasurable
    filter_upwards [hLimitNu,hBoundAll] with q hq hqb
    exact le_of_tendsto hq.norm (Eventually.of_forall hqb)
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ : Space n => B)
    (fun j => ((autoSecond_continuous w.continuous e (h j)).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable)
    (integrable_const B) hBoundNu hLimitNu
  have hpositive : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero,Eventually.of_forall hpos⟩
  have hSmooth := autoSpatialMollify_spatial_contDiff eps heps w hw t
  have hActual := (auto_spatial_second_limit hSmooth x e).comp hpositive
  change Tendsto (fun j => autoSecond (autoSpatialMollify eps heps w) e (h j) (x,t)) atTop _ at hActual
  have hPair : (fun j => autoSecond (autoSpatialMollify eps heps w) e (h j) (x,t))=
      (fun j => ∫ q, autoSecond w e (h j) (x-q,t) ∂nu) := by
    funext j
    exact (auto_mollify_second eps heps w hw e (h j) (x,t)).2
  rw [hPair] at hActual
  exact ⟨hInt,tendsto_nhds_unique hActual hDCT⟩

/-- Fubini produces genuine a.e. valid time slices from a FULL space-time a.e.
limit. No particular time is substituted into a space-time a.e. assertion. -/
theorem auto_spatial_mollify_second_ae_time {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    (hO : MeasurableSet O) (hI : MeasurableSet I) {eps : ℝ} (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    {H : Point n → ℝ} (hH : Measurable H) (e x : Space n)
    (hRegion : ∀ q∈Metric.closedBall (0 : Space n) eps, x-q∈O)
    (h : ℕ → ℝ) (hpos : ∀ j, 0 < h j) (hzero : Tendsto h atTop (𝓝 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ j, ∀ p∈O ×ˢ I, |autoSecond w e (h j) p| ≤ B)
    (hLimit : ∀ᵐ p ∂((volume : Measure (Point n)).restrict (O ×ˢ I)),
      Tendsto (fun j => autoSecond w e (h j) p) atTop (𝓝 (H p))) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict I),
      fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify eps heps w (y,t))) x e e=
        ∫ q, H (x-q,t) ∂autoMollifierMeasure n eps heps := by
  have hProd : ∀ᵐ p ∂((volume : Measure (Space n)).restrict O).prod
      ((volume : Measure ℝ).restrict I),
      Tendsto (fun j => autoSecond w e (h j) p) atTop (𝓝 (H p)) := by
    simpa only [Measure.prod_restrict,← Measure.volume_eq_prod] using hLimit
  have hSwap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hProd
  have hSlices := Measure.ae_ae_of_ae_prod hSwap
  filter_upwards [hSlices,ae_restrict_mem hI] with t ht htI
  exact (auto_spatial_mollify_second_representation_along hO heps w hw
    (fun z => H (z,t)) (hH.comp (measurable_id.prodMk measurable_const)) e x t hRegion
    h hpos hzero hB (fun j z hz => hBound j (z,t) ⟨hz,htI⟩) ht).2

end Yau.LeafProofs.L05AutonomousAux
