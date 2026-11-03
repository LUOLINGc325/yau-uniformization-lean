import Yau.LeafProofs.L05AutonomousJointMollifier
import Yau.LeafProofs.L05AutonomousJointSecondFTC

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

local instance autoJointHessianRepresentation_pointHaar (n : ℕ) :
    (volume : Measure (Point n)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

/-- Full space-time almost-everywhere facts are transferred by actual Haar translation
and the genuine absolutely continuous joint smoothing measure. No fixed-time slice
of an a.e. assertion is taken. -/
theorem autoJointMollifierMeasure_ae_sub {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    {O : Set (Point n)} (hO : MeasurableSet O) (p : Point n)
    (hRegion : ∀ q∈Metric.ball (0 : Point n) eps, p-q∈O)
    {P : Point n → Prop} (hP : ∀ᵐ y ∂((volume : Measure (Point n)).restrict O), P y) :
    ∀ᵐ q ∂autoJointMollifierMeasure n eps, P (p-q) := by
  have hGlobal := (ae_restrict_iff' hO).mp hP
  have hShift := ((volume : Measure (Point n)).measurePreserving_sub_left p).quasiMeasurePreserving.ae hGlobal
  have hAC : autoJointMollifierMeasure n eps ≪ (volume : Measure (Point n)) :=
    withDensity_absolutelyContinuous _ _
  have hShiftNu := hShift.filter_mono hAC.ae_le
  filter_upwards [hShiftNu,autoJointMollifierMeasure_ball_ae heps] with q hq hball
  exact hq (hRegion q hball)

/-- The actual smooth joint Hessian is the genuine average of the measurable
directional Peano limit. This follows from exact finite differences and DCT. -/
theorem auto_joint_mollify_second_representation_along {n : ℕ} {O : Set (Point n)}
    (hO : MeasurableSet O) {eps : ℝ} (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) {H : Point n → ℝ} (hH : Measurable H)
    (e : Space n) (p : Point n)
    (hRegion : ∀ q∈Metric.ball (0 : Point n) eps, p-q∈O)
    (h : ℕ → ℝ) (hpos : ∀ j, 0 < h j) (hzero : Tendsto h atTop (𝓝 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ j, ∀ z∈O, |autoSecond w e (h j) z| ≤ B)
    (hLimit : ∀ᵐ z ∂((volume : Measure (Point n)).restrict O),
      Tendsto (fun j => autoSecond w e (h j) z) atTop (𝓝 (H z))) :
    Integrable (fun q => H (p-q)) (autoJointMollifierMeasure n eps) ∧
      fderiv ℝ (fderiv ℝ (abpMollify eps w)) p (e,0) (e,0)=
        ∫ q, H (p-q) ∂autoJointMollifierMeasure n eps := by
  let nu := autoJointMollifierMeasure n eps
  let : IsProbabilityMeasure nu := autoJointMollifierMeasure_isProbability heps
  have hLimitNu := autoJointMollifierMeasure_ae_sub heps hO p hRegion hLimit
  have hBoundNu (j : ℕ) : ∀ᵐ q ∂nu, ‖autoSecond w e (h j) (p-q)‖ ≤ B := by
    filter_upwards [autoJointMollifierMeasure_ball_ae heps] with q hq
    simpa only [Real.norm_eq_abs] using hBound j _ (hRegion q hq)
  have hBoundAll : ∀ᵐ q ∂nu, ∀ j, ‖autoSecond w e (h j) (p-q)‖ ≤ B :=
    ae_all_iff.mpr hBoundNu
  have hInt : Integrable (fun q => H (p-q)) nu := by
    apply (integrable_const B).mono' (hH.comp (continuous_const.sub continuous_id).measurable).aestronglyMeasurable
    filter_upwards [hLimitNu,hBoundAll] with q hq hqb
    exact le_of_tendsto hq.norm (Eventually.of_forall hqb)
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ : Point n => B)
    (fun j => ((autoSecond_continuous w.continuous e (h j)).comp
      (continuous_const.sub continuous_id)).stronglyMeasurable.aestronglyMeasurable)
    (integrable_const B) hBoundNu hLimitNu
  have hpositive : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero,Eventually.of_forall hpos⟩
  have hSmooth := abpMollify_smooth heps w.continuous
  have hActual := (auto_joint_second_limit hSmooth p e).comp hpositive
  simp only [Function.comp_def,Pi.sub_apply,id_eq] at hActual hDCT
  have hPair : (fun j => autoSecond (abpMollify eps w) e (h j) p)=
      (fun j => ∫ q, autoSecond w e (h j) (p-q) ∂nu) := by
    funext j
    exact (auto_joint_mollify_second heps w e (h j) p).2
  rw [hPair] at hActual
  exact ⟨hInt,tendsto_nhds_unique hActual hDCT⟩

/-- The upper budget is retained exactly, including when it is negative. -/
theorem auto_joint_mollify_second_upper_along {n : ℕ} {O : Set (Point n)}
    (hO : MeasurableSet O) {eps : ℝ} (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) {H : Point n → ℝ} (hH : Measurable H)
    (e : Space n) (p : Point n)
    (hRegion : ∀ q∈Metric.ball (0 : Point n) eps, p-q∈O)
    (h : ℕ → ℝ) (hpos : ∀ j, 0 < h j) (hzero : Tendsto h atTop (𝓝 0))
    {B M : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ j, ∀ z∈O, |autoSecond w e (h j) z| ≤ B)
    (hLimit : ∀ᵐ z ∂((volume : Measure (Point n)).restrict O),
      Tendsto (fun j => autoSecond w e (h j) z) atTop (𝓝 (H z)))
    (hUpper : ∀ᵐ z ∂((volume : Measure (Point n)).restrict O), H z ≤ M) :
    fderiv ℝ (fderiv ℝ (abpMollify eps w)) p (e,0) (e,0) ≤ M := by
  obtain ⟨hInt,hEq⟩ := auto_joint_mollify_second_representation_along hO heps w hH e p hRegion
    h hpos hzero hB hBound hLimit
  let : IsProbabilityMeasure (autoJointMollifierMeasure n eps) := autoJointMollifierMeasure_isProbability heps
  rw [hEq]
  have hm := integral_mono_ae hInt (integrable_const M)
    (autoJointMollifierMeasure_ae_sub heps hO p hRegion hUpper)
  simpa only [integral_const,probReal_univ,one_smul] using hm

end Yau.LeafProofs.L05AutonomousAux
