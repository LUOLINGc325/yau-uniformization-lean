import Yau.LeafProofs.L16TraceHessianOperators

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceSpatialHessian_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceSpatialHessian_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceSpatialHessian_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceSpatialHessian_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The actual full spatial Hessian follows by differentiating the true
    gradient kernel; the normal term is dominated by one fixed Poisson density
    on a strictly positive-height neighborhood. -/
theorem boundaryTraceGradient_hasFDerivAt {n : ℕ} {α F H t : ℝ}
    (hα : 0 < α) {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) {x : Space n} (hx : 0 < inner ℝ e x) :
    IntervalIntegrable (traceSpatialHessianKernel e B t x) volume 0 t ∧
      HasFDerivAt (fun z => boundaryTraceGradient e B (z,t))
        (∫ r in (0 : ℝ)..t, traceSpatialHessianKernel e B t x r) x := by
  obtain ⟨C,hC,hBound⟩ := traceSpatialHessianKernel_bound (n := n) hα.le
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  let P := halfSpaceBoundaryProjection e
  let a := inner ℝ e x
  have ha : 0 < a := hx
  let ξ := P x
  let R := (innerSL ℝ e).smulRight (innerSL ℝ e)
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  have hμ : μ ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hDG := ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
    (retardedHeatAverage_fderiv_time_integrable hB hF ht ξ)).aestronglyMeasurable
  have hD2G := ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
    (retardedHeatAverage_secondFDeriv_time_integrable hα hB hF hH0 hH ht ξ)).aestronglyMeasurable
  have hHm := (normalHeatProfile_time_aestronglyMeasurable a).mono_measure hμ
  have hGM := ((normalGaussianKernel_time_measurable a).const_mul 2).aestronglyMeasurable.smul hDG
  have hVM := (traceNormalTensorMap e).continuous.comp_aestronglyMeasurable
    ((traceGradientPullback P).continuous.comp_aestronglyMeasurable hGM)
  have hFlip := (ContinuousLinearMap.flipₗᵢ ℝ (Space n) (Space n) ℝ).continuous.comp_aestronglyMeasurable hVM
  have hNM := ((normalPoissonKernel_measurable a).aestronglyMeasurable.mul
    ((retardedHeatAverage_aestronglyMeasurable hB (ξ,t)).mono_measure hμ)).smul_const R
  have hHMeas : AEStronglyMeasurable (traceSpatialHessianKernel e B t x) μ :=
    (((hHm.smul ((traceHessianPullback P).continuous.comp_aestronglyMeasurable hD2G)).add hVM).add hFlip).sub hNM
  have hHeight (z : Space n) (hz : z ∈ Metric.ball x (a/2)) :
      a/2 ≤ inner ℝ e z ∧ inner ℝ e z ≤ 3*(a/2) := by
    change inner ℝ e x/2 ≤ inner ℝ e z ∧ inner ℝ e z ≤ 3*(inner ℝ e x/2)
    have hDiff := abs_real_inner_le_norm e (z-x)
    rw [inner_sub_right,he,one_mul] at hDiff
    have hzN : ‖z-x‖ < inner ℝ e x/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
    constructor <;> nlinarith [neg_le_abs (inner ℝ e z-inner ℝ e x),le_abs_self (inner ℝ e z-inner ℝ e x)]
  have hDom : ∀ᵐ r ∂μ, ∀ z ∈ Metric.ball x (a/2),
      ‖traceSpatialHessianKernel e B t z r‖ ≤ C*H*r^(α/2-1)+(3*F)*normalPoissonKernel (a/2) r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro z hz
    obtain ⟨hlo,hhi⟩ := hHeight z hz
    have hPos : 0 ≤ inner ℝ e z := (by positivity : 0 ≤ a/2).trans hlo
    have hK := hBound e he B F H hB hF hH0 hH r hr.1 t z hPos
    have hp := normalPoissonKernel_le_near hr.1 hx hlo hhi
    have hFP := mul_le_mul_of_nonneg_left hp hF0
    nlinarith
  have hPower : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hPInt : Integrable (normalPoissonKernel (a/2)) μ :=
    Integrable.mono_measure (normalPoissonKernel_probability (by positivity : 0 < a/2)).1 hμ
  have hBI : Integrable (fun r : ℝ => C*H*r^(α/2-1)+(3*F)*normalPoissonKernel (a/2) r) μ := by
    change Integrable ((fun r : ℝ => C*H*r^(α/2-1))+(fun r => (3*F)*normalPoissonKernel (a/2) r)) μ
    exact (((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp hPower).const_mul (C*H)).add
      (hPInt.const_mul (3*F))
  have hHInt : Integrable (traceSpatialHessianKernel e B t x) μ := by
    apply hBI.mono' hHMeas
    filter_upwards [hDom] with r hr
    exact hr x (Metric.mem_ball_self (by positivity))
  have hValueMeas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (traceSpatialGradientKernel e B t z) μ := by
    filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < a/2)] with z hz
    have hPos : 0 ≤ inner ℝ e z := (by positivity : 0 ≤ a/2).trans (hHeight z hz).1
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (traceSpatialGradientKernel_integral hB hF ht.le e z hPos).1).aestronglyMeasurable
  have hValueI := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
    (traceSpatialGradientKernel_integral hB hF ht.le e x hx.le).1
  have hD : ∀ᵐ r ∂μ, ∀ z ∈ Metric.ball x (a/2),
      HasFDerivAt (fun y => traceSpatialGradientKernel e B t y r) (traceSpatialHessianKernel e B t z r) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro z hz
    exact traceSpatialGradientKernel_hasFDerivAt hr.1 e hB hF z
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (F := fun z r => traceSpatialGradientKernel e B t z r)
    (F' := fun z r => traceSpatialHessianKernel e B t z r)
    (s := Metric.ball x (a/2)) (bound := fun r => C*H*r^(α/2-1)+(3*F)*normalPoissonKernel (a/2) r)
    (Metric.ball_mem_nhds x (by positivity)) hValueMeas hValueI hHMeas hDom hBI hD
  have hNear : (fun z => boundaryTraceGradient e B (z,t)) =ᶠ[𝓝 x]
      (fun z => ∫ r, traceSpatialGradientKernel e B t z r ∂μ) := by
    filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < a/2)] with z hz
    have hPos : 0 ≤ inner ℝ e z := (by positivity : 0 ≤ a/2).trans (hHeight z hz).1
    rw [← (traceSpatialGradientKernel_integral hB hF ht.le e z hPos).2,
      intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  have hField := hh.congr_of_eventuallyEq hNear
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr hHInt,?_⟩
  convert hField using 1
  rw [intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]

end Yau.LeafProofs.L16Aux
