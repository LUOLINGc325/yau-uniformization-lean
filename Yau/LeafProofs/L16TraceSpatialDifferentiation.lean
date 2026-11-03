import Yau.LeafProofs.L16TraceSpatialLayer

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceSpatialDifferentiation_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceSpatialDifferentiation_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- Differentiation under the genuine spatial trace-layer integral on the
    strict half space, with no smoothness of the source assumed. -/
theorem boundaryTraceLayer_hasFDerivAt {n : ℕ} {F t : ℝ}
    {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (ht : 0 < t) {x : Space n} (hx : 0 < inner ℝ e x) :
    IntervalIntegrable (traceSpatialGradientKernel e B t x) volume 0 t ∧
      HasFDerivAt (fun z => boundaryTraceLayer e B (z,t))
        (∫ r in (0 : ℝ)..t, traceSpatialGradientKernel e B t x r) x := by
  obtain ⟨C,hC,hKernelBound⟩ := traceSpatialGradientKernel_bound (n := n)
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  let P := halfSpaceBoundaryProjection e
  let N := innerSL ℝ e
  have hμ : μ ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hGI : Integrable (fun r => fderiv ℝ (heatAverage r (fun y => B (y,t-r))) (P x)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (retardedHeatAverage_fderiv_time_integrable hB hF ht (P x))
  have hGComp : AEStronglyMeasurable
      (fun r => (fderiv ℝ (heatAverage r (fun y => B (y,t-r))) (P x)).comp P) μ :=
    (continuous_id.clm_comp_const P).comp_aestronglyMeasurable hGI.aestronglyMeasurable
  have hKMeas : AEStronglyMeasurable (traceSpatialGradientKernel e B t x) μ := by
    have hT := ((normalHeatProfile_time_aestronglyMeasurable (inner ℝ e x)).mono_measure hμ).smul hGComp
    have hNormal := ((((normalGaussianKernel_time_measurable (inner ℝ e x)).const_mul 2).aestronglyMeasurable.mul ((retardedHeatAverage_aestronglyMeasurable hB (P x,t)).mono_measure hμ)).smul_const N)
    exact hT.add hNormal
  have hPower : IntervalIntegrable (fun r : ℝ => r^(-(1/2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hBI : Integrable (fun r : ℝ => C*F*r^(-(1/2 : ℝ))) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPower.const_mul (C*F))
  have hHeight (z : Space n) (hz : z ∈ Metric.ball x (inner ℝ e x/2)) : 0 ≤ inner ℝ e z := by
    have hDiff := abs_real_inner_le_norm e (z-x)
    rw [inner_sub_right,he,one_mul] at hDiff
    have hzN : ‖z-x‖ < inner ℝ e x/2 := by
      simpa only [Metric.mem_ball,dist_eq_norm] using hz
    have hLower := neg_le_abs (inner ℝ e z-inner ℝ e x)
    nlinarith
  have hDom : ∀ᵐ r ∂μ, ∀ z ∈ Metric.ball x (inner ℝ e x/2),
      ‖traceSpatialGradientKernel e B t z r‖ ≤ C*F*r^(-(1/2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro z hz
    exact hKernelBound e he B F hB hF r hr.1 t z (hHeight z hz)
  have hKI : Integrable (traceSpatialGradientKernel e B t x) μ := by
    apply hBI.mono' hKMeas
    filter_upwards [hDom] with r hr
    exact hr x (Metric.mem_ball_self (by positivity))
  have hValueMeas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable
      (fun r => normalHeatProfile r (inner ℝ e z)*heatAverage r (fun y => B (y,t-r)) (P z)) μ :=
    Eventually.of_forall fun z =>
      ((normalHeatProfile_time_aestronglyMeasurable (inner ℝ e z)).mono_measure hμ).mul
        ((retardedHeatAverage_aestronglyMeasurable hB (P z,t)).mono_measure hμ)
  have hValueI : Integrable
      (fun r => normalHeatProfile r (inner ℝ e x)*heatAverage r (fun y => B (y,t-r)) (P x)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (normalTraceLayer_integrable_and_bound hB hF ht.le hx.le (P x)).1
  have hD : ∀ᵐ r ∂μ, ∀ z ∈ Metric.ball x (inner ℝ e x/2),
      HasFDerivAt (fun y => normalHeatProfile r (inner ℝ e y)*
        heatAverage r (fun w => B (w,t-r)) (P y)) (traceSpatialGradientKernel e B t z r) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro z hz
    have hProfile := (normalHeatProfile_hasDerivAt r (inner ℝ e z)).comp_hasFDerivAt z N.hasFDerivAt
    have hAvg := ((heatAverage_hasFDerivAt_kernel_of_bounded hr.1
      (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) (P z)).differentiableAt.hasFDerivAt).comp z P.hasFDerivAt
    have hh := hProfile.mul hAvg
    convert hh using 1 <;> try rfl
    ext v
    simp [traceSpatialGradientKernel,P,N,Function.comp_def,Pi.mul_apply,smul_smul,
      mul_comm,mul_left_comm,mul_assoc]
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ)
    (F := fun z r => normalHeatProfile r (inner ℝ e z)*heatAverage r (fun y => B (y,t-r)) (P z))
    (F' := fun z r => traceSpatialGradientKernel e B t z r)
    (s := Metric.ball x (inner ℝ e x/2)) (bound := fun r => C*F*r^(-(1/2 : ℝ)))
    (Metric.ball_mem_nhds x (by positivity)) hValueMeas hValueI hKMeas hDom hBI hD
  have hFun : (fun z => ∫ r, normalHeatProfile r (inner ℝ e z)*
      heatAverage r (fun y => B (y,t-r)) (P z) ∂μ) = fun z => boundaryTraceLayer e B (z,t) := by
    funext z
    rw [boundaryTraceLayer,normalTraceLayer,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  rw [hFun] at hh
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr hKI,?_⟩
  convert hh using 1
  rw [intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]

end Yau.LeafProofs.L16Aux
