import Yau.LeafProofs.L16TraceLayerNormal

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The actual tangent-location derivative of the boundary trace layer. The
normal parameter is independent here; the geometric tangent projection is
applied only after these genuine convolution derivatives are proved. -/
def normalTraceTangential {n : ℕ} (B : Point n → ℝ) (t a : ℝ) (ξ : Space n) :
    Space n →L[ℝ] ℝ :=
  ∫ r in (0 : ℝ)..t, normalHeatProfile r a •
    fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ

def normalTraceTangentialSecond {n : ℕ} (B : Point n → ℝ) (t a : ℝ) (ξ : Space n) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  ∫ r in (0 : ℝ)..t, normalHeatProfile r a •
    fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ

/-- Existing genuine heat-gradient time integrability survives the actual
    age/source-time reversal in the trace-layer formula. -/
theorem retardedHeatAverage_fderiv_time_integrable {n : ℕ} {F t : ℝ}
    {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (ht : 0 < t) (ξ : Space n) :
    IntervalIntegrable (fun r : ℝ => fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ)
      volume 0 t := by
  simpa only [sub_zero,sub_self,sub_sub_cancel] using
    ((heatAverage_fderiv_time_integrable hB hF ht ξ).comp_sub_left t).symm

/-- Tangent-location differentiation of the true layer, with its actual
    integrable heat-gradient kernel. -/
theorem normalTraceLayer_hasFDerivAt_tangent {n : ℕ} {F t a : ℝ}
    {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (ht : 0 < t) (ha : 0 ≤ a) (ξ : Space n) :
    HasFDerivAt (fun z => normalTraceLayer B z t a) (normalTraceTangential B t a ξ) ξ := by
  obtain ⟨C,hC,hGrad⟩ := heatAverage_fderiv_bound_of_bounded (n := n)
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  have hμ : μ ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hHm := (normalHeatProfile_time_aestronglyMeasurable a).mono_measure hμ
  have hAvgI (z : Space n) : Integrable
      (fun r => normalHeatProfile r a*heatAverage r (fun y => B (y,t-r)) z) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (normalTraceLayer_integrable_and_bound hB hF ht.le ha z).1
  have hGm : AEStronglyMeasurable
      (fun r => normalHeatProfile r a • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ) μ :=
    hHm.smul ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (retardedHeatAverage_fderiv_time_integrable hB hF ht ξ)).aestronglyMeasurable
  have hPower : IntervalIntegrable (fun r : ℝ => r^(-(1/2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hBI : Integrable (fun r : ℝ => C*F*r^(-(1/2 : ℝ))) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPower.const_mul (C*F))
  have hDerivBound : ∀ᵐ r ∂μ, ∀ z ∈ Metric.ball ξ 1,
      ‖normalHeatProfile r a • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) z‖ ≤
        C*F*r^(-(1/2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro z hz
    obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr.1 ha
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hh1).trans
      (hGrad r hr.1 (fun y => B (y,t-r)) F
        (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) z)
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ)
    (F := fun z r => normalHeatProfile r a*heatAverage r (fun y => B (y,t-r)) z)
    (F' := fun z r => normalHeatProfile r a • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) z)
    (s := Metric.ball ξ 1) (bound := fun r => C*F*r^(-(1/2 : ℝ)))
    (Metric.ball_mem_nhds ξ (by norm_num))
    (Eventually.of_forall fun z => (hAvgI z).aestronglyMeasurable)
    (hAvgI ξ) hGm hDerivBound hBI (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      intro z hz
      exact ((heatAverage_hasFDerivAt_kernel_of_bounded hr.1
        (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) z).differentiableAt.hasFDerivAt.const_smul (normalHeatProfile r a)))
  have hFun : (fun z => ∫ r, normalHeatProfile r a*heatAverage r (fun y => B (y,t-r)) z ∂μ) =
      fun z => normalTraceLayer B z t a := by
    funext z
    rw [normalTraceLayer,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  rw [hFun] at hh
  convert hh using 1
  rw [normalTraceTangential,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]

/-- The cancelled Gaussian Hessian remains genuinely integrable in the
    retarded trace-layer coordinates. -/
theorem retardedHeatAverage_secondFDeriv_time_integrable {n : ℕ} {α F H t : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (ξ : Space n) :
    IntervalIntegrable (fun r : ℝ =>
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ) volume 0 t := by
  simpa only [sub_zero,sub_self,sub_sub_cancel] using
    ((heatAverage_secondFDeriv_time_integrable hα hB hF hH0 hH ht ξ).comp_sub_left t).symm

/-- A genuine second tangent-location derivative of the boundary trace layer.
    The source is only bounded, continuous, and spatially Holder. -/
theorem normalTraceTangential_hasFDerivAt {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (ha : 0 ≤ a) (ξ : Space n) :
    HasFDerivAt (normalTraceTangential B t a) (normalTraceTangentialSecond B t a ξ) ξ := by
  obtain ⟨C,hC,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  have hμ : μ ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hHm := (normalHeatProfile_time_aestronglyMeasurable a).mono_measure hμ
  have hHb : ∀ᵐ r ∂μ, ‖normalHeatProfile r a‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (normalHeatProfile_bounds hr.1 ha).1]
    exact (normalHeatProfile_bounds hr.1 ha).2
  have hGI (z : Space n) : Integrable
      (fun r => normalHeatProfile r a • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) z) μ :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (retardedHeatAverage_fderiv_time_integrable hB hF ht z)).bdd_smul 1 hHm hHb
  have hHI : Integrable
      (fun r => fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (retardedHeatAverage_secondFDeriv_time_integrable hα hB hF hH0 hH ht ξ)
  have hPower : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hBI : Integrable (fun r : ℝ => C*H*r^(α/2-1)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPower.const_mul (C*H))
  have hDerivBound : ∀ᵐ r ∂μ, ∀ z ∈ Metric.ball ξ 1,
      ‖normalHeatProfile r a • fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) z‖ ≤
        C*H*r^(α/2-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro z hz
    obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr.1 ha
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hh1).trans
      (hHess r hr.1 (fun y => B (y,t-r)) F H
        (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) hH0 (hH (t-r)) z)
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ)
    (F := fun z r => normalHeatProfile r a • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) z)
    (F' := fun z r => normalHeatProfile r a • fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) z)
    (s := Metric.ball ξ 1) (bound := fun r => C*H*r^(α/2-1))
    (Metric.ball_mem_nhds ξ (by norm_num))
    (Eventually.of_forall fun z => (hGI z).aestronglyMeasurable)
    (hGI ξ) (hHm.smul hHI.aestronglyMeasurable) hDerivBound hBI (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      intro z hz
      exact ((heatAverage_fderiv_hasFDerivAt_kernel_of_bounded hr.1
        (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) z).differentiableAt.hasFDerivAt.const_smul (normalHeatProfile r a)))
  have hFun : (fun z => ∫ r, normalHeatProfile r a •
      fderiv ℝ (heatAverage r (fun y => B (y,t-r))) z ∂μ) = normalTraceTangential B t a := by
    funext z
    rw [normalTraceTangential,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  rw [hFun] at hh
  convert hh using 1
  rw [normalTraceTangentialSecond,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]

/-- Identification of the actual iterated tangent derivative with its honest
    cancelled integral candidate. -/
theorem normalTraceLayer_secondFDeriv_tangent {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (ha : 0 ≤ a) (ξ : Space n) :
    fderiv ℝ (fderiv ℝ (fun z => normalTraceLayer B z t a)) ξ = normalTraceTangentialSecond B t a ξ := by
  have hFun : fderiv ℝ (fun z => normalTraceLayer B z t a) = normalTraceTangential B t a := by
    funext z
    exact (normalTraceLayer_hasFDerivAt_tangent hB hF ht ha z).fderiv
  rw [hFun]
  exact (normalTraceTangential_hasFDerivAt hα hB hF hH0 hH ht ha ξ).fderiv

theorem normalTraceTangential_initial {n : ℕ} (B : Point n → ℝ) (a : ℝ) (ξ : Space n) :
    normalTraceTangential B 0 a ξ = 0 := by
  simp only [normalTraceTangential,intervalIntegral.integral_same]

theorem normalTraceTangentialSecond_initial {n : ℕ} (B : Point n → ℝ) (a : ℝ) (ξ : Space n) :
    normalTraceTangentialSecond B 0 a ξ = 0 := by
  simp only [normalTraceTangentialSecond,intervalIntegral.integral_same]

theorem normalTraceTangential_boundary {n : ℕ} (B : Point n → ℝ) (t : ℝ) (ξ : Space n) :
    normalTraceTangential B t 0 ξ = 0 := by
  simp only [normalTraceTangential,normalHeatProfile_zero,zero_smul,intervalIntegral.integral_zero]

theorem normalTraceTangentialSecond_boundary {n : ℕ} (B : Point n → ℝ) (t : ℝ) (ξ : Space n) :
    normalTraceTangentialSecond B t 0 ξ = 0 := by
  simp only [normalTraceTangentialSecond,normalHeatProfile_zero,zero_smul,intervalIntegral.integral_zero]

/-- A quantitative bound on the actual tangent Hessian candidate, with its
    vanishing initial-time factor and constant fixed before the source. -/
theorem normalTraceTangentialSecond_bound {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α) →
      ∀ t : ℝ, 0 ≤ t → ∀ a : ℝ, 0 ≤ a → ∀ ξ : Space n,
        ‖normalTraceTangentialSecond B t a ξ‖ ≤ C*H*t^(α/2) := by
  obtain ⟨C,hC,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  refine ⟨C*(2/α),by positivity,?_⟩
  intro B F H hB hF hH0 hH t ht a ha ξ
  rcases ht.eq_or_lt with rfl | ht
  · rw [normalTraceTangentialSecond_initial,norm_zero]
    positivity
  have hPower : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hBI : Integrable (fun r : ℝ => C*H*r^(α/2-1)) (volume.restrict (Ioo 0 t)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPower.const_mul (C*H))
  have hInt : (∫ r in Ioo (0 : ℝ) t, r^(α/2-1)) = (2/α)*t^(α/2) := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le ht.le,
      integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
      show α/2-1+1 = α/2 by ring,Real.zero_rpow (by linarith : α/2 ≠ 0),sub_zero]
    field_simp
  rw [normalTraceTangentialSecond,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ r in Ioo (0 : ℝ) t, C*H*r^(α/2-1) := by
      apply norm_integral_le_of_norm_le hBI
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr.1 ha
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh0]
      exact (mul_le_of_le_one_left (norm_nonneg _) hh1).trans
        (hHess r hr.1 (fun y => B (y,t-r)) F H
          (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) hH0 (hH (t-r)) ξ)
    _ = (C*(2/α))*H*t^(α/2) := by rw [integral_const_mul,hInt]; ring

end Yau.LeafProofs.L16Aux
