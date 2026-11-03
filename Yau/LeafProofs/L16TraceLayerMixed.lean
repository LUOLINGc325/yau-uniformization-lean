import Yau.LeafProofs.L16TraceLayerTangential
import Yau.LeafProofs.L16TraceGradientHolder

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- The actual mixed normal--tangent kernel integral. -/
def normalTraceMixed {n : ℕ} (B : Point n → ℝ) (t a : ℝ) (ξ : Space n) :
    Space n →L[ℝ] ℝ :=
  ∫ r in (0 : ℝ)..t, (2*normalGaussianKernel r a) •
    fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ

/-- Cancellation in the first Gaussian derivative gives the integrable actual
    mixed-kernel bound, uniformly in the normal parameter. -/
theorem traceMixedKernel_bound {n : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α) →
      ∀ r : ℝ, 0 < r → ∀ t a : ℝ, ∀ ξ : Space n,
        ‖(2*normalGaussianKernel r a) • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ‖ ≤
          C*H*r^(α/2-1) := by
  obtain ⟨C,hC,hGrad⟩ := heatAverage_fderiv_holder_bound (n := n) hα
  let Cg : ℝ := 2*(Real.sqrt (4*Real.pi))⁻¹
  have hCg : 0 < Cg := by dsimp only [Cg]; positivity
  refine ⟨Cg*C,by positivity,?_⟩
  intro B F H hB hF hH0 hH r hr t a ξ
  have hK0 : 0 ≤ 2*normalGaussianKernel r a :=
    mul_nonneg (by norm_num) (normalGaussianKernel_pos hr a).le
  have hK : 2*normalGaussianKernel r a ≤ Cg*r^(-(1/2 : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left (normalGaussianKernel_le_rpow hr a) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [Cg,mul_assoc] using h
  have hG := hGrad r hr (fun y => B (y,t-r)) F H
    (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) hH0 (hH (t-r)) ξ
  have hPow : r^(-(1/2 : ℝ))*r^(α/2-1/2) = r^(α/2-1) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hK0]
  calc
    _ ≤ (Cg*r^(-(1/2 : ℝ)))*(C*H*r^(α/2-1/2)) :=
      mul_le_mul hK hG (norm_nonneg _) (by positivity)
    _ = (Cg*C)*H*(r^(-(1/2 : ℝ))*r^(α/2-1/2)) := by ring
    _ = _ := by rw [hPow]

/-- Tangential differentiation of the actual first normal derivative. -/
theorem normalTraceFirst_hasFDerivAt_tangent {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (ha : 0 ≤ a) (ξ : Space n) :
    HasFDerivAt (fun z => normalTraceFirst B z t a) (normalTraceMixed B t a ξ) ξ := by
  obtain ⟨C,hC,hMixed⟩ := traceMixedKernel_bound (n := n) hα.le
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  have hAvgI (z : Space n) : Integrable
      (fun r => (2*normalGaussianKernel r a)*heatAverage r (fun y => B (y,t-r)) z) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (normalTraceLayer_hasDerivAt hB hF ht.le ha z).1
  have hGm : AEStronglyMeasurable
      (fun r => (2*normalGaussianKernel r a) • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ) μ :=
    ((normalGaussianKernel_time_measurable a).const_mul 2).aestronglyMeasurable.smul
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
        (retardedHeatAverage_fderiv_time_integrable hB hF ht ξ)).aestronglyMeasurable
  have hPower : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hBI : Integrable (fun r : ℝ => C*H*r^(α/2-1)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPower.const_mul (C*H))
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ)
    (F := fun z r => (2*normalGaussianKernel r a)*heatAverage r (fun y => B (y,t-r)) z)
    (F' := fun z r => (2*normalGaussianKernel r a) • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) z)
    (s := Metric.ball ξ 1) (bound := fun r => C*H*r^(α/2-1))
    (Metric.ball_mem_nhds ξ (by norm_num))
    (Eventually.of_forall fun z => (hAvgI z).aestronglyMeasurable) (hAvgI ξ) hGm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      intro z hz
      exact hMixed B F H hB hF hH0 hH r hr.1 t a z) hBI (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      intro z hz
      exact ((heatAverage_hasFDerivAt_kernel_of_bounded hr.1
        (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) z).differentiableAt.hasFDerivAt.const_smul (2*normalGaussianKernel r a)))
  have hFun : (fun z => ∫ r, (2*normalGaussianKernel r a)*heatAverage r (fun y => B (y,t-r)) z ∂μ) =
      fun z => normalTraceFirst B z t a := by
    funext z
    rw [normalTraceFirst,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  rw [hFun] at hh
  convert hh using 1
  rw [normalTraceMixed,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]

/-- The other mixed derivative is also an actual derivative, including the
    normal face; no extra derivative of the source is assumed. -/
theorem normalTraceTangential_hasDerivAt_normal {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (ha : 0 ≤ a) (ξ : Space n) :
    HasDerivAt (fun b => normalTraceTangential B t b ξ) (normalTraceMixed B t a ξ) a := by
  obtain ⟨C,hC,hMixed⟩ := traceMixedKernel_bound (n := n) hα.le
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  let G : ℝ → Space n →L[ℝ] ℝ := fun r => fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ
  have hμ : μ ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hGI : Integrable G μ := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
    (retardedHeatAverage_fderiv_time_integrable hB hF ht ξ)
  have hMeas : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (fun r => normalHeatProfile r b • G r) μ :=
    Eventually.of_forall fun b =>
      ((normalHeatProfile_time_aestronglyMeasurable b).mono_measure hμ).smul hGI.aestronglyMeasurable
  have hHb : ∀ᵐ r ∂μ, ‖normalHeatProfile r a‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (normalHeatProfile_bounds hr.1 ha).1]
    exact (normalHeatProfile_bounds hr.1 ha).2
  have hInt : Integrable (fun r => normalHeatProfile r a • G r) μ :=
    hGI.bdd_smul 1 ((normalHeatProfile_time_aestronglyMeasurable a).mono_measure hμ) hHb
  have hDMeas : AEStronglyMeasurable (fun r => (2*normalGaussianKernel r a) • G r) μ :=
    ((normalGaussianKernel_time_measurable a).const_mul 2).aestronglyMeasurable.smul hGI.aestronglyMeasurable
  have hPower : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hBI : Integrable (fun r : ℝ => C*H*r^(α/2-1)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPower.const_mul (C*H))
  have hBound : ∀ᵐ r ∂μ, ∀ b ∈ (Set.univ : Set ℝ),
      ‖(2*normalGaussianKernel r b) • G r‖ ≤ C*H*r^(α/2-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro b hb
    exact hMixed B F H hB hF hH0 hH r hr.1 t b ξ
  have hD : ∀ᵐ r ∂μ, ∀ b ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun c => normalHeatProfile r c • G r) ((2*normalGaussianKernel r b) • G r) b :=
    Eventually.of_forall fun r b hb => (normalHeatProfile_hasDerivAt r b).smul_const (G r)
  obtain ⟨hi,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (x₀ := a) Filter.univ_mem hMeas hInt hDMeas hBound hBI hD
  have hFun : (fun b => ∫ r, normalHeatProfile r b • G r ∂μ) =
      fun b => normalTraceTangential B t b ξ := by
    funext b
    rw [normalTraceTangential,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  rw [hFun] at hd
  convert hd using 1
  rw [normalTraceMixed,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]

theorem normalTraceMixed_initial {n : ℕ} (B : Point n → ℝ) (a : ℝ) (ξ : Space n) :
    normalTraceMixed B 0 a ξ = 0 := by
  simp only [normalTraceMixed,intervalIntegral.integral_same]

/-- The true mixed jet vanishes quantitatively at the initial time, uniformly
    up to the normal face. -/
theorem normalTraceMixed_bound {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α) →
      ∀ t : ℝ, 0 ≤ t → ∀ a : ℝ, ∀ ξ : Space n,
        ‖normalTraceMixed B t a ξ‖ ≤ C*H*t^(α/2) := by
  obtain ⟨C,hC,hMixed⟩ := traceMixedKernel_bound (n := n) hα.le
  refine ⟨C*(2/α),by positivity,?_⟩
  intro B F H hB hF hH0 hH t ht a ξ
  rcases ht.eq_or_lt with rfl | ht
  · rw [normalTraceMixed_initial,norm_zero]
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
  rw [normalTraceMixed,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ r in Ioo (0 : ℝ) t, C*H*r^(α/2-1) := by
      apply norm_integral_le_of_norm_le hBI
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hMixed B F H hB hF hH0 hH r hr.1 t a ξ
    _ = (C*(2/α))*H*t^(α/2) := by rw [integral_const_mul,hInt]; ring

end Yau.LeafProofs.L16Aux
