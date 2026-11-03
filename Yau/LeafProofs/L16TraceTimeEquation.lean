import Yau.LeafProofs.L16TraceTimeKernel
import Yau.LeafProofs.L16TraceAgeNorm

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The true causal time derivative of the layer, before rewriting its tangent
    and normal Hessian entries. -/
def normalTraceAgeTimeDerivative {n : ℕ} (B : Point n → ℝ) (t a : ℝ) (ξ : Space n) : ℝ :=
  ∫ s in (0 : ℝ)..t, traceTimeKernel B a ξ (t,s)

/-- Actual triangle Fubini applied to the true age primitive gives the
    integrated time equation of the boundary layer. -/
theorem normalTraceLayer_integrated_time_equation {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (ha : 0 < a) (ξ : Space n) :
    IntervalIntegrable (fun r => normalTraceAgeTimeDerivative B r a ξ) volume 0 t ∧
      normalTraceLayer B ξ t a = (∫ s in (0 : ℝ)..t, B (ξ,s))+
        ∫ r in (0 : ℝ)..t, normalTraceAgeTimeDerivative B r a ξ := by
  obtain ⟨C,hC,hAge⟩ := normalHeatAverage_age_norm_integral_bound (n := n) hα
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioo]⟩
  let K := traceTimeKernel B a ξ
  let D : ℝ → ℝ → ℝ := fun r s => -normalPoissonKernel a r*heatAverage r (fun y => B (y,s)) ξ+
    normalHeatProfile r a*heatLaplacian (heatAverage r (fun y => B (y,s))) ξ
  have hKm : StronglyMeasurable K := traceTimeKernel_stronglyMeasurable ha.le hB hF ξ
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  have hfc (s : ℝ) : Continuous (fun y : Space n => B (y,s)) :=
    hB.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |B (y,s)| ≤ F := hF (y,s)
  have hRightSet (s : ℝ) (hs : s ∈ Set.Ioo 0 t) :
      Set.Ioi s ∩ Set.Ioo (0 : ℝ) t = Set.Ioo s t := by
    ext r
    simp only [Set.mem_inter_iff,Set.mem_Ioi,Set.mem_Ioo]
    constructor
    · intro h
      exact ⟨h.1,h.2.2⟩
    · intro h
      exact ⟨h.1,hs.1.trans h.1,h.2⟩
  have hLeftSet (r : ℝ) (hr : r ∈ Set.Ioo 0 t) :
      Set.Iio r ∩ Set.Ioo (0 : ℝ) t = Set.Ioo 0 r := by
    ext s
    simp only [Set.mem_inter_iff,Set.mem_Iio,Set.mem_Ioo]
    constructor
    · intro h
      exact ⟨h.2.1,h.1⟩
    · intro h
      exact ⟨h.2,h.1,h.2.trans hr.2⟩
  have hright (s : ℝ) (hs : s ∈ Set.Ioo 0 t) (L : ℝ → ℝ) :
      (∫ r, (Set.Ioi s).indicator L r ∂μ) = ∫ r in s..t, L r := by
    rw [integral_indicator measurableSet_Ioi]
    change (∫ r, L r ∂((volume.restrict (Set.Ioo 0 t)).restrict (Set.Ioi s))) = _
    rw [Measure.restrict_restrict measurableSet_Ioi,hRightSet s hs,
      ← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hs.2.le]
  have hleft (r : ℝ) (hr : r ∈ Set.Ioo 0 t) (L : ℝ → ℝ) :
      (∫ s, (Set.Iio r).indicator L s ∂μ) = ∫ s in (0 : ℝ)..r, L s := by
    rw [integral_indicator measurableSet_Iio]
    change (∫ s, L s ∂((volume.restrict (Set.Ioo 0 t)).restrict (Set.Iio r))) = _
    rw [Measure.restrict_restrict measurableSet_Iio,hLeftSet r hr,
      ← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr.1.le]
  have hRightKernel (s : ℝ) : (fun r => K (r,s)) = (Ioi s).indicator (fun r => D (r-s) s) := by
    funext r
    by_cases hsr : s < r <;> simp [K,traceTimeKernel,D,hsr]
  have hFTC (s : ℝ) (hs : s ∈ Ioo 0 t) := normalHeatAverage_integrated_heat_equation hα
    (hfc s) (hMs s) hH0 (hH s) ha (sub_pos.mpr hs.2) ξ
  have hRI (s : ℝ) (hs : s ∈ Ioo 0 t) : IntervalIntegrable (fun r => D (r-s) s) volume s t := by
    simpa only [zero_add,sub_add_cancel,D] using ((hFTC s hs).1.comp_sub_right s)
  have hKri (s : ℝ) (hs : s ∈ Ioo 0 t) : Integrable (fun r => K (r,s)) μ := by
    rw [hRightKernel,integrable_indicator_iff measurableSet_Ioi]
    change Integrable _ ((volume.restrict (Ioo 0 t)).restrict (Ioi s))
    rw [Measure.restrict_restrict measurableSet_Ioi,hRightSet s hs]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hs.2.le).mp (hRI s hs)
  have hKnB (s : ℝ) (hs : s ∈ Ioo 0 t) :
      (∫ r, ‖K (r,s)‖ ∂μ) ≤ F+C*H*t^(α/2) := by
    have hNorm : (fun r => ‖K (r,s)‖) = (Ioi s).indicator (fun r => |D (r-s) s|) := by
      funext r
      by_cases hsr : s < r <;> simp [K,traceTimeKernel,D,hsr,Real.norm_eq_abs]
    rw [hNorm,hright s hs,intervalIntegral.integral_comp_sub_right (fun r => |D r s|) s,sub_self]
    have hBound := hAge (fun y => B (y,s)) F H (hfc s) (hMs s) hH0 (hH s)
      a ha (t-s) (sub_pos.mpr hs.2) ξ
    apply hBound.trans
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (sub_pos.mpr hs.2).le (sub_le_self t hs.1.le) (by positivity)) (by positivity)
  have hFnI : Integrable (fun s => ∫ r, ‖K (r,s)‖ ∂μ) μ := by
    apply (integrable_const (F+C*H*t^(α/2))).mono'
      hKm.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_of_nonneg (integral_nonneg (fun r => norm_nonneg (K (r,s))))]
    exact hKnB s hs
  have hprod : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff' hKm.aestronglyMeasurable).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hKri s hs
  have hKL (r : ℝ) (hr : r ∈ Ioo 0 t) :
      normalTraceAgeTimeDerivative B r a ξ = ∫ s, K (r,s) ∂μ := by
    have hInd : (Iio r).indicator (fun s => K (r,s)) = fun s => K (r,s) := by
      funext s
      by_cases hsr : s < r <;> simp [K,traceTimeKernel,hsr]
    rw [normalTraceAgeTimeDerivative,← hleft r hr (fun s => K (r,s)),hInd]
  have hKR (s : ℝ) (hs : s ∈ Ioo 0 t) :
      (∫ r, K (r,s) ∂μ) = normalHeatProfile (t-s) a*heatAverage (t-s) (fun y => B (y,s)) ξ-B (ξ,s) := by
    rw [hRightKernel,hright s hs,intervalIntegral.integral_comp_sub_right (fun r => D r s) s,sub_self]
    exact (hFTC s hs).2
  have hDI : Integrable (fun r => normalTraceAgeTimeDerivative B r a ξ) μ := by
    apply hprod.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hKL r hr).symm
  have hDouble : (∫ r, normalTraceAgeTimeDerivative B r a ξ ∂μ) =
      ∫ s, normalHeatProfile (t-s) a*heatAverage (t-s) (fun y => B (y,s)) ξ-B (ξ,s) ∂μ := by
    calc
      _ = ∫ r, (∫ s, K (r,s) ∂μ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hKL r hr
      _ = ∫ s, (∫ r, K (r,s) ∂μ) ∂μ := integral_integral_swap hprod
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hKR s hs
  have hAvgII : IntervalIntegrable (fun s => normalHeatProfile (t-s) a*
      heatAverage (t-s) (fun y => B (y,s)) ξ) volume 0 t := by
    simpa only [sub_self,sub_zero,sub_sub_cancel] using
      ((normalTraceLayer_integrable_and_bound hB hF ht.le ha.le ξ).1.comp_sub_left t).symm
  have hAvgIO := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp hAvgII
  have hFII : IntervalIntegrable (fun s => B (ξ,s)) volume 0 t :=
    (hB.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  have hFIO := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp hFII
  have hReverse : (∫ s in (0 : ℝ)..t, normalHeatProfile (t-s) a*
      heatAverage (t-s) (fun y => B (y,s)) ξ) = normalTraceLayer B ξ t a := by
    simpa only [sub_self,sub_zero,sub_sub_cancel,normalTraceLayer] using
      (intervalIntegral.integral_comp_sub_left
        (fun r => normalHeatProfile r a*heatAverage r (fun y => B (y,t-r)) ξ) t (a := 0) (b := t))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr hDI,?_⟩
  have hEq : (∫ r in (0 : ℝ)..t, normalTraceAgeTimeDerivative B r a ξ) =
      normalTraceLayer B ξ t a-(∫ s in (0 : ℝ)..t, B (ξ,s)) := by
    rw [intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
    change (∫ r, normalTraceAgeTimeDerivative B r a ξ ∂μ) = _
    rw [hDouble,integral_sub hAvgIO hFIO,← hReverse,
      intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  linarith

end Yau.LeafProofs.L16Aux
