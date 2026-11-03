import Yau.LeafProofs.L05AutonomousBallMeanErrorIntegrable

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_green_cutoff_product_range (r eta s : ℝ) :
    0 ≤ autoGreenCutoffProduct r eta s ∧ autoGreenCutoffProduct r eta s ≤ 1 := by
  obtain ⟨hI0,hI1⟩ := auto_green_inner_range eta s
  obtain ⟨hO0,hO1⟩ := auto_green_outer_range r eta s
  exact ⟨mul_nonneg hI0 hO0,(mul_le_mul hI1 hO1 hO0 zero_le_one).trans_eq (mul_one 1)⟩

theorem auto_green_cutoff_product_zero {r eta s : ℝ} (hs : r ≤ s) :
    autoGreenCutoffProduct r eta s=0 := by
  simp only [autoGreenCutoffProduct,autoGreenOuter,ite_eq_right (not_lt.mpr hs),mul_zero]

theorem auto_green_cutoff_product_tendsto {s : ℝ} (hs : 0 < s) (r : ℝ) :
    Tendsto (fun eta : ℝ => autoGreenCutoffProduct r eta s) (𝓝[>] 0)
      (𝓝 (if s < r then 1 else 0)) := by
  by_cases hsr : s < r
  · rw [ite_eq_left hsr]
    have hp : 0 < min (s/2) ((r-s)/2) := lt_min (half_pos hs) (half_pos (sub_pos.mpr hsr))
    have hEvent : Ioo (0 : ℝ) (min (s/2) ((r-s)/2))∈𝓝[>] 0 :=
      mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨_,hp,subset_rfl⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hEvent] with eta heta
    have hI : autoGreenInner eta s=1 := auto_green_inner_one heta.1 (by
      rw [abs_of_pos hs]
      have h := heta.2.trans_le (min_le_left _ _)
      linarith)
    have hO : autoGreenOuter r eta s=1 := auto_green_outer_one heta.1 (by
      have h := heta.2.trans_le (min_le_right _ _)
      linarith)
    simp only [autoGreenCutoffProduct,hI,hO,mul_one]
  · simpa only [auto_green_cutoff_product_zero (le_of_not_gt hsr),ite_eq_right hsr] using
      (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))

theorem auto_ballMean_cutoff_product_tsupport {n : ℕ} (r eta : ℝ) :
    tsupport (fun x : Space n => autoGreenCutoffProduct r eta ‖x‖) ⊆ closedBall 0 r := by
  apply closure_minimal ?_ isClosed_closedBall
  intro x hx
  by_contra h
  apply hx
  apply auto_green_cutoff_product_zero
  have hh : r < ‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using h
  exact hh.le

theorem auto_ballMean_cutoff_product_integrable {n : ℕ} {r eta : ℝ} (heta : 0 < eta)
    {v : Space n → ℝ} (hv : ContinuousOn v (closedBall 0 r)) :
    Integrable (fun x : Space n => v x*autoGreenCutoffProduct r eta ‖x‖) := by
  have hSub := auto_ballMean_cutoff_product_tsupport (n := n) r eta
  exact auto_ballMean_integrable_mul_compact (hv.mono hSub)
    ((auto_green_cutoff_product_contDiff heta r).continuous.comp continuous_norm)
    ((isCompact_closedBall (0 : Space n) r).of_isClosed_subset (isClosed_tsupport _) hSub)

theorem auto_ballMean_bulk_tendsto {n : ℕ} {r : ℝ} {v : Space n → ℝ}
    (hv : ContinuousOn v (closedBall 0 r)) (hv0 : v 0=0) :
    Tendsto (fun eta : ℝ => ∫ x : Space n, v x*autoGreenCutoffProduct r eta ‖x‖) (𝓝[>] 0)
      (𝓝 (∫ x in ball (0 : Space n) r, v x)) := by
  have hInt : Integrable ((closedBall (0 : Space n) r).indicator (fun x => ‖v x‖)) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr (hv.norm.integrableOn_compact (isCompact_closedBall 0 r))
  rw [← integral_indicator measurableSet_ball]
  apply tendsto_integral_filter_of_dominated_convergence
    ((closedBall (0 : Space n) r).indicator (fun x => ‖v x‖))
  · filter_upwards [self_mem_nhdsWithin] with eta heta
    exact (auto_ballMean_cutoff_product_integrable heta hv).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun eta => ae_of_all volume fun x => by
      by_cases hx : x∈closedBall (0 : Space n) r
      · rw [indicator_of_mem hx]
        simp only [norm_mul,Real.norm_eq_abs,
          abs_of_nonneg (auto_green_cutoff_product_range r eta ‖x‖).1]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (auto_green_cutoff_product_range r eta ‖x‖).2 (abs_nonneg (v x))
      · have hxr : r ≤ ‖x‖ := (show r < ‖x‖ by simpa only [mem_closedBall,dist_zero_right,not_le] using hx).le
        simp only [indicator_of_notMem hx,auto_green_cutoff_product_zero hxr,mul_zero,norm_zero,le_refl]
  · exact hInt
  · exact ae_of_all volume fun x => by
      by_cases hx : x=0
      · subst x
        have hInd : (ball (0 : Space n) r).indicator v 0=0 := by
          by_cases hm : (0 : Space n)∈ball 0 r
          · rw [indicator_of_mem hm,hv0]
          · rw [indicator_of_notMem hm]
        simp only [hv0,zero_mul,hInd]
        exact tendsto_const_nhds
      · have h := (auto_green_cutoff_product_tendsto (norm_pos_iff.mpr hx) r).const_mul (v x)
        by_cases hxr : ‖x‖ < r
        · have hxB : x∈ball (0 : Space n) r := by simpa only [mem_ball,dist_zero_right] using hxr
          rw [indicator_of_mem hxB]
          simpa only [ite_eq_left hxr,mul_one] using h
        · have hxB : x∉ball (0 : Space n) r := by simpa only [mem_ball,dist_zero_right] using hxr
          rw [indicator_of_notMem hxB]
          simpa only [ite_eq_right hxr,mul_zero] using h

end Yau.LeafProofs.L05AutonomousAux
