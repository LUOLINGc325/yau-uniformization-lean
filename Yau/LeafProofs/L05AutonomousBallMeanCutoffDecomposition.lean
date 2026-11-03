import Yau.LeafProofs.L05AutonomousBallMeanCutoffJets

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

theorem auto_green_inner_eventuallyEq_one {eta s : ℝ} (heta : 0 < eta) (hs : 2*eta < s) :
    autoGreenInner eta=ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
  filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
  exact auto_green_inner_one heta (ht.le.trans (le_abs_self t))

theorem auto_green_outer_eventuallyEq_one {eta r s : ℝ} (heta : 0 < eta) (hs : s < r-2*eta) :
    autoGreenOuter r eta=ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
  filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
  exact auto_green_outer_one heta ht.le

theorem auto_green_product_eventuallyEq_inner {eta r s : ℝ} (heta : 0 < eta) (hs : s < r-2*eta) :
    autoGreenCutoffProduct r eta=ᶠ[𝓝 s] autoGreenInner eta := by
  filter_upwards [auto_green_outer_eventuallyEq_one heta hs] with t ht
  simp only [autoGreenCutoffProduct,ht,mul_one]

theorem auto_green_product_eventuallyEq_outer {eta r s : ℝ} (heta : 0 < eta) (hs : 2*eta < s) :
    autoGreenCutoffProduct r eta=ᶠ[𝓝 s] autoGreenOuter r eta := by
  filter_upwards [auto_green_inner_eventuallyEq_one heta hs] with t ht
  simp only [autoGreenCutoffProduct,ht,one_mul]

theorem auto_green_product_deriv_zero_outside {eta r s : ℝ} (heta : 0 < eta) (hs : 0 < s)
    (hIn : s∉Icc eta (2*eta)) (hOut : s∉Icc (r-2*eta) (r-eta)) :
    deriv (autoGreenCutoffProduct r eta) s=0 ∧ deriv (deriv (autoGreenCutoffProduct r eta)) s=0 := by
  have hConst : ∃ c : ℝ, autoGreenCutoffProduct r eta=ᶠ[𝓝 s] (fun _ => c) := by
    by_cases hse : s < eta
    · refine ⟨0,?_⟩
      filter_upwards [isOpen_Ioo.mem_nhds (show s∈Ioo 0 eta from ⟨hs,hse⟩)] with t ht
      have hI := auto_green_inner_zero heta (show |t| ≤ eta by rw [abs_of_pos ht.1]; exact ht.2.le)
      simp only [autoGreenCutoffProduct,hI,zero_mul]
    · have hLarge : 2*eta < s := by
        by_contra h
        exact hIn ⟨le_of_not_gt hse,le_of_not_gt h⟩
      by_cases hsr : s < r-2*eta
      · refine ⟨1,?_⟩
        filter_upwards [auto_green_inner_eventuallyEq_one heta hLarge,
          auto_green_outer_eventuallyEq_one heta hsr] with t htI htO
        simp only [autoGreenCutoffProduct,htI,htO,mul_one]
      · have hRight : r-eta < s := by
          by_contra h
          exact hOut ⟨le_of_not_gt hsr,le_of_not_gt h⟩
        refine ⟨0,?_⟩
        filter_upwards [isOpen_Ioi.mem_nhds hRight] with t ht
        simp only [autoGreenCutoffProduct,auto_green_outer_zero heta ht.le,mul_zero]
  obtain ⟨c,hc⟩ := hConst
  constructor
  · simpa only [deriv_const] using hc.deriv_eq
  · simpa only [deriv_const',deriv_const] using hc.deriv.deriv_eq

theorem auto_green_error_decomposition (d : ℕ) (omega : ℝ) {r eta s : ℝ}
    (heta : 0 < eta) (hetar : eta < r/8) (hs : 0 < s) :
    autoGreenCutoffError d omega r s (deriv (autoGreenCutoffProduct r eta) s)
      (deriv (deriv (autoGreenCutoffProduct r eta)) s)=
      (if s∈Icc eta (2*eta) then autoGreenCutoffError d omega r s (deriv (autoGreenInner eta) s)
        (deriv (deriv (autoGreenInner eta)) s) else 0)+
      (if s∈Icc (r-2*eta) (r-eta) then autoGreenCutoffError d omega r s (deriv (autoGreenOuter r eta) s)
        (deriv (deriv (autoGreenOuter r eta)) s) else 0) := by
  by_cases hIn : s∈Icc eta (2*eta)
  · have hOut : s∉Icc (r-2*eta) (r-eta) := by
      intro h
      linarith [hIn.2,h.1]
    have hEq := auto_green_product_eventuallyEq_inner heta (show s < r-2*eta by linarith [hIn.2])
    rw [ite_eq_left hIn,ite_eq_right hOut,hEq.deriv_eq,hEq.deriv.deriv_eq,add_zero]
  · by_cases hOut : s∈Icc (r-2*eta) (r-eta)
    · have hEq := auto_green_product_eventuallyEq_outer (r := r) heta (show 2*eta < s by linarith [hOut.1])
      rw [ite_eq_right hIn,ite_eq_left hOut,hEq.deriv_eq,hEq.deriv.deriv_eq,zero_add]
    · obtain ⟨hD,hDD⟩ := auto_green_product_deriv_zero_outside heta hs hIn hOut
      simp only [hD,hDD,ite_eq_right hIn,ite_eq_right hOut,autoGreenCutoffError,mul_zero,add_zero]

end Yau.LeafProofs.L05AutonomousAux
