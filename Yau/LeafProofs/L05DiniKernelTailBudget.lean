import Yau.LeafProofs.L05DiniKernelTail
import Yau.LeafProofs.L05DiniKernelBudgetScale

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem diniModulusTail_near_eq (G : ℝ) (phi : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∫ s in (0:ℝ)..r, diniModulusTail G phi s/s)=(∫ s in (0:ℝ)..r, phi s/s) := by
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc 0 r := by simpa only [Set.uIcc_of_le hr] using hs
  rcases hs'.1.eq_or_lt with hzero | hpos
  · rw [← hzero]
    simp only [div_zero]
  · simp only [diniModulusTail,ite_eq_right hpos.not_ge,ite_eq_left (hs'.2.trans hr1)]

theorem diniModulusTail_middle_eq (G : ℝ) (phi : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (∫ s in r..(1:ℝ), diniModulusTail G phi s/s^2)=(∫ s in r..(1:ℝ), phi s/s^2) := by
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc r 1 := by simpa only [Set.uIcc_of_le hr1] using hs
  have hs0 : 0 < s := hr.trans_le hs'.1
  simp only [diniModulusTail,ite_eq_right hs0.not_ge,ite_eq_left hs'.2]

theorem diniModulusTail_far_eq (G : ℝ) (phi : ℝ → ℝ) :
    (∫ s in Set.Ioi (1:ℝ), diniModulusTail G phi s/s^2)=phi 1+2*G := by
  calc
    _=(phi 1+2*G)*(∫ s in Set.Ioi (1:ℝ), s^(-(2:ℝ))) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change diniModulusTail G phi s/s^2=(phi 1+2*G)*s^(-(2:ℝ))
      have hs0 : 0 < s := zero_lt_one.trans hs
      rw [diniModulusTail,ite_eq_right hs0.not_ge,ite_eq_right (not_le.mpr hs),
        Real.rpow_neg hs0.le,Real.rpow_two,div_eq_mul_inv]
    _=_ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : -(2:ℝ) < -1) (by norm_num : (0:ℝ) < 1)]
      norm_num

theorem diniModulusTail_budget_eq {phi : ℝ → ℝ} {eta B G r : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hm : Measurable phi) (hmono : MonotoneOn phi (Set.Ioc (0:ℝ) 1))
    (hp : powerBound eta B phi) (hr : r ∈ Set.Ioc (0:ℝ) 1) :
    diniBudget (diniModulusTail G phi) r=(∫ s in (0:ℝ)..r, phi s/s)+
      r*(∫ s in r..(1:ℝ), phi s/s^2)+r*phi 1+2*r*G := by
  have hd := diniModulusTail_data he he1 hB hG hm hmono hp
  have hBG : 0 ≤ B+2*G := by positivity
  have hR := diniBudget_integrable he he1 hBG hd.1 hd.2.2.2 hr.1
  have hOne := diniBudget_integrable he he1 hBG hd.1 hd.2.2.2 (by norm_num : (0:ℝ) < 1)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hR.2 hOne.2
  rw [diniModulusTail_middle_eq G phi hr.1 hr.2,diniModulusTail_far_eq] at hsplit
  have hscaled := congrArg (fun v : ℝ => r*v) hsplit
  unfold diniBudget
  rw [diniModulusTail_near_eq G phi hr.1.le hr.2]
  nlinarith only [hscaled]

theorem diniModulusTail_budget_le {phi : ℝ → ℝ} {eta B G r : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hm : Measurable phi) (hmono : MonotoneOn phi (Set.Ioc (0:ℝ) 1))
    (hp : powerBound eta B phi) (hr : r ∈ Set.Ioc (0:ℝ) 1) :
    diniBudget (diniModulusTail G phi) r ≤ diniTransform phi r+2*r*G := by
  have hEq := diniModulusTail_budget_eq he he1 hB hG hm hmono hp hr
  have hDI := diniIntegrable_of_powerBound he he1 hB hm hp hr.1 hr.2
  have hu : 0 ≤ min (2*r) 1 := le_min (by linarith only [hr.1]) zero_le_one
  have hrmin : r ≤ min (2*r) 1 := le_min (by linarith only [hr.1]) hr.2
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 (min (2*r) 1))] (fun s : ℝ => phi s/s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact div_nonneg (hp s ⟨hs.1,hs.2.trans (min_le_right _ _)⟩).1 hs.1.le
  have hNear := intervalIntegral.integral_mono_interval (a := 0) (b := r) (c := 0) (d := min (2*r) 1)
    le_rfl hr.1.le hrmin hnonneg hDI.1
  unfold diniTransform
  linarith only [hEq,hNear,(hp r hr).1]

end Yau.LeafProofs.L05Aux
