import Yau.LeafProofs.L05DiniKernelBudget

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem diniBudget_dilate_le {psi : ℝ → ℝ} {eta B r D : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta)
    (hr : 0 < r) (hD : 1 ≤ D) : diniBudget psi (D*r) ≤ D*diniBudget psi r := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hDr : 0 < D*r := mul_pos hD0 hr
  have hrD : r ≤ D*r := by nlinarith only [hr,hD]
  have hR := diniBudget_integrable he he1 hB hm hpsi hr
  have hBig := diniBudget_integrable he he1 hB hm hpsi hDr
  have hMid : IntervalIntegrable (fun s : ℝ => psi s/s) volume r (D*r) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrD]
    exact hBig.1.1.mono_set (fun s hs => ⟨hr.trans hs.1,hs.2⟩)
  have hMidTail : IntervalIntegrable (fun s : ℝ => psi s/s^2) volume r (D*r) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrD]
    exact hR.2.mono_set Set.Ioc_subset_Ioi_self
  have hMiddle : (∫ s in r..D*r, psi s/s) ≤ (D*r)*(∫ s in r..D*r, psi s/s^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hrD hMid (hMidTail.const_mul (D*r))
    intro s hs
    have hs0 : 0 < s := hr.trans_le hs.1
    have heq : psi s/s=s*(psi s/s^2) := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hs.2 (div_nonneg (hpsi s hs0).1 (sq_nonneg _))
  have hTail := intervalIntegral.integral_interval_add_Ioi hR.2 hBig.2
  have hNear := intervalIntegral.integral_add_adjacent_intervals hR.1 hMid
  have hNear0 : 0 ≤ ∫ s in (0:ℝ)..r, psi s/s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hr.le
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rcases hs.1.eq_or_lt with hzero | hpos
    · rw [← hzero]
      simp only [div_zero,Pi.zero_apply,le_refl]
    · exact div_nonneg (hpsi s hpos).1 hpos.le
  have hScale := mul_le_mul_of_nonneg_right hD hNear0
  have hTailScaled := congrArg (fun v : ℝ => (D*r)*v) hTail
  unfold diniBudget
  rw [← hNear]
  nlinarith only [hMiddle,hTailScaled,hScale]

end Yau.LeafProofs.L05Aux
