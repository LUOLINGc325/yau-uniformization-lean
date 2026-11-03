import Yau.LeafProofs.L05DiniKernelDefinitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem diniBudget_integrable {psi : ℝ → ℝ} {eta B r : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (_hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hr : 0 < r) :
    IntervalIntegrable (fun s : ℝ => psi s/s) volume 0 r ∧
      IntegrableOn (fun s : ℝ => psi s/s^2) (Set.Ioi r) := by
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
    have hg := ((intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := r) (by linarith : -1 < eta-1)).const_mul B).1
    refine hg.mono' (hm.div measurable_id).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hp := hpsi s hs.1
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hp.1 hs.1.le)]
    calc
      _ ≤ (B*s^eta)/s := div_le_div_of_nonneg_right hp.2 hs.1.le
      _ = B*s^(eta-1) := by rw [mul_div_assoc,power_div_self_eq hs.1.le he1.ne]
  · have hg := (integrableOn_Ioi_rpow_of_lt (by linarith : eta-2 < -1) hr).const_mul B
    refine hg.mono' (hm.div (measurable_id.pow_const 2)).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hr.trans hs
    have hp := hpsi s hs0
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hp.1 (sq_nonneg _))]
    calc
      _ ≤ (B*s^eta)/s^2 := div_le_div_of_nonneg_right hp.2 (sq_nonneg _)
      _ = B*s^(eta-2) := by rw [mul_div_assoc,power_div_sq_eq hs0.le (by linarith : eta ≠ 2)]

theorem diniBudget_nonneg {psi : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s) : 0 ≤ diniBudget psi r := by
  have hnear : 0 ≤ ∫ s in (0:ℝ)..r, psi s/s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hr.le
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rcases hs.1.eq_or_lt with hzero | hpos
    · rw [← hzero]
      simp only [div_zero,Pi.zero_apply,le_refl]
    · exact div_nonneg (hpsi s hpos) hpos.le
  have hfar : 0 ≤ ∫ s in Set.Ioi r, psi s/s^2 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact div_nonneg (hpsi s (hr.trans hs)) (sq_nonneg _)
  exact add_nonneg hnear (mul_nonneg hr.le hfar)

end Yau.LeafProofs.L05Aux
