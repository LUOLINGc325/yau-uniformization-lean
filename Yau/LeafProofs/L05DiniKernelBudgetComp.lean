import Yau.LeafProofs.L05DiniKernelBudget

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem diniBudget_comp_mul (psi : ℝ → ℝ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    diniBudget (fun s => psi (c*s)) r=diniBudget psi (c*r) := by
  let f := fun s : ℝ => c*s
  have hcR : 0 < c*r := mul_pos hc hr
  have hf (s : ℝ) : HasDerivAt f c s := by
    convert! (hasDerivAt_id s).const_mul c using 1 <;> simp only [mul_one,id_eq]
  have hInj : Function.Injective f := fun x y hxy => mul_left_cancel₀ hc.ne' hxy
  have himg0 : f '' Set.Ioc (0:ℝ) r=Set.Ioc (0:ℝ) (c*r) := by
    simpa only [mul_zero] using Set.image_mul_left_Ioc hc 0 r
  have himg1 : f '' Set.Ioi r=Set.Ioi (c*r) := Set.image_mul_left_Ioi hc r
  have hNear : (∫ s in (0:ℝ)..c*r, psi s/s)=(∫ s in (0:ℝ)..r, psi (c*s)/s) := by
    have hj := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioc (0:ℝ) r) measurableSet_Ioc
      (fun s hs => (hf s).hasDerivWithinAt) hInj.injOn (fun u : ℝ => psi u/u)
    rw [himg0] at hj
    rw [intervalIntegral.integral_of_le hcR.le,intervalIntegral.integral_of_le hr.le]
    exact hj.trans (setIntegral_congr_fun measurableSet_Ioc (fun s hs => by
      change |c| • (psi (c*s)/(c*s))=psi (c*s)/s
      rw [abs_of_pos hc,smul_eq_mul]
      field_simp [hc.ne',hs.1.ne']))
  have hFar : c*(∫ s in Set.Ioi (c*r), psi s/s^2)=(∫ s in Set.Ioi r, psi (c*s)/s^2) := by
    have hj := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioi r) measurableSet_Ioi
      (fun s hs => (hf s).hasDerivWithinAt) hInj.injOn (fun u : ℝ => c*(psi u/u^2))
    rw [himg1,integral_const_mul] at hj
    exact hj.trans (setIntegral_congr_fun measurableSet_Ioi (fun s hs => by
      change |c| • (c*(psi (c*s)/(c*s)^2))=psi (c*s)/s^2
      rw [abs_of_pos hc,smul_eq_mul]
      have hs0 : 0 < s := hr.trans hs
      field_simp [hc.ne',hs0.ne']))
  unfold diniBudget
  rw [← hNear,← hFar]
  ring

end Yau.LeafProofs.L05Aux
