import Yau.Proofs.F01ScalarLeviLinearity
import Yau.Proofs.F01ScalarLeviDiagonal

/-! Actual differentiation of the fixed-direction Rayleigh denominator:
log(q/(exp(f)r)) has the three original scalar Hessians with their exact signs. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem leviC_log_exp_quotient (q f r : ComplexVector n → ℝ)
    {S : Set (ComplexVector n)} (hS : IsOpen S)
    (hpos : ∀ w ∈ S, 0 < q w ∧ 0 < r w)
    {z : ComplexVector n} (hz : z ∈ S)
    (hq : ContDiffAt ℝ 2 q z) (hf : ContDiffAt ℝ 2 f z) (hr : ContDiffAt ℝ 2 r z) :
    leviC (fun w => Real.log (q w / (Real.exp (f w) * r w))) z =
      leviC (fun w => Real.log (q w)) z - leviC f z -
        leviC (fun w => Real.log (r w)) z := by
  have hLq : ContDiffAt ℝ 2 (fun w => Real.log (q w)) z := hq.log (hpos z hz).1.ne'
  have hLr : ContDiffAt ℝ 2 (fun w => Real.log (r w)) z := hr.log (hpos z hz).2.ne'
  have heq : (fun w => Real.log (q w / (Real.exp (f w) * r w))) =ᶠ[𝓝 z]
      (fun w => Real.log (q w) - f w - Real.log (r w)) := by
    filter_upwards [hS.mem_nhds hz] with w hw
    rw [Real.log_div (hpos w hw).1.ne'
      (mul_pos (Real.exp_pos _) (hpos w hw).2).ne',
      Real.log_mul (Real.exp_pos _).ne' (hpos w hw).2.ne', Real.log_exp]
    ring
  rw [Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq heq,
    leviC_sub (hLq.sub hf) hLr, leviC_sub hLq hf]

theorem log_quotient_curve_hasDerivAt {qcurve : ℝ → ℝ} {t qdot c : ℝ}
    (hq : HasDerivAt qcurve qdot t) (hpos : 0 < qcurve t) (hc : 0 < c) :
    HasDerivAt (fun s => Real.log (qcurve s / c)) (qdot / qcurve t) t := by
  convert (hq.div_const c).log (div_ne_zero hpos.ne' hc.ne') using 1
  field_simp

theorem leviC_log_normal_diagonal {r : ComplexVector n → ℝ} {z : ComplexVector n}
    (hr : ContDiffAt ℝ 2 r z) (hvalue : r z = 1)
    (hzero : fderiv ℝ r z = 0) (i : Fin n) :
    (leviC (fun w => Real.log (r w)) z i i).re = (leviC r z i i).re := by
  have hpos : 0 < r z := by rw [hvalue]; norm_num
  have hw : wirt (fun w => (r w : ℂ)) z (stdVec i) = 0 := by
    have hd : fderiv ℝ (fun w => (r w : ℂ)) z =
        Complex.ofRealCLM.comp (fderiv ℝ r z) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ r) z = _
      rw [fderiv_comp z Complex.ofRealCLM.differentiableAt
        (hr.differentiableAt (by norm_num)), ContinuousLinearMap.fderiv]
    simp only [wirt, hd, hzero, ContinuousLinearMap.comp_zero, zero_apply,
      mul_zero, sub_self]
  rw [leviC_log_diagonal hr hpos, hvalue, hw]
  simp

end Yau.NodeProofs.F01Aux
