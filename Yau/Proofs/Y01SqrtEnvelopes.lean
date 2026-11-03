import Yau.Blueprint.Stages

/-! Fixed polynomial factors are absorbed in exp(C sqrt(s)); their error
rate is the explicit C/sqrt(s), tending to zero along the same clock. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Filter

 theorem log_one_add_le_four_sqrt {s : ℝ} (hs : 1 ≤ s) :
    Real.log (1 + s) ≤ 4 * Real.sqrt s := by
  have hs0 : 0 ≤ s := by linarith
  have hx : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.2 (by linarith)
  have hlog := Real.log_le_sub_one_of_pos hx
  rw [Real.log_sqrt (by linarith : 0 ≤ 1 + s)] at hlog
  have hsqrt : Real.sqrt (1 + s) ≤ 2 * Real.sqrt s := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hs0]
  linarith

theorem polynomial_le_sqrt_envelope {s p : ℝ} (hs : 1 ≤ s) :
    (1 + s) ^ p ≤ Real.exp ((4 * |p|) * Real.sqrt s) := by
  have hbase : 0 < 1 + s := by linarith
  have hlog0 : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith)
  rw [Real.rpow_def_of_pos hbase]
  apply Real.exp_le_exp.2
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self p) hlog0
  have h2 := mul_le_mul_of_nonneg_right (log_one_add_le_four_sqrt hs) (abs_nonneg p)
  nlinarith

theorem sqrt_one_le {s : ℝ} (hs : 1 ≤ s) : 1 ≤ Real.sqrt s := by
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hs

theorem exp_sqrt_add_bound {s A B x y : ℝ} (hs : 1 ≤ s)
    (hx : x ≤ Real.exp (A * Real.sqrt s)) (hy : y ≤ Real.exp (B * Real.sqrt s)) :
    x + y ≤ Real.exp ((max A B + Real.log 2) * Real.sqrt s) := by
  have hroot : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hX : x ≤ Real.exp (max A B * Real.sqrt s) :=
    hx.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hroot))
  have hY : y ≤ Real.exp (max A B * Real.sqrt s) :=
    hy.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hroot))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    x + y ≤ 2 * Real.exp (max A B * Real.sqrt s) := by linarith
    _ = Real.exp (max A B * Real.sqrt s + Real.log 2) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith [sqrt_one_le hs])

theorem sqrt_error_tendsto {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) (C : ℝ) :
    Tendsto (fun k => C / Real.sqrt (s k)) atTop (nhds 0) :=
  (Real.tendsto_sqrt_atTop.comp hs).const_div_atTop C

theorem sqrt_error_identity {s C : ℝ} (hs : 0 < s) :
    (C / Real.sqrt s) * s = C * Real.sqrt s := by
  have hroot : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  rw [div_mul_eq_mul_div, div_eq_iff hroot]
  rw [mul_assoc, Real.mul_self_sqrt hs.le]

end Yau.Proofs.Y01Aux
