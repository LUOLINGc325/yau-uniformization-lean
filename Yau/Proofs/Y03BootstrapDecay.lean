import Yau.Proofs.Y03Grid

/-! One uniform late threshold makes the exponential backward bound smaller than every required polynomial error. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem bootstrap_decay_real_eventually {a c C : ℝ} (ha : 0 < a) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      (1 + x) ^ C * Real.exp (-c * (Real.exp (a * x) / x ^ 2)) ≤ Real.exp (-x) := by
  have hlim : Tendsto (fun x : ℝ => Real.exp (a * x) / x ^ 3) atTop atTop := by
    simpa only [Real.rpow_natCast] using tendsto_exp_mul_div_rpow_atTop (3 : ℕ) a ha
  filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_atTop.1 hlim) ((C + 1) / c)] with x hx hpay
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hclock : (C + 1) * x ≤ c * (Real.exp (a * x) / x ^ 2) := by
    have hp := (div_le_div_iff₀ hc (pow_pos hxpos 3)).1 hpay
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hxpos)).2
    nlinarith
  have hlog : Real.log (1 + x) ≤ x := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
    linarith
  rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + x), ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hmul := mul_le_mul_of_nonneg_right hlog hC
  nlinarith

theorem bootstrap_decay_nat_eventually {hm c C : ℝ} (hhm : 0 < hm) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop,
      (1 + (j : ℝ)) ^ C * Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2) ≤
        Real.exp (-(j : ℝ)) := by
  have h : ∀ᶠ j : ℕ in atTop,
      (1 + (j : ℝ)) ^ C * Real.exp (-c * (Real.exp (hm / 2 * j) / (j : ℝ) ^ 2)) ≤ Real.exp (-(j : ℝ)) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).eventually
      (bootstrap_decay_real_eventually (a := hm / 2) (by linarith) hc hC)
  filter_upwards [h] with j hj
  have heq : hm / 2 * (j : ℝ) = hm * (j : ℝ) / 2 := by ring
  rw [heq] at hj
  have hlhs : -c * Real.exp (hm * (j : ℝ) / 2) / (j : ℝ) ^ 2 =
      -c * (Real.exp (hm * (j : ℝ) / 2) / (j : ℝ) ^ 2) := by ring
  rw [← hlhs] at hj
  simpa only [macroClock, ← Real.exp_half] using hj

end Yau.Blueprint.Alignment.Y03Proof
