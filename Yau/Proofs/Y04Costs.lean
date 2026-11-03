import Yau.Proofs.Y04FiniteCharging

/-! The full-component payment has no residual factor; prefixes pay one width. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y04Proof

theorem full_reset_cost {D W L : ℕ} {α b x y : ℝ}
    (hD : 1 ≤ D) (hW : 0 < W) (hWL : W ≤ L)
    (hb : 0 < b) (hx : 0 < x) (hy : 0 < y)
    (hpay : Real.log (D:ℝ) + max 0 (Real.log (2/b))/(W:ℝ) ≤ α)
    (hgrowth : α*(L:ℝ) ≤ Real.log (y/x)) :
    (D:ℝ)^L*x ≤ (b/2)*y := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hWr : 0 < (W : ℝ) := by exact_mod_cast hW
  have hWLr : (W : ℝ) ≤ L := by exact_mod_cast hWL
  have hLr : 0 ≤ (L : ℝ) := by positivity
  have hB : 0 ≤ max 0 (Real.log (2/b)) / (W:ℝ) := div_nonneg (le_max_left _ _) hWr.le
  have hscale : Real.log (2/b) ≤ (max 0 (Real.log (2/b)) / (W:ℝ)) * L := by
    calc
      _ ≤ max 0 (Real.log (2/b)) := le_max_right _ _
      _ = (max 0 (Real.log (2/b)) / (W:ℝ)) * W := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hWLr hB
  have hpayL := mul_le_mul_of_nonneg_right hpay hLr
  have hlog : (L:ℝ) * Real.log (D:ℝ) + Real.log (2/b) ≤ Real.log (y/x) := by
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, ← Real.log_pow, Real.exp_log (pow_pos hDr _),
    Real.exp_log (div_pos (by norm_num) hb), Real.exp_log (div_pos hy hx)] at hexp
  have hmul := (le_div_iff₀ hx).mp hexp
  have hbmul := mul_le_mul_of_nonneg_right hmul hb.le
  have hcancel : (D:ℝ)^L * (2/b) * x * b = 2 * ((D:ℝ)^L*x) := by field_simp
  rw [hcancel] at hbmul
  nlinarith

theorem prefix_cost {D W L : ℕ} {α x y : ℝ}
    (hD : 1 ≤ D) (hx : 0 < x) (hxy : x ≤ y)
    (hpay : Real.log (D:ℝ) ≤ α)
    (hgrowth : α*((L-W:ℕ):ℝ) ≤ Real.log (y/x)) :
    (D:ℝ)^L*x ≤ (D:ℝ)^W*y := by
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : 0 < (D:ℝ) := lt_of_lt_of_le zero_lt_one hDr
  by_cases hLW : L ≤ W
  · exact mul_le_mul (pow_le_pow_right₀ hDr hLW) hxy hx.le (pow_nonneg hDpos.le _)
  · have hWL : W ≤ L := by omega
    have hlog : ((L-W:ℕ):ℝ) * Real.log (D:ℝ) ≤ Real.log (y/x) := by
      have := mul_le_mul_of_nonneg_right hpay (show 0 ≤ ((L-W:ℕ):ℝ) by positivity)
      nlinarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [← Real.log_pow, Real.exp_log (pow_pos hDpos _), Real.exp_log (div_pos (hx.trans_le hxy) hx)] at hexp
    have hsmall := (le_div_iff₀ hx).mp hexp
    calc
      (D:ℝ)^L*x = (D:ℝ)^W * ((D:ℝ)^(L-W)*x) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hWL]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (pow_nonneg hDpos.le _)

end Yau.Blueprint.Alignment.Y04Proof
