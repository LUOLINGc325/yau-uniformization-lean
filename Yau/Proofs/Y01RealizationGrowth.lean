import Yau.Proofs.Y01SqrtEnvelopes

/-! The raw Y02 realization exponent contributes one fixed coefficient of
delta-s; every endpoint cost remains in an explicit sqrt-s error envelope. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

theorem raw_realization_growth
    {s Δ A B C x y : ℝ} (hs : 1 ≤ s) (hΔ : 0 ≤ Δ) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ Real.exp (A * Real.sqrt s))
    (hy : y ≤ Real.exp (Δ / 2 + B * Real.sqrt s)) :
    C * (1 + x + y) ^ C ≤
      Real.exp ((1 + |C|) * Δ +
        (|C| * (max 0 (max A B) + 1 + Real.log 3)) * Real.sqrt s) := by
  let a := max 0 (max A B)
  let T := Δ / 2 + a * Real.sqrt s
  let S := 1 + x + y
  have ha0 : 0 ≤ a := le_max_left _ _
  have hAa : A ≤ a := (le_max_left _ _).trans (le_max_right _ _)
  have hBa : B ≤ a := (le_max_right _ _).trans (le_max_right _ _)
  have hroot : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  have hxT : x ≤ Real.exp T := hx.trans (Real.exp_le_exp.2 (by
    dsimp [T]
    have := mul_le_mul_of_nonneg_right hAa hroot
    linarith))
  have hyT : y ≤ Real.exp T := hy.trans (Real.exp_le_exp.2 (by
    dsimp [T]
    linarith [mul_le_mul_of_nonneg_right hBa hroot]))
  have hST : S ≤ 3 * Real.exp T := by
    have hOne := Real.one_le_exp hT
    dsimp [S]
    linarith
  have hlogS : Real.log S ≤ Real.log 3 + T := by
    have hlog := Real.log_le_log hSpos hST
    rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt (Real.exp_pos T)), Real.log_exp] at hlog
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hpow : S ^ C ≤ S ^ |C| := Real.rpow_le_rpow_of_exponent_le hS (le_abs_self C)
  have hpowBound : S ^ |C| ≤ Real.exp ((Real.log 3 + T) * |C|) := by
    rw [Real.rpow_def_of_pos hSpos]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hlogS hC0)
  have hAbs : |C| ≤ Real.exp |C| := by linarith [Real.add_one_le_exp |C|]
  have hlead : |C| / 2 * Δ ≤ (1 + |C|) * Δ := by nlinarith [mul_nonneg hC0 hΔ]
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hConst : |C| * (1 + Real.log 3) ≤ |C| * (1 + Real.log 3) * Real.sqrt s :=
    le_mul_of_one_le_right (by positivity) (sqrt_one_le hs)
  change C * S ^ C ≤ _
  calc
    C * S ^ C ≤ |C| * S ^ C := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hSpos.le _)
    _ ≤ |C| * S ^ |C| := mul_le_mul_of_nonneg_left hpow hC0
    _ ≤ Real.exp |C| * Real.exp ((Real.log 3 + T) * |C|) :=
      mul_le_mul hAbs hpowBound (Real.rpow_nonneg hSpos.le _) (Real.exp_pos _).le
    _ = Real.exp (|C| + (Real.log 3 + T) * |C|) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.2 (by dsimp [T, a]; nlinarith)

end Yau.Proofs.Y01Aux
