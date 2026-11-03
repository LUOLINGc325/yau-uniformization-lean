import spec.CHAIN.CONTRACTS

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof

theorem exists_uniform_small_time_exponential (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ d ∈ Icc (0 : ℝ) δ,
      Real.exp (C * d) ≤ (3 / 2 : ℝ) ^ 2 := by
  have hlog : 0 < Real.log (9 / 4 : ℝ) := Real.log_pos (by norm_num)
  let δ := min 1 (Real.log (9 / 4 : ℝ) / (C + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hlog (by linarith))
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro d hd
  have hD : (C + 1) * δ ≤ Real.log (9 / 4 : ℝ) := by
    have hh := (le_div_iff₀ (by linarith : 0 < C + 1)).mp
      (min_le_right (1 : ℝ) (Real.log (9 / 4 : ℝ) / (C + 1)))
    simpa only [mul_comm] using hh
  have hCd : C * d ≤ Real.log (9 / 4 : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hd.2 hC
    nlinarith
  calc
    Real.exp (C * d) ≤ Real.exp (Real.log (9 / 4 : ℝ)) := Real.exp_le_exp.mpr hCd
    _ = (3 / 2 : ℝ) ^ 2 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 9 / 4)]; norm_num

end Yau.Blueprint.C02Proof
