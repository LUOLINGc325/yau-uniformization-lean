import Yau.Proofs.P07HeatLinear

/-! Elementary Gaussian majorants for unit-range Lipschitz data. -/
noncomputable section
namespace Yau.NodeProofs.P07Aux

 theorem exp_neg_le_one_sub_half {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (-s) ≤ 1 - s / 2 := by
  have he : Real.exp (-s) * (1 + s) ≤ 1 := by
    calc
      Real.exp (-s) * (1 + s) ≤ Real.exp (-s) * Real.exp s :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp s]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hp : 1 ≤ (1 - s / 2) * (1 + s) := by nlinarith
  exact (mul_le_mul_iff_left₀ (by linarith : 0 < 1 + s)).mp (he.trans hp)

theorem unit_lipschitz_gaussian_majorant
    {K δ a d q q0 : ℝ} (hK : 0 < K) (hδ : 0 < δ) (ha : 0 < a)
    (hrel : 4 * a * δ = K) (hd : 0 ≤ d)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hq0 : q0 ∈ Set.Icc (0 : ℝ) 1)
    (hLip : |q - q0| ≤ K * d) :
    |q - q0| ≤ K * δ + 2 * (1 - Real.exp (-a * d ^ 2)) := by
  have hunit : |q - q0| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1, hq0.2], by linarith [hq.2, hq0.1]⟩
  have hquad : K * d ≤ K * δ + a * d ^ 2 := by
    rw [← hrel]
    nlinarith [mul_nonneg ha.le (sq_nonneg (d - 2 * δ))]
  by_cases hs : a * d ^ 2 ≤ 1
  · have he := exp_neg_le_one_sub_half (mul_nonneg ha.le (sq_nonneg d)) hs
    have heq : - (a * d ^ 2) = -a * d ^ 2 := by ring
    rw [heq] at he
    linarith
  · have hh := exp_neg_le_one_sub_half (s := 1) (by norm_num) (by norm_num)
    have he : Real.exp (-a * d ^ 2) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [mul_pos hK hδ]

end Yau.NodeProofs.P07Aux
