import Yau.Proofs.P08CompactHeatSubmean

/-! The genuine finite-ball comparison error decays inversely in its radius. -/
noncomputable section
open scoped Topology
namespace Yau.NodeProofs.P08Aux

theorem heat_submean_barrier_error_le (n : ℕ) {B A R T : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hR : 1 ≤ R) (hT : 0 < T) :
    ((B + A * R + 1) / (1 - Real.exp (-1))) *
        (1 - Real.exp (-(((2 * n : ℕ) : ℝ) * (1 / R ^ 2) / (1 - 1 / 2) * T))) ≤
      ((B + A + 1) / (1 - Real.exp (-1)) * (4 * n) * T) / R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hd : 0 < 1 - Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  let x : ℝ := ((2 * n : ℕ) : ℝ) * (1 / R ^ 2) / (1 - 1 / 2) * T
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hexp : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  have hlin : (B + A * R + 1) / (1 - Real.exp (-1)) ≤
      ((B + A + 1) / (1 - Real.exp (-1))) * R := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right ?_ hd.le
    nlinarith
  calc
    _ ≤ ((B + A * R + 1) / (1 - Real.exp (-1))) * x :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (((B + A + 1) / (1 - Real.exp (-1))) * R) * x :=
      mul_le_mul_of_nonneg_right hlin hx
    _ = _ := by
      dsimp only [x]
      push_cast
      field_simp
      ring

end Yau.NodeProofs.P08Aux
