import Yau.Proofs.F01RayleighPenalty
import Yau.Proofs.F01GradientYoung

/-! The penalty contact inequality supplies the exact uniform coefficient
needed to absorb the gradient cross term; no bound on Q is assumed here. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem rayleighPenalty_contact_coefficient {a v W : ℝ}
    (ha : 0 < a) (hv : 0 ≤ v) (hW : Real.exp (rayleighPenalty a v) ≤ W) :
    (W⁻¹ * deriv (rayleighPenalty a) v) ^ 2 /
        (-deriv (deriv (rayleighPenalty a)) v) ≤ 4 := by
  let D := 1 + a * v
  have hD : 0 < D := by dsimp [D]; positivity
  have hcontact : D ≤ W := rayleighPenalty_contact_lower ha.le hv hW
  have hWp : 0 < W := lt_of_lt_of_le hD hcontact
  rw [rayleighPenalty_deriv a v hD.ne', rayleighPenalty_second_deriv a v hD.ne']
  change (W⁻¹ * (a + a / D)) ^ 2 / (-(-(a ^ 2) / D ^ 2)) ≤ 4
  simp only [neg_div, neg_neg]
  have hid : (W⁻¹ * (a + a / D)) ^ 2 / (a ^ 2 / D ^ 2) = ((D + 1) / W) ^ 2 := by
    field_simp
  rw [hid]
  have hratio : (D + 1) / W ≤ 2 := by
    apply (div_le_iff₀ hWp).mpr
    have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
    linarith
  have hratio0 : 0 ≤ (D + 1) / W := by positivity
  nlinarith

theorem rayleighPenalty_absorbs_gradient {a v W A B : ℝ}
    (ha : 0 < a) (hv : 0 ≤ v) (hW : Real.exp (rayleighPenalty a v) ≤ W)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    2 * (W⁻¹ * deriv (rayleighPenalty a) v) * Real.sqrt A * Real.sqrt B +
        deriv (deriv (rayleighPenalty a)) v * B ≤
      8 * A + deriv (deriv (rayleighPenalty a)) v / 2 * B := by
  have hden : 0 < 1 + a * v := by positivity
  have hd : 0 < -deriv (deriv (rayleighPenalty a)) v := by
    rw [rayleighPenalty_second_deriv a v hden.ne']
    simp only [neg_div, neg_neg]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hden)
  have hh := gradient_young_half hA hB hd
    (c := W⁻¹ * deriv (rayleighPenalty a) v)
  have hc := rayleighPenalty_contact_coefficient ha hv hW
  have hmul := mul_le_mul_of_nonneg_right hc hA
  have hcoef : 2 * (W⁻¹ * deriv (rayleighPenalty a) v) ^ 2 /
      (-deriv (deriv (rayleighPenalty a)) v) * A ≤ 8 * A := by
    calc
      _ = 2 * (((W⁻¹ * deriv (rayleighPenalty a) v) ^ 2 /
          (-deriv (deriv (rayleighPenalty a)) v)) * A) := by ring
      _ ≤ 2 * (4 * A) := mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = _ := by ring
  linarith

end Yau.NodeProofs.F01Aux
