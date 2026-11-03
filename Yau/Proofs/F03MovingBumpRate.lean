import Yau.Proofs.F03MovingBumpBound

/-! The cubic inequality holds on the entire support interface as well. -/
noncomputable section
namespace Yau.Proofs.F03Aux

def movingCubicRate (R lam P : ℝ) : ℝ :=
  max (4*P/R^2) (3*P^2/(8*lam*R^2))

theorem moving_cubic_polynomial_bound (R lam P d : ℝ)
    (hR : 0 < R) (hlam : 0 < lam) (hP : 0 ≤ P) :
    3*P*positivePower 2 (R^2-d^2)-24*lam*d^2*positivePower 1 (R^2-d^2) ≤
      movingCubicRate R lam P*positivePower 3 (R^2-d^2) := by
  let q := R^2-d^2
  by_cases hq : 0 < q
  · have hqne : q ≠ 0 := hq.ne'
    have hrate : 3*P/q-24*lam*d^2/q^2 ≤ movingCubicRate R lam P :=
      moving_cubic_quotient_bound R lam P d hR hlam hP (sub_pos.mp hq)
    have hm := mul_le_mul_of_nonneg_right hrate (pow_nonneg hq.le 3)
    have heq : (3*P/q-24*lam*d^2/q^2)*q^3 = 3*P*q^2-24*lam*d^2*q := by
      field_simp
    rw [heq] at hm
    simpa only [positivePower,max_eq_right hq.le,pow_one,q] using hm
  · have hq' : R^2-d^2 ≤ 0 := le_of_not_gt hq
    simp only [positivePower,max_eq_left hq',zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 1 ≠ 0),zero_pow (by decide : 3 ≠ 0),mul_zero,sub_self,le_refl]

end Yau.Proofs.F03Aux
