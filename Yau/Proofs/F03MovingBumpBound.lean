import Yau.Proofs.F03MovingBumpHessian

/-! The finite uniform zeroth-order correction for the actual moving cubic. -/
noncomputable section
namespace Yau.Proofs.F03Aux

theorem linear_div_quadratic_bound (a b q : ℝ) (hb : 0 < b) (hq : 0 < q) :
    a/q-b/q^2 ≤ a^2/(4*b) := by
  apply (le_div_iff₀ (show 0 < 4*b by positivity)).mpr
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hq)).mp
  have hs := sq_nonneg (a*q-2*b)
  field_simp
  nlinarith only [hs]

/-- One finite number controls the moving cubic's differential quotient,
including the thin annulus where the distance to its support face vanishes. -/
theorem moving_cubic_quotient_bound (R lam P d : ℝ)
    (hR : 0 < R) (hlam : 0 < lam) (hP : 0 ≤ P) (hd : d^2 < R^2) :
    3*P/(R^2-d^2)-24*lam*d^2/(R^2-d^2)^2 ≤
      max (4*P/R^2) (3*P^2/(8*lam*R^2)) := by
  let q := R^2-d^2
  have hq : 0 < q := sub_pos.mpr hd
  by_cases hin : d^2 ≤ R^2/4
  · have hfirst : 3*P/q ≤ 4*P/R^2 := by
      apply (div_le_div_iff₀ hq (sq_pos_of_pos hR)).mpr
      dsimp only [q]
      nlinarith only [hin,hP]
    have hsecond : 0 ≤ 24*lam*d^2/q^2 := by positivity
    exact (sub_le_self _ hsecond).trans (hfirst.trans (le_max_left _ _))
  · have hout : R^2/4 ≤ d^2 := (lt_of_not_ge hin).le
    have hb : 0 < 6*lam*R^2 := by positivity
    have hsecond : 6*lam*R^2/q^2 ≤ 24*lam*d^2/q^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg q)
      nlinarith only [hout,hlam]
    have hnum := linear_div_quadratic_bound (3*P) (6*lam*R^2) q hb hq
    have hrat : (3*P)^2/(4*(6*lam*R^2))=3*P^2/(8*lam*R^2) := by ring
    rw [hrat] at hnum
    exact (sub_le_sub_left hsecond _).trans (hnum.trans (le_max_right _ _))

end Yau.Proofs.F03Aux
