import Yau.Proofs.F03MovingBump

/-! Actual first derivatives of the compact moving cubic, including its zero interface. -/

noncomputable section
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem movingBallBump_time_hasDerivAt (R : ℝ) {c : ℝ → E} {c' : E}
    (x : E) {t : ℝ} (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s => movingBallBump R c (x, s))
      (6 * positivePower 2 (R ^ 2 - ‖x - c t‖ ^ 2) * ⟪x - c t, c'⟫_ℝ) t := by
  have hs := ((hc.const_sub x).norm_sq).const_sub (R ^ 2)
  have hp := (positivePower_hasDerivAt 3 (by omega) (R ^ 2 - ‖x - c t‖ ^ 2)).comp t hs
  convert hp using 1
  · rfl
  · simp only [Nat.cast_ofNat, Nat.reduceSub, inner_neg_right]
    ring

theorem movingBallBump_space_hasFDerivAt (R : ℝ) (c : ℝ → E) (x : E) (t : ℝ) :
    HasFDerivAt (fun y => movingBallBump R c (y, t))
      ((-6 * positivePower 2 (R ^ 2 - ‖x - c t‖ ^ 2)) • innerSL ℝ (x - c t)) x := by
  have hs : HasFDerivAt (fun y : E => R ^ 2 - ‖y - c t‖ ^ 2)
      (-(2 • innerSL ℝ (x - c t))) x := by
    simpa only [id_eq, ContinuousLinearMap.comp_id] using
      (((hasFDerivAt_id x).sub_const (c t)).norm_sq.const_sub (R ^ 2))
  have hp := (positivePower_hasDerivAt 3 (by omega)
    (R ^ 2 - ‖x - c t‖ ^ 2)).comp_hasFDerivAt x hs
  convert hp using 1
  · rfl
  · ext v
    simp only [smul_apply, neg_apply, smul_eq_mul,
      Nat.cast_ofNat, Nat.reduceSub]
    ring

theorem movingBallBump_space_fderiv_apply (R : ℝ) (c : ℝ → E) (x v : E) (t : ℝ) :
    fderiv ℝ (fun y => movingBallBump R c (y, t)) x v =
      -6 * positivePower 2 (R ^ 2 - ‖x - c t‖ ^ 2) * ⟪x - c t, v⟫_ℝ := by
  rw [(movingBallBump_space_hasFDerivAt R c x t).fderiv]
  rfl

end Yau.Proofs.F03Aux
