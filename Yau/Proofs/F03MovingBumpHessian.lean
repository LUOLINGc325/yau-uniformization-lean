import Yau.Proofs.F03MovingBumpDerivatives

/-! The actual Hessian of the compact cubic, with the zero-interface formula included. -/

noncomputable section
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem movingBallBump_space_hessian (R : ℝ) (c : ℝ → E) (x v w : E) (t : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => movingBallBump R c (y, t))) x v w =
      24 * positivePower 1 (R ^ 2 - ‖x - c t‖ ^ 2) * ⟪x - c t, v⟫_ℝ * ⟪x - c t, w⟫_ℝ -
        6 * positivePower 2 (R ^ 2 - ‖x - c t‖ ^ 2) * ⟪v, w⟫_ℝ := by
  let S : E → ℝ := fun y => R ^ 2 - ‖y - c t‖ ^ 2
  have hs : HasFDerivAt S (-(2 • innerSL ℝ (x - c t))) x := by
    simpa only [S, id_eq, ContinuousLinearMap.comp_id] using
      (((hasFDerivAt_id x).sub_const (c t)).norm_sq.const_sub (R ^ 2))
  let a : E → ℝ := fun y => -6 * positivePower 2 (S y)
  let b : E → E →L[ℝ] ℝ := fun y => innerSL ℝ (y - c t)
  have ha := ((positivePower_hasDerivAt 2 (by omega) (S x)).comp_hasFDerivAt x hs).const_mul (-6)
  change HasFDerivAt a _ x at ha
  have hb : HasFDerivAt b (innerSL ℝ) x := by
    simpa only [b, id_eq, Function.comp_def, ContinuousLinearMap.comp_id] using
      ((innerSL ℝ).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (c t)))
  have hab := ha.smul hb
  have heq : fderiv ℝ (fun y => movingBallBump R c (y, t)) = a • b := by
    funext y
    exact (movingBallBump_space_hasFDerivAt R c y t).fderiv
  rw [heq, hab.fderiv]
  simp only [a, b, S, smul_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, neg_apply, smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub]
  rw [show ((innerSL ℝ) v) w = ⟪v, w⟫_ℝ from rfl]
  ring

end Yau.Proofs.F03Aux
