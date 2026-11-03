import Yau.LeafProofs.L22LeviCalculus

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L22Aux

set_option backward.isDefEq.respectTransparency false in
theorem complexLeviQuadratic_norm_sq {n : ℕ} (z v : ComplexVector n) :
    complexLeviQuadratic (fun w : ComplexVector n => ‖w‖^2) z v = ‖v‖^2 := by
  have HD : fderiv ℝ (fderiv ℝ (fun w : ComplexVector n => ‖w‖^2)) z =
      2 • innerSL ℝ (E := ComplexVector n) := by
    rw [fderiv_norm_sq]
    exact (2 • innerSL ℝ (E := ComplexVector n)).fderiv
  have hi (w : ComplexVector n) : (innerSL ℝ (E := ComplexVector n)) w w = ‖w‖^2 := by
    change inner ℝ w w = ‖w‖^2
    exact real_inner_self_eq_norm_sq w
  unfold complexLeviQuadratic
  rw [HD]
  simp only [two_smul,add_apply,hi,norm_smul,Complex.norm_I,one_mul]
  ring

theorem quadratic_levi_posDef {n : ℕ} (a : ℝ) (ha : 0 < a) (z : ComplexVector n) :
    (leviC (fun w : ComplexVector n => a*‖w‖^2) z).PosDef := by
  have hc : ContDiffAt ℝ 2 (fun w : ComplexVector n => a*‖w‖^2) z :=
    contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt
  apply (leviC_posDef_iff hc).mpr
  intro v hv
  rw [complexLeviQuadratic_const_mul (contDiff_norm_sq ℝ).contDiffAt,
    complexLeviQuadratic_norm_sq]
  exact mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hv))

end Yau.NodeProofs.P02Aux
