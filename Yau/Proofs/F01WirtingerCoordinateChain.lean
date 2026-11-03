import Yau.LeafProofs.L14

/-! Unbarred coordinate chain and constant-factor rules, reusing the proved
native barred chain and conjugation identities. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem wirt_comp_complex_differentiable (T : E → F) (f : F → ℂ) (z v : E)
    (hT : DifferentiableAt ℂ T z) (hf : DifferentiableAt ℝ f (T z)) :
    wirt (fun w => f (T w)) z v = wirt f (T z) (fderiv ℂ T z v) := by
  have h := L14Aux.wirtBar_comp_complex_differentiable T (fun y => star (f y)) z v hT hf.star
  rw [L14Aux.wirtBar_star, L14Aux.wirtBar_star] at h
  exact star_injective h

theorem wirt_const_mul_rule (c : ℂ) {f : E → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f z) (v : E) :
    wirt (fun w => c * f w) z v = c * wirt f z v := by
  unfold wirt
  rw [fderiv_const_mul hf]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem wirt_mul_const_rule (c : ℂ) {f : E → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f z) (v : E) :
    wirt (fun w => f w * c) z v = wirt f z v * c := by
  simpa only [mul_comm] using wirt_const_mul_rule c hf v

end Yau.NodeProofs.F01Aux
