import Yau.Proofs.F01ScalarChain

/-! The actual Levi chain rule after scaling the argument by L. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem complexLeviQuadratic_div_const {u : ComplexVector n → ℝ} {z : ComplexVector n}
    (hu : ContDiffAt ℝ 2 u z) (L : ℝ) (v : ComplexVector n) :
    LeafProofs.L22Aux.complexLeviQuadratic (fun w => u w / L) z v =
      LeafProofs.L22Aux.complexLeviQuadratic u z v / L := by
  have he : (fun w => u w / L) = (fun w => L⁻¹ * u w) := by
    funext w
    ring
  rw [he, LeafProofs.L22Aux.complexLeviQuadratic_const_mul hu]
  ring

theorem fderiv_div_const_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z : E} (hu : DifferentiableAt ℝ u z) (L : ℝ) (v : E) :
    fderiv ℝ (fun w => u w / L) z v = fderiv ℝ u z v / L := by
  have he : (fun w => u w / L) = (fun w => L⁻¹ * u w) := by
    funext w
    ring
  rw [he, fderiv_const_mul hu]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem complexLeviQuadratic_scaled_scalar_comp {u : ComplexVector n → ℝ}
    {F : ℝ → ℝ} {z : ComplexVector n} (L : ℝ)
    (hu : ContDiffAt ℝ 2 u z) (hF : ContDiffAt ℝ 2 F (u z / L))
    (v : ComplexVector n) :
    LeafProofs.L22Aux.complexLeviQuadratic (fun w => F (u w / L)) z v =
      (deriv F (u z / L) / L) * LeafProofs.L22Aux.complexLeviQuadratic u z v +
      (deriv (deriv F) (u z / L) / L ^ 2) *
        (((fderiv ℝ u z v) ^ 2 + (fderiv ℝ u z (Complex.I • v)) ^ 2) / 4) := by
  have he := complexLeviQuadratic_scalar_comp (hu.div_const L) hF v
  rw [complexLeviQuadratic_div_const hu,
    fderiv_div_const_apply (hu.differentiableAt (by norm_num)),
    fderiv_div_const_apply (hu.differentiableAt (by norm_num))] at he
  change LeafProofs.L22Aux.complexLeviQuadratic (fun w => F (u w / L)) z v = _ at he
  rw [he]
  ring

end Yau.NodeProofs.F01Aux
