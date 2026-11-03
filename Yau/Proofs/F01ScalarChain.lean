import Yau.LeafProofs.L22LeviCalculus

/-! Scalar composition identities for the actual real Hessian and Levi form. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau

theorem scalar_secondFDeriv_apply {F : ℝ → ℝ} {t : ℝ}
    (hF : ContDiffAt ℝ 2 F t) (a b : ℝ) :
    fderiv ℝ (fderiv ℝ F) t a b = deriv (deriv F) t * a * b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) t :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he : fderiv ℝ (deriv F) t a = fderiv ℝ (fderiv ℝ F) t a 1 := by
    change fderiv ℝ (fun s => fderiv ℝ F s 1) t a = _
    rw [fderiv_clm_apply hd (differentiableAt_const (1 : ℝ))]
    simp
  have hb := (fderiv ℝ (fderiv ℝ F) t a).map_smul b (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at hb
  rw [hb, ← he, fderiv_eq_deriv_mul]
  ring

theorem secondFDeriv_scalar_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {F : ℝ → ℝ} {z : E}
    (hu : ContDiffAt ℝ 2 u z) (hF : ContDiffAt ℝ 2 F (u z)) (v w : E) :
    fderiv ℝ (fderiv ℝ (F ∘ u)) z v w =
      deriv (deriv F) (u z) * (fderiv ℝ u z v) * (fderiv ℝ u z w) +
        deriv F (u z) * fderiv ℝ (fderiv ℝ u) z v w := by
  rw [LeafProofs.L18Aux.secondFDeriv_comp hu hF,
    scalar_secondFDeriv_apply hF, fderiv_eq_deriv_mul]

theorem complexLeviQuadratic_scalar_comp {n : ℕ}
    {u : ComplexVector n → ℝ} {F : ℝ → ℝ} {z : ComplexVector n}
    (hu : ContDiffAt ℝ 2 u z) (hF : ContDiffAt ℝ 2 F (u z))
    (v : ComplexVector n) :
    LeafProofs.L22Aux.complexLeviQuadratic (F ∘ u) z v =
      deriv F (u z) * LeafProofs.L22Aux.complexLeviQuadratic u z v +
      deriv (deriv F) (u z) *
        ((fderiv ℝ u z v) ^ 2 + (fderiv ℝ u z (Complex.I • v)) ^ 2) / 4 := by
  simp only [LeafProofs.L22Aux.complexLeviQuadratic,
    secondFDeriv_scalar_comp hu hF]
  ring

end Yau.NodeProofs.F01Aux
