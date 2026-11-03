import Yau.Proofs.C05HessianFrameChange

/-! Realification preserves the same complex frame and its real quadratic form. -/
noncomputable section
open scoped Matrix BigOperators
namespace Yau.Proofs.C05HessianFrameEnergyBindingAux
open Yau Yau.NodeProofs.G01Aux
variable {n : ℕ}

theorem rawReal_det_ne_zero (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.det ≠ 0) :
    (rawReal W).det ≠ 0 := by
  apply Matrix.det_ne_zero_of_left_inverse (B := rawReal W⁻¹)
  rw [← rawReal_mul, Matrix.nonsing_inv_mul W (isUnit_iff_ne_zero.mpr hW), rawReal_one]

theorem rawReal_congruence (H W : Matrix (Fin n) (Fin n) ℂ) :
    (rawReal W)ᵀ * rawReal H * rawReal W = rawReal (Wᴴ * H * W) := by
  rw [rawReal_mul, rawReal_mul, rawReal_conjTranspose]

theorem rawReal_diagonal (lam : Fin n → ℝ) :
    rawReal (Matrix.diagonal (fun j => (lam j : ℂ))) =
      Matrix.diagonal (fun a : RIdx n => lam a.1) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;> by_cases hij : i = j <;>
    simp [rawReal, hij]

theorem rawReal_mulVec (W : Matrix (Fin n) (Fin n) ℂ) (w : ComplexVector n) :
    rawReal W *ᵥ realCoord w =
      realCoord (WithLp.toLp 2 (W *ᵥ WithLp.ofLp w)) := by
  ext ⟨i,a⟩
  fin_cases a <;>
    simp [Matrix.mulVec, dotProduct, rawReal, realCoord, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, Complex.re_sum,
      Complex.im_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring

theorem real_quadratic_congruence (B J : Matrix (RIdx n) (RIdx n) ℝ)
    (u : RIdx n → ℝ) :
    (J *ᵥ u) ⬝ᵥ (B *ᵥ (J *ᵥ u)) = u ⬝ᵥ ((Jᵀ * B * J) *ᵥ u) := by
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem real_double_sum_quadratic (B : Matrix (RIdx n) (RIdx n) ℝ)
    (u : RIdx n → ℝ) :
    (∑ a, ∑ b, B a b * u a * u b) = u ⬝ᵥ (B *ᵥ u) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Yau.Proofs.C05HessianFrameEnergyBindingAux
