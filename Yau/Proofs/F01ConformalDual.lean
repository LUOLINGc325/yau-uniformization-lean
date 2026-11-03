import Yau.Proofs.F01ConformalMetric
import Yau.LeafProofs.L12

/-! Actual inverse-matrix and cotangent-norm scaling for exp(f)g. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem matrix_inv_smul_of_ne_zero (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : IsUnit H.det) (a : ℂ) (ha : a ≠ 0) :
    (a • H)⁻¹ = a⁻¹ • H⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha,
    one_smul, Matrix.nonsing_inv_mul _ hH]

theorem dualNormMat_real_smul (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : IsUnit H.det) (a : ℝ) (ha : a ≠ 0) (ξ : ComplexVector n) :
    dualNormMat ((a : ℂ) • H) ξ = a⁻¹ * dualNormMat H ξ := by
  rw [dualNormMat, matrix_inv_smul_of_ne_zero H hH _ (Complex.ofReal_ne_zero.mpr ha),
    Matrix.transpose_smul, Matrix.smul_mulVec, dotProduct_smul]
  simp only [← Complex.ofReal_inv, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, dualNormMat]

theorem conformalField_dualNormMat (g : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) (ξ : ComplexVector n) :
    dualNormMat (gMat (conformalField g f) x) ξ =
      Real.exp (-f x) * dualNormMat (gMat g x) ξ := by
  have hdet : IsUnit (gMat g x).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hpos := LeafProofs.L12Aux.hMat_det_re_pos g x (mem_extChartAt_target x)
    change 0 < (gMat g x).det.re at hpos
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  rw [conformalField_gMat, dualNormMat_real_smul _ hdet _ (Real.exp_pos _).ne',
    Real.exp_neg]

theorem conformalField_gradNormSq (g : HermitianField M) (f u : M.Carrier → ℝ)
    (x : M.Carrier) :
    gradNormSq (conformalField g f) u x = Real.exp (-f x) * gradNormSq g u x := by
  exact conformalField_dualNormMat g f x _

end Yau.NodeProofs.F01Aux
