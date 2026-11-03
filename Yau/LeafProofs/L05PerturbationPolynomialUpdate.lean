import Yau.LeafProofs.L05PerturbationRescaledOperator

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_iter_quad_add {n : ℕ} (A B : Sym n) (x : Space n) :
    perturbQuad (A+B) x=perturbQuad A x+perturbQuad B x := by
  simp only [perturbQuad,(selfAdjoint (Mat n)).coe_add,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

theorem perturb_iter_quad_smul {n : ℕ} (a : ℝ) (A : Sym n) (x : Space n) :
    perturbQuad (a • A) x=a*perturbQuad A x := by
  simp only [perturbQuad,selfAdjoint.val_smul,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem perturb_iter_quad_space_scale {n : ℕ} (a : ℝ) (A : Sym n) (x : Space n) :
    perturbQuad A (a • x)=a^2*perturbQuad A x := by
  simp only [perturbQuad_eq_bilinear,map_smul,smul_apply,smul_eq_mul]
  ring

theorem perturb_iter_polynomial_update {n : ℕ} {r eta : ℝ} (hr : 0 < r)
    (c d q s : ℝ) (b e : Space n →L[ℝ] ℝ) (A B : Sym n) (p : Point n) :
    perturbPolynomial (c+r^(2+eta)*d) (b+r^(1+eta) • e) (A+r^eta • B) (q+r^eta*s)
      (perturbScale r p)=
    perturbPolynomial c b A q (perturbScale r p)+r^(2+eta)*perturbPolynomial d e B s p := by
  simp only [perturbPolynomial,perturbScale,add_apply,smul_apply,map_smul,smul_eq_mul,
    perturb_iter_quad_add,perturb_iter_quad_smul,perturb_iter_quad_space_scale,
    Real.rpow_add hr,Real.rpow_one,Real.rpow_two]
  ring

theorem perturb_iter_polynomial_compatibility {n : ℕ} {r eta q s : ℝ} (hr : 0 < r)
    (Phi : Sym n → Point n → ℝ) (f : Point n → ℝ) (A B : Sym n)
    (hq : q=Phi A (0,0)+f (0,0)) (hs : s=perturbIterOperator Phi A r eta B (0,0)) :
    q+r^eta*s=Phi (A+r^eta • B) (0,0)+f (0,0) := by
  rw [hs,perturbIterOperator,perturbScale_zero]
  rw [← mul_assoc,mul_inv_cancel₀ (Real.rpow_pos_of_pos hr eta).ne',one_mul,hq]
  ring

theorem perturb_iter_increment_bounds {n : ℕ} {r eta K c d q s : ℝ} (hr : 0 < r)
    (b e : Space n →L[ℝ] ℝ) (A B : Sym n)
    (hd : |d| ≤ K) (he : ‖e‖ ≤ K) (hB : ‖B‖ ≤ K) (hs : |s| ≤ K) :
    |(c+r^(2+eta)*d)-c| ≤ K*r^(2+eta) ∧
      ‖(b+r^(1+eta) • e)-b‖ ≤ K*r^(1+eta) ∧
      ‖(A+r^eta • B)-A‖ ≤ K*r^eta ∧ |(q+r^eta*s)-q| ≤ K*r^eta := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [add_sub_cancel_left,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hr (2+eta))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd (Real.rpow_pos_of_pos hr (2+eta)).le
  · rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hr (1+eta))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (Real.rpow_pos_of_pos hr (1+eta)).le
  · rw [add_sub_cancel_left,perturb_sym_smul_norm,abs_of_pos (Real.rpow_pos_of_pos hr eta)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hB (Real.rpow_pos_of_pos hr eta).le
  · rw [add_sub_cancel_left,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hr eta)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos hr eta).le

end Yau.LeafProofs.L05Aux
