import Yau.Proofs.C05HessianBlocks
import Yau.Proofs.G01RawAlgebra

/-! The complex mixed block transforms in the same actual complex frame
as the metric and Ricci form. No coordinate chart is changed here. -/

noncomputable section
open scoped BigOperators Matrix
namespace Yau.Proofs.C05Aux
open Yau Matrix Yau.NodeProofs.G01Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

def complexFrameInReal : Matrix (RIdx n) (Fin n) ℂ :=
  fun a j => if a.1 = j then (if a.2 = 0 then 1 else -Complex.I) else 0

theorem hessianMixed_matrix (B : Matrix (RIdx n) (RIdx n) ℝ) :
    hessianMixed B = (1 / 4 : ℂ) •
      ((complexFrameInReal (n := n))ᴴ * B.map Complex.ofRealHom * (complexFrameInReal (n := n))) := by
  ext i j
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,complexFrameInReal,
    Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.map_apply,hessianMixed,
    Matrix.smul_apply,smul_eq_mul]
  simp only [apply_ite]
  simp [Complex.star_def,Finset.sum_add_distrib]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

theorem rawReal_complexFrame (W : Matrix (Fin n) (Fin n) ℂ) :
    (rawReal W).map Complex.ofRealHom * (complexFrameInReal (n := n)) = (complexFrameInReal (n := n)) * W := by
  ext ⟨i,a⟩ j
  fin_cases a <;>
    simp [Matrix.mul_apply,complexFrameInReal,rawReal,Fintype.sum_prod_type,
      Fin.sum_univ_two,Matrix.map_apply]
  <;> apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring

theorem realMatrix_complexify_transpose (J : Matrix (RIdx n) (RIdx n) ℝ) :
    Jᵀ.map Complex.ofRealHom = (J.map Complex.ofRealHom)ᴴ := by
  ext a b
  simp [Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.map_apply]

theorem hessianMixed_congruence (B : Matrix (RIdx n) (RIdx n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    hessianMixed ((rawReal W)ᵀ * B * rawReal W) = Wᴴ * hessianMixed B * W := by
  rw [hessianMixed_matrix,hessianMixed_matrix]
  simp only [Matrix.map_mul,realMatrix_complexify_transpose]
  have hc : (complexFrameInReal (n := n))ᴴ * ((rawReal W).map Complex.ofRealHom)ᴴ =
      Wᴴ * (complexFrameInReal (n := n))ᴴ := by
    rw [← Matrix.conjTranspose_mul,rawReal_complexFrame,Matrix.conjTranspose_mul]
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  calc
    _ = ((complexFrameInReal (n := n))ᴴ * ((rawReal W).map Complex.ofRealHom)ᴴ) *
        B.map Complex.ofRealHom * ((rawReal W).map Complex.ofRealHom * (complexFrameInReal (n := n))) := by
      simp only [Matrix.mul_assoc]
    _ = (Wᴴ * (complexFrameInReal (n := n))ᴴ) * B.map Complex.ofRealHom * ((complexFrameInReal (n := n)) * W) := by
      rw [hc,rawReal_complexFrame]
    _ = _ := by simp only [Matrix.mul_assoc]

end Yau.Proofs.C05Aux
