import Yau.Proofs.C05UnitaryHessian
import Yau.Geometry.Basic

/-! The mixed and pure complex blocks of the same real bilinear form.
The weighted-square identity keeps the normalization G = 2 Re h explicit. -/

noncomputable section
open scoped BigOperators
namespace Yau.Proofs.C05Aux
open Yau Matrix
variable {n : ℕ}

def hessianMixed (B : Matrix (RIdx n) (RIdx n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((B (i,0) (j,0) + B (i,1) (j,1)) / 4 : ℝ) +
    Complex.I * (((B (i,1) (j,0) - B (i,0) (j,1)) / 4 : ℝ) : ℂ)

def hessianPure (B : Matrix (RIdx n) (RIdx n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((B (i,0) (j,0) - B (i,1) (j,1)) / 4 : ℝ) -
    Complex.I * (((B (i,0) (j,1) + B (i,1) (j,0)) / 4 : ℝ) : ℂ)

theorem hessianBlocks_square (B : Matrix (RIdx n) (RIdx n) ℝ) (i j : Fin n) :
    ‖hessianMixed B i j‖ ^ 2 + ‖hessianPure B i j‖ ^ 2 =
      (B (i,0) (j,0) ^ 2 + B (i,0) (j,1) ^ 2 +
        B (i,1) (j,0) ^ 2 + B (i,1) (j,1) ^ 2) / 8 := by
  simp only [hessianMixed,hessianPure,Complex.sq_norm,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add,add_zero]
  ring

theorem hessianBlocks_weighted_square (B : Matrix (RIdx n) (RIdx n) ℝ)
    (lam : Fin n → ℝ) :
    weightedHessianSquare lam (hessianMixed B) + weightedHessianSquare lam (hessianPure B) =
      (1 / 8 : ℝ) * ∑ a : RIdx n, ∑ b : RIdx n, (lam a.1)⁻¹ * B a b ^ 2 := by
  simp only [weightedHessianSquare,← Finset.sum_add_distrib,← mul_add,
    hessianBlocks_square,Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hessianBlocks_entry_quadratic (B : Matrix (RIdx n) (RIdx n) ℝ)
    (v : Fin n → ℂ) (i j : Fin n) :
    2 * (star (v i) * hessianMixed B i j * v j).re +
      2 * (hessianPure B i j * v i * v j).re =
      B (i,0) (j,0) * (v i).re * (v j).re +
      B (i,0) (j,1) * (v i).re * (v j).im +
      B (i,1) (j,0) * (v i).im * (v j).re +
      B (i,1) (j,1) * (v i).im * (v j).im := by
  simp only [hessianMixed,hessianPure,Complex.star_def,Complex.conj_re,
    Complex.conj_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add,add_zero]
  ring

theorem hessianBlocks_quadratic (B : Matrix (RIdx n) (RIdx n) ℝ)
    (v : ComplexVector n) :
    unitaryHessianQuadratic (hessianMixed B) (hessianPure B) (WithLp.ofLp v) =
      ∑ a : RIdx n, ∑ b : RIdx n, B a b * realCoord v a * realCoord v b := by
  unfold unitaryHessianQuadratic
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,← mul_assoc]
  change 2 * Complex.reCLM (∑ i, ∑ j, star (v i) * hessianMixed B i j * v j) +
    2 * Complex.reCLM (∑ i, ∑ j, hessianPure B i j * v i * v j) = _
  have he : 2 * Complex.reCLM (∑ i, ∑ j, star (v i) * hessianMixed B i j * v j) +
      2 * Complex.reCLM (∑ i, ∑ j, hessianPure B i j * v i * v j) =
      ∑ i, ∑ j, (2 * (star (v i) * hessianMixed B i j * v j).re +
        2 * (hessianPure B i j * v i * v j).re) := by
    simp only [map_sum,Finset.mul_sum,Finset.sum_add_distrib]
    rfl
  rw [he]
  simp_rw [hessianBlocks_entry_quadratic]
  simp [Fintype.sum_prod_type,Fin.sum_univ_two,realCoord,Finset.sum_add_distrib]
  <;> ring

theorem hessianMixed_isHermitian (B : Matrix (RIdx n) (RIdx n) ℝ)
    (hB : B.IsSymm) : (hessianMixed B).IsHermitian := by
  ext i j
  have h00 := congrFun (congrFun hB (i,0)) (j,0)
  have h01 := congrFun (congrFun hB (i,0)) (j,1)
  have h10 := congrFun (congrFun hB (i,1)) (j,0)
  have h11 := congrFun (congrFun hB (i,1)) (j,1)
  simp only [transpose_apply] at h00 h01 h10 h11
  apply Complex.ext <;>
    simp only [conjTranspose_apply,hessianMixed,Complex.star_def,
      Complex.conj_re,Complex.conj_im,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add,add_zero]
  · linarith
  · linarith

theorem hessianPure_isSymm (B : Matrix (RIdx n) (RIdx n) ℝ)
    (hB : B.IsSymm) : (hessianPure B).IsSymm := by
  ext i j
  have h00 := congrFun (congrFun hB (i,0)) (j,0)
  have h01 := congrFun (congrFun hB (i,0)) (j,1)
  have h10 := congrFun (congrFun hB (i,1)) (j,0)
  have h11 := congrFun (congrFun hB (i,1)) (j,1)
  simp only [transpose_apply] at h00 h01 h10 h11 ⊢
  unfold hessianPure
  rw [h00,h11,h01,h10]
  ring

end Yau.Proofs.C05Aux
