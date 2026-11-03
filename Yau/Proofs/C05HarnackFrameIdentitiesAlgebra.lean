import Yau.Proofs.C05HarnackEvolutionAlgebra
import Mathlib.Tactic.Abel

/-! Trace identities in one and the same normalized complex frame. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Proofs.C05HarnackFrameIdentitiesAux
open Yau.Proofs.C05Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem inverse_eq_frame_gram (g W : Matrix (Fin n) (Fin n) ℂ)
    (hdet : W.det ≠ 0) (hGram : Wᴴ*g*W=1) : g⁻¹=W*Wᴴ := by
  have hWW := Matrix.mul_nonsing_inv W (isUnit_iff_ne_zero.mpr hdet)
  apply Matrix.inv_eq_left_inv
  calc
    _ = ((W*Wᴴ)*g)*(W*W⁻¹) := by rw [hWW,Matrix.mul_one]
    _ = W*(Wᴴ*g*W)*W⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hGram,Matrix.mul_one,hWW]

theorem frame_metric_product (g A B W : Matrix (Fin n) (Fin n) ℂ)
    (hdet : W.det ≠ 0) (hGram : Wᴴ*g*W=1) :
    Wᴴ*(A*g⁻¹*B)*W=(Wᴴ*A*W)*(Wᴴ*B*W) := by
  rw [inverse_eq_frame_gram g W hdet hGram]
  simp only [Matrix.mul_assoc]

theorem frame_trace (g B W : Matrix (Fin n) (Fin n) ℂ)
    (hdet : W.det ≠ 0) (hGram : Wᴴ*g*W=1) :
    (Wᴴ*B*W).trace=(g⁻¹*B).trace := by
  rw [Matrix.trace_mul_cycle,←inverse_eq_frame_gram g W hdet hGram]

theorem frame_pairing_trace (g A B W : Matrix (Fin n) (Fin n) ℂ)
    (hdet : W.det ≠ 0) (hGram : Wᴴ*g*W=1) :
    (g⁻¹*A*g⁻¹*B).trace=((Wᴴ*A*W)*(Wᴴ*B*W)).trace := by
  calc
    _ = (g⁻¹*(A*g⁻¹*B)).trace := by simp only [Matrix.mul_assoc]
    _ = (Wᴴ*(A*g⁻¹*B)*W).trace := (frame_trace g _ W hdet hGram).symm
    _ = _ := by rw [frame_metric_product g A B W hdet hGram]

theorem diagonal_pairing_trace (lam : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    ((Matrix.diagonal (fun j => (lam j:ℂ)))*B).trace.re = ∑ j,lam j*(B j j).re := by
  simp [Matrix.trace,Matrix.diagonal_mul,Complex.mul_re]

theorem frame_hessian_shift (g A H W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (κ : ℝ) (hdet : W.det ≠ 0) (hGram : Wᴴ*g*W=1)
    (hDiag : Wᴴ*A*W=Matrix.diagonal (fun j => (lam j:ℂ))) :
    Wᴴ*H*W = Wᴴ*(H+A*g⁻¹*A+(κ:ℂ)•A)*W -
      Matrix.diagonal (fun j => ((lam j*(lam j+κ):ℝ):ℂ)) := by
  have hp := frame_metric_product g A A W hdet hGram
  have hshift : Wᴴ*(A*g⁻¹*A)*W+(κ:ℂ)•(Wᴴ*A*W) =
      Matrix.diagonal (fun j => ((lam j*(lam j+κ):ℝ):ℂ)) := by
    rw [hp,hDiag,Matrix.diagonal_mul_diagonal,←Matrix.diagonal_smul,Matrix.diagonal_add]
    congr 1
    funext j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    push_cast
    ring
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]
  rw [←hshift]
  abel

theorem frame_leading_identity (g A H W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (κ : ℝ) (hdet : W.det ≠ 0) (hGram : Wᴴ*g*W=1)
    (hDiag : Wᴴ*A*W=Matrix.diagonal (fun j => (lam j:ℂ))) :
    3*(g⁻¹*A*g⁻¹*H).trace.re+2*(g⁻¹*A*g⁻¹*A*g⁻¹*A).trace.re+
      κ*(g⁻¹*A*g⁻¹*A).trace.re-κ^2*(g⁻¹*A).trace.re =
        diagonalScalarHarnackEvolution lam κ (Wᴴ*(H+A*g⁻¹*A+(κ:ℂ)•A)*W) := by
  have hpair : (g⁻¹*A*g⁻¹*H).trace.re = ∑ j,lam j*((Wᴴ*H*W) j j).re := by
    rw [frame_pairing_trace g A H W hdet hGram,hDiag,diagonal_pairing_trace]
  have hsquare : (g⁻¹*A*g⁻¹*A).trace.re = ∑ j,lam j^2 := by
    rw [frame_pairing_trace g A A W hdet hGram,hDiag,Matrix.diagonal_mul_diagonal]
    simp [Matrix.trace,pow_two]
  have hcube : (g⁻¹*A*g⁻¹*A*g⁻¹*A).trace.re = ∑ j,lam j^3 := by
    have hh := frame_pairing_trace g (A*g⁻¹*A) A W hdet hGram
    rw [frame_metric_product g A A W hdet hGram,hDiag,
      Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal] at hh
    have hh' := congrArg Complex.re hh
    simp only [Matrix.mul_assoc] at hh' ⊢
    rw [hh']
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.diagonal_apply_eq,Complex.re_sum,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
      zero_mul,sub_zero,add_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hscalar : (g⁻¹*A).trace.re = ∑ j,lam j := by
    rw [←frame_trace g A W hdet hGram,hDiag]
    simp [Matrix.trace]
  unfold diagonalScalarHarnackEvolution
  rw [←frame_hessian_shift g A H W lam κ hdet hGram hDiag]
  rw [hpair,hsquare,hcube,hscalar]

end Yau.Proofs.C05HarnackFrameIdentitiesAux
