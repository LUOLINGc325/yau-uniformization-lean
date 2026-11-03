import Yau.Proofs.E02MatrixBasic
import Mathlib.Analysis.Matrix.Order

open Matrix
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- A concrete bound in the actual entrywise matrix norm. The vector
keeps its genuine Euclidean norm; the estimate includes n=0. -/
theorem abs_qform_le_entrywise {n : ℕ} (A : Herm n) (V : ComplexVector n) :
    |qform A V| ≤ (n : ℝ)^2*‖A‖*‖V‖^2 := by
  have hExpand : star (WithLp.ofLp V) ⬝ᵥ (A*ᵥWithLp.ofLp V) =
      ∑ i, ∑ j, star (WithLp.ofLp V i)*A i j*WithLp.ofLp V j := by
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,mul_assoc]
  calc
    |qform A V| ≤ ‖star (WithLp.ofLp V) ⬝ᵥ (A*ᵥWithLp.ofLp V)‖ := Complex.abs_re_le_norm _
    _ = ‖∑ i, ∑ j, star (WithLp.ofLp V i)*A i j*WithLp.ofLp V j‖ := by rw [hExpand]
    _ ≤ ∑ i, ∑ j, ‖star (WithLp.ofLp V i)*A i j*WithLp.ofLp V j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, ‖A‖*‖V‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_mul,norm_star]
      calc
        _ ≤ ‖V‖*‖A‖*‖V‖ := by
          gcongr
          · exact PiLp.norm_apply_le V i
          · exact Matrix.norm_entry_le_entrywise_sup_norm A
          · exact PiLp.norm_apply_le V j
        _ = _ := by ring
    _ = _ := by simp; ring

theorem qform_one {n : ℕ} (V : ComplexVector n) : qform (1 : Herm n) V = ‖V‖^2 := by
  rw [qform,Matrix.one_mulVec,PiLp.norm_sq_eq_of_L2]
  simp only [dotProduct,Complex.re_sum,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.sq_norm,Complex.normSq_apply]
  ring

theorem qform_sub_real_smul {n : ℕ} (A B : Herm n) (c : ℝ) (V : ComplexVector n) :
    qform (A-(c : ℂ) • B) V = qform A V-c*qform B V := by
  simp only [qform,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,
    smul_eq_mul,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

end Yau.NodeProofs.E02Aux
