import Yau.Proofs.F01WeightedCovectorCauchy
import Yau.Proofs.F01DiagonalCovectorNorm

/-! The gradient comparison with the actual matrix trace in the positive
diagonal normal frame. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem weightedCovectorSquare_le_total (weights : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (ξ : Fin n → ℂ) :
    weightedCovectorSquare weights ξ ≤
      (∑ i, weights i) * ∑ i, Complex.normSq (ξ i) := by
  unfold weightedCovectorSquare
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)) (Complex.normSq_nonneg _)

theorem real_smul_one_eq_diagonal (E : ℝ) :
    (E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun _ => (E : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.one_apply, Matrix.diagonal_apply, hij]

theorem traceWith_real_diagonal_smul_one (values : Fin n → ℝ)
    (hv : ∀ i, values i ≠ 0) (E : ℝ) :
    traceWith (Matrix.diagonal (fun i => (values i : ℂ)))
        ((E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = E * ∑ i, (values i)⁻¹ := by
  unfold traceWith
  rw [inverse_real_diagonal values hv, real_smul_one_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dualNormMat_diagonal_le_trace (values : Fin n → ℝ)
    (hv : ∀ i, 0 < values i) (E : ℝ) (hE : 0 < E) (ξ : Fin n → ℂ) :
    dualNormMat (Matrix.diagonal (fun i => (values i : ℂ))) (WithLp.toLp 2 ξ) ≤
      traceWith (Matrix.diagonal (fun i => (values i : ℂ)))
        ((E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *
          dualNormMat ((E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (WithLp.toLp 2 ξ) := by
  rw [dualNormMat_real_diagonal values (fun i => (hv i).ne'),
    traceWith_real_diagonal_smul_one values (fun i => (hv i).ne'),
    real_smul_one_eq_diagonal, dualNormMat_real_diagonal (fun _ : Fin n => E) (fun _ => hE.ne')]
  have hh := weightedCovectorSquare_le_total (fun i => (values i)⁻¹)
    (fun i => inv_nonneg.mpr (hv i).le) ξ
  change (∑ i, (values i)⁻¹ * Complex.normSq (ξ i)) ≤ _ at hh
  rw [← Finset.mul_sum]
  calc
    _ ≤ (∑ i, (values i)⁻¹) * ∑ i, Complex.normSq (ξ i) := hh
    _ = _ := by field_simp

end Yau.NodeProofs.F01Aux
