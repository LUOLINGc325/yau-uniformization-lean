import Yau.Proofs.F01DiagonalCovectorNorm

/-! The actual full negative squared matrix jet controls its fixed row,
with exactly the reciprocal eigenvalue and cotangent scaling factors. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem weighted_row_square_le_total (weights : Fin n → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    (∑ i, weights i * weights a * Complex.normSq (U a i)) ≤
      ∑ i, ∑ j, weights i * weights j * Complex.normSq (U j i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => mul_nonneg (mul_nonneg (hw i) (hw j)) (Complex.normSq_nonneg (U j i)))
    (Finset.mem_univ a)

theorem negative_matrix_square_controls_row (values : Fin n → ℝ) (hv : ∀ i, 0 < values i)
    (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    dualNormMat (Matrix.diagonal (fun i => (values i : ℂ)))
      (WithLp.toLp 2 (fun i => U a i / (values a : ℂ))) ≤
        (values a)⁻¹ * ∑ i, ∑ j, (values i)⁻¹ * (values j)⁻¹ * Complex.normSq (U j i) := by
  rw [dualNormMat_real_diagonal values (fun i => (hv i).ne')]
  have heq : (∑ i, (values i)⁻¹ * Complex.normSq (U a i / (values a : ℂ))) =
      (values a)⁻¹ * ∑ i, (values i)⁻¹ * (values a)⁻¹ * Complex.normSq (U a i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.normSq_div, Complex.normSq_ofReal]
    field_simp [(hv a).ne']
    <;> ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (weighted_row_square_le_total (fun i => (values i)⁻¹) (fun i => inv_nonneg.mpr (hv i).le) U a)
    (inv_nonneg.mpr (hv a).le)

end Yau.NodeProofs.F01Aux
