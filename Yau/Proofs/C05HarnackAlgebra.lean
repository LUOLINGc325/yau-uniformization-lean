import Mathlib.Analysis.Matrix.PosDef

/-! The finite-dimensional cancellation in the scalar Harnack equality calculation. -/

open scoped BigOperators ComplexOrder

noncomputable section

namespace Yau.Proofs.C05Aux

variable {n : ℕ}

def weightedHessianSquare (lam : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, (lam i)⁻¹ * ‖H i j‖ ^ 2

def diagonalHarnackPower (lam : Fin n → ℝ) (k : ℝ) : ℝ :=
  ∑ i, lam i * (lam i + k) ^ 2

theorem complex_norm_sub_real_sq (z : ℂ) (d : ℝ) :
    ‖z - (d : ℂ)‖ ^ 2 = ‖z‖ ^ 2 - 2 * d * z.re + d ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem weightedHessianSquare_shift (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (k : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    weightedHessianSquare lam (M - Matrix.diagonal (fun i => ((lam i * (lam i + k) : ℝ) : ℂ))) =
      weightedHessianSquare lam M - 2 * (∑ i, (lam i + k) * (M i i).re) +
        diagonalHarnackPower lam k := by
  have hrow (i : Fin n) :
      (∑ j, (lam i)⁻¹ * ‖(M - Matrix.diagonal (fun i => ((lam i * (lam i + k) : ℝ) : ℂ))) i j‖ ^ 2) =
        (∑ j, (lam i)⁻¹ * ‖M i j‖ ^ 2) -
          2 * (lam i + k) * (M i i).re + lam i * (lam i + k) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add Finset.univ (fun j => (lam i)⁻¹ * ‖M i j‖ ^ 2) (Finset.mem_univ i)]
    have hoff : (∑ j ∈ Finset.univ.erase i,
        (lam i)⁻¹ * ‖(M - Matrix.diagonal (fun i => ((lam i * (lam i + k) : ℝ) : ℂ))) i j‖ ^ 2) =
        ∑ j ∈ Finset.univ.erase i, (lam i)⁻¹ * ‖M i j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hji.symm, sub_zero]
    rw [hoff]
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, complex_norm_sub_real_sq]
    field_simp [ne_of_gt (hlam i)]
    <;> ring
  unfold weightedHessianSquare diagonalHarnackPower
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hs : (∑ i, 2 * (lam i + k) * (M i i).re) =
      2 * ∑ i, (lam i + k) * (M i i).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]

theorem weightedHessianSquare_nonneg (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (H : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ weightedHessianSquare lam H :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (inv_nonneg.mpr (hlam i)) (sq_nonneg _)

theorem pure_square_le_harnack_error (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosSemidef) (k Z P E : ℝ)
    (hidentity : Z = P + (∑ i, lam i * (M i i).re) -
      2 * k * M.trace.re + weightedHessianSquare lam M - E) :
    P ≤ Z + 2 * k * M.trace.re + |E| := by
  have hdiag : 0 ≤ ∑ i, lam i * (M i i).re := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hlam i) (Complex.nonneg_iff.mp (hM.diag_nonneg (i := i))).1
  have hs := weightedHessianSquare_nonneg lam hlam M
  linarith [le_abs_self E]

end Yau.Proofs.C05Aux
