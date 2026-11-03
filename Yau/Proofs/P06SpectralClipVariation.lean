import Yau.Proofs.P06SpectralClipSlope

noncomputable section

namespace Yau.NodeProofs.P06Aux.Clip

def polynomialVariation {A : Type*} [Ring A] [Algebra ℝ A]
    (p : Polynomial ℝ) (S D : A) : A :=
  ∑ m ∈ p.support, p.coeff m • powerVariation S D m

theorem polynomialVariation_map {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]
    (f : A →ₐ[ℝ] B) (p : Polynomial ℝ) (S D : A) :
    polynomialVariation p (f S) (f D) = f (polynomialVariation p S D) := by
  classical
  simp only [polynomialVariation, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro m _
  exact congrArg (fun z : B => p.coeff m • z) (powerVariation_map f.toRingHom S D m)

theorem polynomialVariation_diagonal_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Polynomial ℝ) (lam : ι → ℝ) (D : Matrix ι ι ℝ) (i j : ι) :
    polynomialVariation p (Matrix.diagonal lam) D i j = D i j * polynomialSlope p (lam i) (lam j) := by
  classical
  simp only [polynomialVariation, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    powerVariation_diagonal_apply, polynomialSlope, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

def matrixEntryEnergy {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, D i j ^ 2

/-- At a single eigenbasis, the actual full polynomial differential
contracts every matrix direction in Hilbert–Schmidt energy. The matrix
direction need not commute with the diagonal matrix. -/
theorem polynomialVariation_diagonal_energy_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Polynomial ℝ) {R : ℝ} (lam : ι → ℝ) (D : Matrix ι ι ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (-R) R)
    (hder : ∀ x ∈ Set.Icc (-R) R, |p.derivative.eval x| ≤ 1) :
    matrixEntryEnergy (polynomialVariation p (Matrix.diagonal lam) D) ≤ matrixEntryEnergy D := by
  classical
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [polynomialVariation_diagonal_apply]
  have hs := polynomialSlope_abs_le_one p hder (hlam i) (hlam j)
  have ha : |D i j * polynomialSlope p (lam i) (lam j)| ≤ |D i j| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans_eq (mul_one _)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2

end Yau.NodeProofs.P06Aux.Clip
