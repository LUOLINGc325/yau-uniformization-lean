import Yau.Proofs.G01RawPairing

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.G01Aux
open Yau
variable {n : ℕ}

theorem complexMatrixPairing_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (W Z : ComplexVector n) :
    complexMatrixPairing (c • A) W Z = c * complexMatrixPairing A W Z := by
  simp only [complexMatrixPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexMatrixPairing_sub (A B : Matrix (Fin n) (Fin n) ℂ)
    (W Z : ComplexVector n) :
    complexMatrixPairing (A - B) W Z =
      complexMatrixPairing A W Z - complexMatrixPairing B W Z := by
  simp only [complexMatrixPairing, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Reordering the four finite real sums before reconstructing the complex pairing. -/
theorem raw_pairing_weighted (A : Matrix (Fin n) (Fin n) ℂ)
    (W Z : ComplexVector n) (u v : ℝ) :
    (∑ c, ∑ d, 2 * rawReal A d c * u * v * realCoord W c * realCoord Z d) =
      2 * (complexMatrixPairing A W Z).re * u * v := by
  rw [← rawReal_pairing]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  ring

end Yau.NodeProofs.G01Aux
