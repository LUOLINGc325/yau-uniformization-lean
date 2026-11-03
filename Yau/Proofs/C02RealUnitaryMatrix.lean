import Yau.Proofs.G01Realification
import Yau.Proofs.C02UnitaryMatrixTrace

/-! The complex unitary frame induces a genuine orthonormal real frame
for the physical matrix 2 Re h, with the required factor 1/sqrt(2). -/

noncomputable section
open scoped Matrix
namespace Yau.Blueprint.C02Proof
open Yau.NodeProofs.G01Aux
variable {n : ℕ}

theorem rawReal_conjTranspose (S : Matrix (Fin n) (Fin n) ℂ) :
    rawReal S.conjTranspose = (rawReal S).transpose := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [rawReal, Matrix.conjTranspose_apply, Matrix.transpose_apply]

def physicalUnitaryRealMatrix (S : Matrix (Fin n) (Fin n) ℂ) : Matrix (RIdx n) (RIdx n) ℝ :=
  (Real.sqrt (2 : ℝ))⁻¹ • rawReal S

theorem physicalUnitaryRealMatrix_gram (H S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.conjTranspose * H * S = 1) :
    (physicalUnitaryRealMatrix S).transpose * ((2 : ℝ) • rawReal H) * physicalUnitaryRealMatrix S = 1 := by
  have hs : (Real.sqrt (2 : ℝ))⁻¹ * 2 * (Real.sqrt (2 : ℝ))⁻¹ = 1 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    nlinarith
  simp only [physicalUnitaryRealMatrix, Matrix.transpose_smul, ← rawReal_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← rawReal_mul, ← rawReal_mul, hS, rawReal_one]
  convert (one_smul ℝ (1 : Matrix (RIdx n) (RIdx n) ℝ)) using 1 <;> congr 1 <;> nlinarith [hs]

theorem inverseMetric_of_orthonormalMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G D : Matrix ι ι ℝ) (hD : D.transpose * G * D = 1) : G⁻¹ = D * D.transpose := by
  apply Matrix.inv_eq_left_inv
  have hRight : D * (D.transpose * G) = 1 := mul_eq_one_comm.mp hD
  simpa only [Matrix.mul_assoc] using hRight

end Yau.Blueprint.C02Proof
