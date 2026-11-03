import Yau.Proofs.C04MatrixCauchy
import Yau.Proofs.C04HarnackScalar
import Yau.Proofs.C04MatrixForms

/-! The matrix Harnack tensor and its actual nonnegative variance imply monotonic logarithmic dual rate. -/

noncomputable section
open scoped ComplexOrder Matrix

namespace Yau.Proofs.C04Aux
open Yau Blueprint Matrix
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem matrix_harnack_form_nonneg (K R R' : Herm n) (hK : K.IsHermitian)
    (t : ℝ) (hB : (R' + R * K * R + ((t⁻¹ : ℝ) : ℂ) • R).PosSemidef)
    (v : Fin n → ℂ) :
    0 ≤ Blueprint.Alignment.Y03Proof.matrixForm (K * R' * K) v +
      Blueprint.Alignment.Y03Proof.matrixForm (K * R * K * R * K) v +
      t⁻¹ * Blueprint.Alignment.Y03Proof.matrixForm (K * R * K) v := by
  have hconj := hB.conjTranspose_mul_mul_same K
  simp only [hK.eq] at hconj
  have hm : K * (R' + R * K * R + ((t⁻¹ : ℝ) : ℂ) • R) * K =
      K * R' * K + K * R * K * R * K + ((t⁻¹ : ℝ) : ℂ) • (K * R * K) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hm] at hconj
  have hh := hconj.re_dotProduct_nonneg v
  change 0 ≤ Blueprint.Alignment.Y03Proof.matrixForm
    (K * R' * K + K * R * K * R * K + ((t⁻¹ : ℝ) : ℂ) • (K * R * K)) v at hh
  simpa only [matrixForm_add, matrixForm_real_smul] using hh

theorem matrix_harnack_lograte_nonneg (K R R' : Herm n) (hK : K.PosDef)
    (hR : R.IsHermitian) (t : ℝ) (ht : 0 < t)
    (hB : (R' + R * K * R + ((t⁻¹ : ℝ) : ℂ) • R).PosSemidef)
    (v : Fin n → ℂ) (hv : v ≠ 0) :
    let F := Blueprint.Alignment.Y03Proof.matrixForm K v
    let N := Blueprint.Alignment.Y03Proof.matrixForm (K * R * K) v
    let T := Blueprint.Alignment.Y03Proof.matrixForm (K * R' * K) v
    let V := Blueprint.Alignment.Y03Proof.matrixForm (K * R * K * R * K) v
    0 ≤ N / F + t * (((T + 2 * V) * F - N ^ 2) / F ^ 2) := by
  dsimp only
  exact log_rate_derivative_nonneg t _ _ _ _ ht (hK.re_dotProduct_pos hv)
    (matrix_harnack_form_nonneg K R R' hK.isHermitian t hB v)
    (inverse_ricci_variance K R hK hR v)

end Yau.Proofs.C04Aux
