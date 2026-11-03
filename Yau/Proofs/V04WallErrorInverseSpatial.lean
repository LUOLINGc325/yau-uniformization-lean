import Yau.Proofs.G01ChernCalculus
import Yau.Proofs.V03MetricSmooth

/-! First spatial derivatives of the genuine inverse metric, obtained by
differentiating its local matrix identity on a valid chart. -/

open Filter
open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.G01Aux

variable {n r : ℕ}

theorem matrixWirt_inverse {H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ}
    {U : Set (ComplexVector n)} (hU : IsOpen U)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hdet : ∀ z ∈ U, (H z).det ≠ 0) {z : ComplexVector n} (hz : z ∈ U) (k : Fin n) :
    matrixWirt (fun w => (H w)⁻¹) z k =
      -(H z)⁻¹ * matrixWirt H z k * (H z)⁻¹ := by
  have hHD (i j : Fin r) : DifferentiableAt ℝ (fun w => H w i j) z :=
    ((hH i j).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hID (i j : Fin r) : DifferentiableAt ℝ (fun w => (H w)⁻¹ i j) z :=
    ((entrywise_matrix_inv_contDiffOn hH hdet i j).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hzero : matrixWirt H z k * (H z)⁻¹ +
      H z * matrixWirt (fun w => (H w)⁻¹) z k = 0 := by
    rw [← matrixWirt_mul H (fun w => (H w)⁻¹) z hHD hID k]
    ext i j
    have heq : (fun w => (H w * (H w)⁻¹) i j) =ᶠ[𝓝 z]
        (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) i j) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact congrArg (fun B : Matrix (Fin r) (Fin r) ℂ => B i j)
        (Matrix.mul_nonsing_inv (H w) (isUnit_iff_ne_zero.mpr (hdet w hw)))
    have hconst := (hasFDerivAt_const (𝕜 := ℝ) ((1 : Matrix (Fin r) (Fin r) ℂ) i j) z).fderiv
    simp only [matrixWirt, wirt, heq.fderiv_eq (𝕜 := ℝ), hconst,
      zero_apply, mul_zero, sub_zero, Matrix.zero_apply]
  have he := congrArg (fun B => (H z)⁻¹ * B) hzero
  rw [Matrix.mul_add, ← Matrix.mul_assoc ((H z)⁻¹) (H z)
      (matrixWirt (fun w => (H w)⁻¹) z k),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet z hz)),
    Matrix.one_mul, Matrix.mul_zero] at he
  exact (eq_neg_of_add_eq_zero_right he).trans
    (by simp only [Matrix.neg_mul, Matrix.mul_assoc])

theorem matrixWirtBar_inverse {H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ}
    {U : Set (ComplexVector n)} (hU : IsOpen U)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hdet : ∀ z ∈ U, (H z).det ≠ 0) {z : ComplexVector n} (hz : z ∈ U) (k : Fin n) :
    matrixWirtBar (fun w => (H w)⁻¹) z k =
      -(H z)⁻¹ * matrixWirtBar H z k * (H z)⁻¹ := by
  have hHD (i j : Fin r) : DifferentiableAt ℝ (fun w => H w i j) z :=
    ((hH i j).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hID (i j : Fin r) : DifferentiableAt ℝ (fun w => (H w)⁻¹ i j) z :=
    ((entrywise_matrix_inv_contDiffOn hH hdet i j).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hzero : matrixWirtBar H z k * (H z)⁻¹ +
      H z * matrixWirtBar (fun w => (H w)⁻¹) z k = 0 := by
    rw [← matrixWirtBar_mul H (fun w => (H w)⁻¹) z hHD hID k]
    ext i j
    have heq : (fun w => (H w * (H w)⁻¹) i j) =ᶠ[𝓝 z]
        (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) i j) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact congrArg (fun B : Matrix (Fin r) (Fin r) ℂ => B i j)
        (Matrix.mul_nonsing_inv (H w) (isUnit_iff_ne_zero.mpr (hdet w hw)))
    have hconst := (hasFDerivAt_const (𝕜 := ℝ) ((1 : Matrix (Fin r) (Fin r) ℂ) i j) z).fderiv
    simp only [matrixWirtBar, wirtBar, heq.fderiv_eq (𝕜 := ℝ), hconst,
      zero_apply, mul_zero, add_zero, Matrix.zero_apply]
  have he := congrArg (fun B => (H z)⁻¹ * B) hzero
  rw [Matrix.mul_add, ← Matrix.mul_assoc ((H z)⁻¹) (H z)
      (matrixWirtBar (fun w => (H w)⁻¹) z k),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet z hz)),
    Matrix.one_mul, Matrix.mul_zero] at he
  exact (eq_neg_of_add_eq_zero_right he).trans
    (by simp only [Matrix.neg_mul, Matrix.mul_assoc])

end Yau.Blueprint.V04Proof.WallErrorAux
