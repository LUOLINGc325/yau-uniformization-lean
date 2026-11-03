import Yau.Proofs.V04WallErrorInverseSpatial
import Yau.Proofs.V03LeviCalculus

/-! Jacobi's identity for the actual complex determinant. The multilinear
calculus below follows the already proved L07 determinant argument and
keeps the scalar and transpose conventions of the current metric. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.G01Aux

variable {n r : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def determinantMultilinear (r : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin r => Fin r → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

theorem determinantMultilinear_apply (A : Matrix (Fin r) (Fin r) ℂ) :
    determinantMultilinear r A = A.det := rfl

theorem determinant_linearDeriv (A D : Matrix (Fin r) (Fin r) ℂ) :
    (determinantMultilinear r).linearDeriv A D =
      ∑ i, (A.updateRow i (D i)).det := by
  exact (determinantMultilinear r).linearDeriv_apply A D

theorem determinant_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) :
    fderiv ℝ (fun w => (H w).det) z v =
      ∑ i, ((H z).updateRow i (fderiv ℝ H z v i)).det := by
  have hd := (((determinantMultilinear r).hasFDerivAt (H z)).restrictScalars ℝ).comp
    z hH.hasFDerivAt
  calc
    _ = (determinantMultilinear r).linearDeriv (H z) (fderiv ℝ H z v) :=
      congrArg (fun f : X →L[ℝ] ℂ => f v) hd.fderiv
    _ = _ := determinant_linearDeriv (H z) (fderiv ℝ H z v)

theorem determinant_updateRow_of_invertible (A D : Matrix (Fin r) (Fin r) ℂ)
    (hA : IsUnit A.det) (i : Fin r) :
    (A.updateRow i (D i)).det = (D * A⁻¹) i i * A.det := by
  have heq : ∑ j, (D * A⁻¹) i j • A j = D i := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change ((D * A⁻¹) * A) i k = D i k
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  rw [← heq, Matrix.det_updateRow_sum, smul_eq_mul]

theorem determinant_fderiv_trace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) :
    fderiv ℝ (fun w => (H w).det) z v =
      (H z).det * Matrix.trace ((H z)⁻¹ * fderiv ℝ H z v) := by
  rw [determinant_fderiv H z v hH]
  simp_rw [determinant_updateRow_of_invertible (H z) _ hdet]
  rw [← Finset.sum_mul]
  change Matrix.trace (fderiv ℝ H z v * (H z)⁻¹) * (H z).det = _
  rw [Matrix.trace_mul_comm, mul_comm]

theorem matrix_fderiv_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (i j : Fin r) :
    fderiv ℝ (fun w => H w i j) z v = fderiv ℝ H z v i j := by
  have hrow : DifferentiableAt ℝ (fun w => H w i) z :=
    (differentiableAt_pi.mp hH) i
  have h₁ := congrArg (fun L : X →L[ℝ] ℂ => L v) (fderiv_apply hrow j)
  have h₂ := congrArg (fun L : X →L[ℝ] (Fin r → ℂ) => L v j) (fderiv_apply hH i)
  exact h₁.trans h₂

theorem matrix_wirt_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) :
    (Matrix.of fun i j => wirt (fun w => H w i j) z v) =
      (1 / 2 : ℂ) • (fderiv ℝ H z v - Complex.I • fderiv ℝ H z (Complex.I • v)) := by
  ext i j
  simp only [wirt, matrix_fderiv_entry H z _ hH, Matrix.of_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]

theorem determinant_wirt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) :
    wirt (fun w => (H w).det) z v =
      (H z).det * Matrix.trace ((H z)⁻¹ *
        (Matrix.of fun i j => wirt (fun w => H w i j) z v)) := by
  rw [matrix_wirt_eq H z v hH]
  simp only [wirt, determinant_fderiv_trace H z _ hH hdet, Matrix.mul_smul,
    Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  ring

theorem determinant_wirtBar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : E → Matrix (Fin r) (Fin r) ℂ) (z v : E)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) :
    wirtBar (fun w => (H w).det) z v =
      (H z).det * Matrix.trace ((H z)⁻¹ *
        (Matrix.of fun i j => wirtBar (fun w => H w i j) z v)) := by
  have hmatrix : (Matrix.of fun i j => wirtBar (fun w => H w i j) z v) =
      (1 / 2 : ℂ) • (fderiv ℝ H z v + Complex.I • fderiv ℝ H z (Complex.I • v)) := by
    ext i j
    simp only [wirtBar, matrix_fderiv_entry H z _ hH, Matrix.of_apply,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  rw [hmatrix]
  simp only [wirtBar, determinant_fderiv_trace H z _ hH hdet, Matrix.mul_smul,
    Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  ring

theorem matrix_jacobi_wirtBar_logdet
    {H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ} {U : Set (ComplexVector n)}
    (hU : IsOpen U) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hpos : ∀ z ∈ U, (H z).PosDef) {z : ComplexVector n} (hz : z ∈ U) (k : Fin n) :
    wirtBar (fun w => (Real.log (H w).det.re : ℂ)) z (stdVec k) =
      Matrix.trace ((H z)⁻¹ * matrixWirtBar H z k) := by
  have hHD : DifferentiableAt ℝ H z := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact ((hH i j).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hD : DifferentiableAt ℝ (fun w => (H w).det) z :=
    ((entrywise_matrix_det_contDiffOn hH).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hDR : DifferentiableAt ℝ (fun w => (H w).det.re) z :=
    Complex.reCLM.differentiableAt.comp z hD
  have hdetR : (H z).det.re ≠ 0 := ne_of_gt (Complex.pos_iff.mp (hpos z hz).det_pos).1
  have hreal (w : ComplexVector n) (hw : w ∈ U) :
      (H w).det = ((H w).det.re : ℂ) := by
    change (H w).det = ((RCLike.re (H w).det : ℝ) : ℂ)
    rw [(hpos w hw).isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
    rfl
  have heq : (fun w => ((H w).det.re : ℂ)) =ᶠ[𝓝 z] (fun w => (H w).det) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hreal w hw).symm
  have hw : wirtBar (fun w => ((H w).det.re : ℂ)) z (stdVec k) =
      wirtBar (fun w => (H w).det) z (stdVec k) := by
    simp only [wirtBar, heq.fderiv_eq (𝕜 := ℝ)]
  have hcoef : ((H z).det.re : ℂ)⁻¹ * (H z).det = 1 := by
    calc
      ((H z).det.re : ℂ)⁻¹ * (H z).det = ((H z).det.re : ℂ)⁻¹ * ((H z).det.re : ℂ) :=
        congrArg (fun v : ℂ => ((H z).det.re : ℂ)⁻¹ * v) (hreal z hz)
      _ = 1 := inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hdetR)
  rw [wirtBar_log_real hDR hdetR, hw, determinant_wirtBar H z (stdVec k) hHD
    ((hpos z hz).isUnit.map Matrix.detMonoidHom), ← mul_assoc, hcoef, one_mul]
  rfl

end Yau.Blueprint.V04Proof.WallErrorAux
