import Yau.Proofs.E01MatrixWirtinger

/-! Entrywise Wirtinger product and locality rules, with actual real differentiability. -/

noncomputable section
open scoped Matrix Topology
open Filter

namespace Yau.NodeProofs.E01Aux
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_matrix_entries_differentiable_mul {A B : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) :
    ∀ i j, DifferentiableAt ℝ (fun w => (A w * B w) i j) z := by
  intro i j
  exact DifferentiableAt.fun_sum (fun k _ => (hA i k).mul (hB k j))

theorem complexMatrixWirt_mul {A B : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (v : E) :
    complexMatrixWirt (fun w => A w * B w) z v =
      complexMatrixWirt A z v * B z + A z * complexMatrixWirt B z v := by
  rw [complexMatrixWirt_eq, complexMatrixDerivative_mul hA hB v,
    complexMatrixDerivative_mul hA hB (Complex.I • v), complexMatrixWirt_eq, complexMatrixWirt_eq]
  simp only [smul_add, smul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub]
  abel

theorem complexMatrixWirtBar_mul {A B : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (v : E) :
    complexMatrixWirtBar (fun w => A w * B w) z v =
      complexMatrixWirtBar A z v * B z + A z * complexMatrixWirtBar B z v := by
  rw [complexMatrixWirtBar_eq, complexMatrixDerivative_mul hA hB v,
    complexMatrixDerivative_mul hA hB (Complex.I • v), complexMatrixWirtBar_eq, complexMatrixWirtBar_eq]
  simp only [smul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  abel

theorem complexMatrixWirt_congr {A B : E → Matrix ι ι ℂ} {z : E}
    (heq : A =ᶠ[𝓝 z] B) (v : E) :
    complexMatrixWirt A z v = complexMatrixWirt B z v := by
  rw [complexMatrixWirt_eq, complexMatrixWirt_eq,
    complexMatrixDerivative_congr heq v, complexMatrixDerivative_congr heq (Complex.I • v)]

theorem complexMatrixWirt_neg (A : E → Matrix ι ι ℂ) (z v : E) :
    complexMatrixWirt (fun w => -A w) z v = -complexMatrixWirt A z v := by
  ext i j
  simp only [complexMatrixWirt, Matrix.neg_apply, wirt, fderiv_fun_neg,
    ContinuousLinearMap.neg_apply, neg_mul]
  ring

end Yau.NodeProofs.E01Aux
