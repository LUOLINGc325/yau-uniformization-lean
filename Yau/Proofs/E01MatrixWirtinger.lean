import Yau.Proofs.E01MatrixInverse

/-! First Wirtinger derivatives of the genuine complex inverse matrix. -/

noncomputable section
open scoped Matrix

namespace Yau.NodeProofs.E01Aux
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexMatrixWirt (A : E → Matrix ι ι ℂ) (z v : E) : Matrix ι ι ℂ :=
  fun i j => wirt (fun w => A w i j) z v

def complexMatrixWirtBar (A : E → Matrix ι ι ℂ) (z v : E) : Matrix ι ι ℂ :=
  fun i j => wirtBar (fun w => A w i j) z v

theorem complexMatrixWirt_eq (A : E → Matrix ι ι ℂ) (z v : E) :
    complexMatrixWirt A z v = (1 / 2 : ℂ) •
      (complexMatrixDerivative A z v - Complex.I • complexMatrixDerivative A z (Complex.I • v)) := rfl

theorem complexMatrixWirtBar_eq (A : E → Matrix ι ι ℂ) (z v : E) :
    complexMatrixWirtBar A z v = (1 / 2 : ℂ) •
      (complexMatrixDerivative A z v + Complex.I • complexMatrixDerivative A z (Complex.I • v)) := rfl

theorem complexMatrixWirt_inverse {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (v : E) :
    complexMatrixWirt (fun w => (A w)⁻¹) z v =
      -((A z)⁻¹ * complexMatrixWirt A z v * (A z)⁻¹) := by
  rw [complexMatrixWirt_eq, complexMatrixDerivative_inverse hA hdet v,
    complexMatrixDerivative_inverse hA hdet (Complex.I • v), complexMatrixWirt_eq]
  simp only [smul_sub, smul_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_neg, neg_mul]
  abel

theorem complexMatrixWirtBar_inverse {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (v : E) :
    complexMatrixWirtBar (fun w => (A w)⁻¹) z v =
      -((A z)⁻¹ * complexMatrixWirtBar A z v * (A z)⁻¹) := by
  rw [complexMatrixWirtBar_eq, complexMatrixDerivative_inverse hA hdet v,
    complexMatrixDerivative_inverse hA hdet (Complex.I • v), complexMatrixWirtBar_eq]
  simp only [smul_add, smul_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_neg, neg_mul]
  abel

end Yau.NodeProofs.E01Aux
