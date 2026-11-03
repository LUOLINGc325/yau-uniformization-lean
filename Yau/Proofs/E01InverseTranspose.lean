import Yau.Proofs.E01MixedInverse

/-! Actual inverse-transpose Wirtinger formulas, retaining every noncommutative multiplication order. -/

noncomputable section
open scoped Matrix Topology
open Filter

namespace Yau.NodeProofs.E01Aux
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexMatrixWirt_invTranspose {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (v : E) :
    complexMatrixWirt (fun w => ((A w)⁻¹)ᵀ) z v =
      -((A z)⁻¹)ᵀ * (complexMatrixWirt A z v)ᵀ * ((A z)⁻¹)ᵀ := by
  have htranspose : complexMatrixWirt (fun w => ((A w)⁻¹)ᵀ) z v =
      (complexMatrixWirt (fun w => (A w)⁻¹) z v)ᵀ := rfl
  rw [htranspose, complexMatrixWirt_inverse hA hdet]
  simp only [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.mul_assoc, neg_mul]

theorem complexMatrixWirtBar_invTranspose {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (v : E) :
    complexMatrixWirtBar (fun w => ((A w)⁻¹)ᵀ) z v =
      -((A z)⁻¹)ᵀ * (complexMatrixWirtBar A z v)ᵀ * ((A z)⁻¹)ᵀ := by
  have htranspose : complexMatrixWirtBar (fun w => ((A w)⁻¹)ᵀ) z v =
      (complexMatrixWirtBar (fun w => (A w)⁻¹) z v)ᵀ := rfl
  rw [htranspose, complexMatrixWirtBar_inverse hA hdet]
  simp only [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.mul_assoc, neg_mul]

theorem complexMatrix_mixed_invTranspose {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hlocal : ∀ᶠ y in 𝓝 z, ∀ i j, DifferentiableAt ℝ (fun w => A w i j) y)
    (hdet : (A z).det ≠ 0) (a b : E)
    (hbar : ∀ i j, DifferentiableAt ℝ (fun w => complexMatrixWirtBar A w b i j) z) :
    complexMatrixWirt (fun w => complexMatrixWirtBar (fun y => ((A y)⁻¹)ᵀ) w b) z a =
      ((A z)⁻¹)ᵀ * (complexMatrixWirtBar A z b)ᵀ * ((A z)⁻¹)ᵀ *
          (complexMatrixWirt A z a)ᵀ * ((A z)⁻¹)ᵀ +
      ((A z)⁻¹)ᵀ * (complexMatrixWirt A z a)ᵀ * ((A z)⁻¹)ᵀ *
          (complexMatrixWirtBar A z b)ᵀ * ((A z)⁻¹)ᵀ -
      ((A z)⁻¹)ᵀ * (complexMatrixWirt (fun w => complexMatrixWirtBar A w b) z a)ᵀ * ((A z)⁻¹)ᵀ := by
  have htranspose : complexMatrixWirt (fun w => complexMatrixWirtBar (fun y => ((A y)⁻¹)ᵀ) w b) z a =
      (complexMatrixWirt (fun w => complexMatrixWirtBar (fun y => (A y)⁻¹) w b) z a)ᵀ := rfl
  rw [htranspose, complexMatrix_mixed_inverse hA hlocal hdet a b hbar]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.mul_assoc]

end Yau.NodeProofs.E01Aux
