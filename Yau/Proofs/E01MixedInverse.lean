import Yau.Proofs.E01MatrixWirtProduct

/-! The full, noncommutative mixed Wirtinger derivative of the actual inverse matrix. -/

noncomputable section
open scoped Matrix Topology
open Filter

namespace Yau.NodeProofs.E01Aux
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexMatrix_mixed_inverse {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hlocal : ∀ᶠ y in 𝓝 z, ∀ i j, DifferentiableAt ℝ (fun w => A w i j) y)
    (hdet : (A z).det ≠ 0) (a b : E)
    (hbar : ∀ i j, DifferentiableAt ℝ (fun w => complexMatrixWirtBar A w b i j) z) :
    complexMatrixWirt (fun w => complexMatrixWirtBar (fun y => (A y)⁻¹) w b) z a =
      (A z)⁻¹ * complexMatrixWirt A z a * (A z)⁻¹ * complexMatrixWirtBar A z b * (A z)⁻¹ +
      (A z)⁻¹ * complexMatrixWirtBar A z b * (A z)⁻¹ * complexMatrixWirt A z a * (A z)⁻¹ -
      (A z)⁻¹ * complexMatrixWirt (fun w => complexMatrixWirtBar A w b) z a * (A z)⁻¹ := by
  have hndet : ∀ᶠ y in 𝓝 z, (A y).det ≠ 0 :=
    (complex_matrix_det_differentiableAt hA).continuousAt.eventually (eventually_ne_nhds hdet)
  have heq : (fun w => complexMatrixWirtBar (fun y => (A y)⁻¹) w b) =ᶠ[𝓝 z]
      (fun w => -((A w)⁻¹ * complexMatrixWirtBar A w b * (A w)⁻¹)) := by
    filter_upwards [hlocal, hndet] with y hy hd
    exact complexMatrixWirtBar_inverse hy hd b
  rw [complexMatrixWirt_congr heq, complexMatrixWirt_neg]
  have hinv := complex_matrix_inverse_entries_differentiableAt hA hdet
  rw [complexMatrixWirt_mul (complex_matrix_entries_differentiable_mul hinv hbar) hinv,
    complexMatrixWirt_mul hinv hbar]
  simp only [complexMatrixWirt_inverse hA hdet a]
  noncomm_ring

end Yau.NodeProofs.E01Aux
