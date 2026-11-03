import Yau.Proofs.E01MatrixDerivative

/-! The actual nonsingular complex matrix inverse, differentiated entry by entry. -/

noncomputable section
open scoped Matrix Topology
open Filter

namespace Yau.NodeProofs.E01Aux
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_matrix_inverse_entries_differentiableAt
    {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun w => (A w)⁻¹ i j) z := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Matrix.adjugate_apply]
  apply ((complex_matrix_det_differentiableAt hA).inv hdet).mul
  apply complex_matrix_det_differentiableAt
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte]
    exact differentiableAt_const (𝕜 := ℝ) (x := z) _
  · simp only [hkj, ↓reduceIte]
    exact hA k l

theorem complexMatrixDerivative_inverse
    {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (v : E) :
    complexMatrixDerivative (fun w => (A w)⁻¹) z v =
      -((A z)⁻¹ * complexMatrixDerivative A z v * (A z)⁻¹) := by
  have hdcont : ContinuousAt (fun w => (A w).det) z :=
    (complex_matrix_det_differentiableAt hA).continuousAt
  have hn : ∀ᶠ w in 𝓝 z, (A w).det ≠ 0 := hdcont.eventually (eventually_ne_nhds hdet)
  have heq : (fun w => A w * (A w)⁻¹) =ᶠ[𝓝 z] (fun _ => (1 : Matrix ι ι ℂ)) := by
    filter_upwards [hn] with w hw
    exact Matrix.mul_nonsing_inv (A w) (isUnit_iff_ne_zero.mpr hw)
  have hprod := complexMatrixDerivative_congr heq v
  rw [complexMatrixDerivative_mul hA (complex_matrix_inverse_entries_differentiableAt hA hdet),
    complexMatrixDerivative_const] at hprod
  have hunit : IsUnit (A z).det := isUnit_iff_ne_zero.mpr hdet
  have hsum : (A z)⁻¹ * complexMatrixDerivative A z v * (A z)⁻¹ +
      complexMatrixDerivative (fun w => (A w)⁻¹) z v = 0 := by
    calc
      _ = (A z)⁻¹ * (complexMatrixDerivative A z v * (A z)⁻¹ +
          A z * complexMatrixDerivative (fun w => (A w)⁻¹) z v) := by
        rw [mul_add, ← mul_assoc (A z)⁻¹ (A z), Matrix.nonsing_inv_mul (A z) hunit, one_mul]
        simp only [mul_assoc]
      _ = 0 := by rw [hprod, mul_zero]
  exact eq_neg_of_add_eq_zero_right hsum

end Yau.NodeProofs.E01Aux
