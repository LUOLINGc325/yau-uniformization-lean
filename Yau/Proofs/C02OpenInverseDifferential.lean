import Yau.Proofs.C02OperatorSmoothInverse

/-! The inverse derivative and its numerical bound belong to the actual
open partial inverse, without a separately supplied inverse operator. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem openPartialHomeomorph_fderiv_symm
    (e : OpenPartialHomeomorph E E) (y : E) (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ (e : E → E) (e.symm y))
    (hInv : (fderiv ℝ (e : E → E) (e.symm y)).IsInvertible) :
    fderiv ℝ e.symm y = (fderiv ℝ (e : E → E) (e.symm y)).inverse := by
  obtain ⟨L, hL⟩ := hInv
  have hd : HasFDerivAt (e : E → E) (L : E →L[ℝ] E) (e.symm y) := by
    rw [hL]
    exact hf.hasFDerivAt
  rw [← hL, ContinuousLinearMap.inverse_equiv]
  exact (e.hasFDerivAt_symm hy hd).fderiv

theorem openPartialHomeomorph_inverse_derivative_norm_le_two
    (e : OpenPartialHomeomorph E E) (hf : Differentiable ℝ (e : E → E))
    (hClose : ∀ x ∈ e.source,
      ‖fderiv ℝ (e : E → E) x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4)
    (y : E) (hy : y ∈ e.target) : ‖fderiv ℝ e.symm y‖ ≤ 2 := by
  have hD := hClose (e.symm y) (e.map_target hy)
  rw [openPartialHomeomorph_fderiv_symm e y hy (hf _) (isInvertible_of_close_identity _ hD)]
  exact norm_actual_inverse_of_close_identity _ hD

end Yau.Blueprint.C02Proof
