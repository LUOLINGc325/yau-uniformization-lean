import Yau.Proofs.C04BoundedGeometryChartsInverseComplexIntertwining

/-! Uniform singular-value bounds for the same normalized inverse parameter. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

section RealSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem close_identity_norm_bounds (D : E →L[ℝ] E)
    (hD : ‖D - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) (v : E) :
    (3 / 4 : ℝ) * ‖v‖ ≤ ‖D v‖ ∧ ‖D v‖ ≤ (5 / 4 : ℝ) * ‖v‖ := by
  have he : ‖D v - v‖ ≤ (1 / 4 : ℝ) * ‖v‖ := by
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] using
      ((D - ContinuousLinearMap.id ℝ E).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg v))
  have h₁ := norm_sub_norm_le v (D v)
  rw [norm_sub_rev] at h₁
  have h₂ := norm_sub_norm_le (D v) v
  constructor <;> linarith

theorem equiv_inverse_norm_bounds (D : E ≃L[ℝ] E)
    (hD : ‖(D : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) (v : E) :
    (4 / 5 : ℝ) * ‖v‖ ≤ ‖D.symm v‖ ∧ ‖D.symm v‖ ≤ (4 / 3 : ℝ) * ‖v‖ := by
  have h := close_identity_norm_bounds (D : E →L[ℝ] E) hD (D.symm v)
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h
  constructor <;> linarith [h.1, h.2]

end RealSpace
variable {n : ℕ}

theorem normalizedInverseParameter_deriv_norm_bounds
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (F : ComplexVector n → ComplexVector n) (he : (e : ComplexVector n → ComplexVector n) = F)
    (hF : ContDiff ℝ ∞ F) (L : ComplexVector n →L[ℝ] ComplexVector n)
    (hL : ‖L - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ))
    {d : ℝ} (hd : d ≠ 0) (z : ComplexVector n) (hw : d⁻¹ • L z ∈ e.target)
    (hD : ‖fderiv ℝ F (e.symm (d⁻¹ • L z)) - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ))
    (v : ComplexVector n) :
    (3 / 5 : ℝ) * ‖v‖ ≤ ‖fderiv ℝ (normalizedInverseParameter e L d) z v‖ ∧
      ‖fderiv ℝ (normalizedInverseParameter e L d) z v‖ ≤ (5 / 3 : ℝ) * ‖v‖ := by
  obtain ⟨D, hDE⟩ := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one
    (fderiv ℝ F (e.symm (d⁻¹ • L z))) (hD.trans_lt (by norm_num))
  have hDF : HasFDerivAt e (D : ComplexVector n →L[ℝ] ComplexVector n)
      (e.symm (d⁻¹ • L z)) := by
    rw [he, hDE]
    exact (hF.differentiable (by simp) _).hasFDerivAt
  have hψ := e.hasFDerivAt_symm hw hDF
  rw [normalizedInverseParameter_fderiv e L hd z hψ.differentiableAt, hψ.fderiv,
    ContinuousLinearMap.comp_apply]
  have hDi : ‖(D : ComplexVector n →L[ℝ] ComplexVector n) - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤
      (1 / 4 : ℝ) := by rw [hDE]; exact hD
  have hi := equiv_inverse_norm_bounds D hDi (L v)
  have hl := close_identity_norm_bounds L hL v
  simp only [ContinuousLinearEquiv.coe_coe] at ⊢
  constructor <;> linarith [hi.1, hi.2, hl.1, hl.2]

theorem normal_gram_composition_norm_bounds
    (A D : ComplexVector n →L[ℝ] ComplexVector n)
    (hA : ‖A - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ))
    (hD : ∀ v, (3 / 5 : ℝ) * ‖v‖ ≤ ‖D v‖ ∧ ‖D v‖ ≤ (5 / 3 : ℝ) * ‖v‖)
    (v : ComplexVector n) :
    (1 / 4 : ℝ) * ‖v‖ ≤ ‖A (D v)‖ ∧ ‖A (D v)‖ ≤ 4 * ‖v‖ := by
  have ha := close_identity_norm_bounds A hA (D v)
  have hd := hD v
  constructor <;> linarith [ha.1, ha.2, hd.1, hd.2, norm_nonneg v]

end Yau.Proofs.C04ChartsAux
