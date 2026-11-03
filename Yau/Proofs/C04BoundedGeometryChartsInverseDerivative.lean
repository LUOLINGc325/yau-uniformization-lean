import Yau.Proofs.C04BoundedGeometryChartsInverse

/-! The uniform first derivative estimate for the same fixed inverse. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04ChartsAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverse_norm_le_of_close_id (D : E ≃L[ℝ] E)
    (hclose : ‖(D : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) :
    ‖(D.symm : E →L[ℝ] E)‖ ≤ (4 / 3 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound (D.symm : E →L[ℝ] E) (by norm_num)
  intro v
  change ‖D.symm v‖ ≤ (4 / 3 : ℝ) * ‖v‖
  have hh := ((D : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E).le_opNorm (D.symm v)
  have herror : ‖v - D.symm v‖ ≤ (1 / 4 : ℝ) * ‖D.symm v‖ := by
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.id_apply] using
      hh.trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  have htri := norm_sub_norm_le (D.symm v) v
  rw [norm_sub_rev] at htri
  linarith

variable [CompleteSpace E]

theorem inverse_fderiv_norm_le (e : OpenPartialHomeomorph E E)
    (hF : ContDiff ℝ ∞ (e : E → E))
    (hclose : ∀ x ∈ e.source,
      ‖fderiv ℝ e x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ))
    {w : E} (hw : w ∈ e.target) :
    ‖fderiv ℝ e.symm w‖ ≤ (4 / 3 : ℝ) := by
  have hx := e.map_target hw
  obtain ⟨D, hD⟩ := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one
    (fderiv ℝ e (e.symm w)) (lt_of_le_of_lt (hclose _ hx) (by norm_num))
  have hd : HasFDerivAt e (D : E →L[ℝ] E) (e.symm w) := by
    rw [hD]
    exact (hF.differentiable (by simp) _).hasFDerivAt
  rw [(e.hasFDerivAt_symm hw hd).fderiv]
  apply inverse_norm_le_of_close_id
  rw [hD]
  exact hclose _ hx

end Yau.Proofs.C04ChartsAux
