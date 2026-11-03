import Yau.Proofs.F05NormalProduct

/-! The real normal product contains genuine open tangential buffers times
closed inward intervals, with an explicit spatial margin. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_normal_product_buffer (j : RIdx n) {x : Space n} {R : ℝ}
    (hFace : realCoord x j = 0) (hx : ‖x‖ < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Metric.ball (F05TangentPoint j x hFace) δ ×ˢ Icc 0 δ,
      ‖F05NormalMergeMap j q‖ < R ∧ realCoord (F05NormalMergeMap j q) j ≤ 0 := by
  let δ : ℝ := (R-‖x‖)/4
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  refine ⟨δ,hδ,?_⟩
  intro q hq
  have hDistance : ‖q.1.val-x‖ < δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,← Submodule.norm_coe,Submodule.coe_sub,F05TangentPoint] using hq.1
  have hNorm : ‖q.1.val‖ ≤ ‖q.1.val-x‖+‖x‖ := norm_le_norm_sub_add _ _
  have hMerge : ‖F05NormalMergeMap j q‖ ≤ ‖q.1.val‖+q.2 := by
    change ‖q.1.val-q.2 • realVec j‖ ≤ _
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq.2.1,realVec_norm,mul_one] using
      norm_sub_le q.1.val (q.2 • realVec j)
  refine ⟨?_,?_⟩
  · dsimp only [δ] at hDistance hq
    linarith [hq.2.2]
  · rw [F05_normal_product_inward]
    exact neg_nonpos.mpr hq.2.1

theorem F05_normal_product_face (j : RIdx n) {x : Space n} (hx : realCoord x j = 0) :
    F05NormalProduct j x = (F05TangentPoint j x hx,0) := by
  have hxL : realCoordLinear j x = 0 := by simpa only [realCoordLinear_apply] using hx
  apply Prod.ext
  · apply Subtype.ext
    change x-realCoordLinear j x • realVec j = x
    simp only [hxL,zero_smul,sub_zero]
  · change -realCoordLinear j x = 0
    simp only [hxL,neg_zero]

end Yau.Proofs.F05Aux
