import Yau.LeafProofs.L17KoszulChange

/-! Differentiating a metric pullback, with the actual second derivative. -/

noncomputable section

namespace Yau.LeafProofs.L17Aux

theorem fderiv_bilinear_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : F → F →L[ℝ] F →L[ℝ] ℝ} {T : E → F} {z : E}
    (hB : DifferentiableAt ℝ B (T z)) (hT : DifferentiableAt ℝ T z)
    (hD : DifferentiableAt ℝ (fderiv ℝ T) z) (u v w : E) :
    fderiv ℝ (fun x => B (T x) (fderiv ℝ T x v) (fderiv ℝ T x w)) z u =
      (fderiv ℝ B (T z) (fderiv ℝ T z u)) (fderiv ℝ T z v) (fderiv ℝ T z w) +
        B (T z) ((fderiv ℝ (fderiv ℝ T) z u) v) (fderiv ℝ T z w) +
        B (T z) (fderiv ℝ T z v) ((fderiv ℝ (fderiv ℝ T) z u) w) := by
  have hc : DifferentiableAt ℝ (fun x => B (T x)) z := by
    exact DifferentiableAt.comp (g := B) (f := T) z hB hT
  have hv := hD.clm_apply (differentiableAt_const (c := v))
  have hw := hD.clm_apply (differentiableAt_const (c := w))
  rw [fderiv_clm_apply (hc.clm_apply hv) hw, fderiv_clm_apply hc hv,
    fderiv_clm_apply hD (differentiableAt_const (c := v)),
    fderiv_clm_apply hD (differentiableAt_const (c := w))]
  have hcomp : fderiv ℝ (fun x => B (T x)) z =
      (fderiv ℝ B (T z)).comp (fderiv ℝ T z) := by
    exact fderiv_comp (g := B) (f := T) z hB hT
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply, fderiv_const_apply, zero_apply, map_zero, zero_add]
  ring

end Yau.LeafProofs.L17Aux
