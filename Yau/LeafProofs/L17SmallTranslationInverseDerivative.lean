import Yau.LeafProofs.L17SmallTranslationSmooth

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SmallTranslationAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L)

theorem cutoffInverse_hasFDerivAt {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (y : E) :
    HasFDerivAt (cutoffInverse χ hχ L hL hDf θ)
      (cutoffJacobianEquiv χ L hL hDf θ hθ (cutoffInverse χ hχ L hL hDf θ y)).symm.toContinuousLinearMap y := by
  let z := cutoffInverse χ hχ L hL hDf θ y
  let J := cutoffJacobianEquiv χ L hL hDf θ hθ z
  have hJac : HasFDerivAt (cutoffTranslation χ θ) J.toContinuousLinearMap z := by
    rw [cutoffJacobianEquiv_toCLM]
    exact cutoffTranslation_hasFDerivAt hχ θ z
  have hStrict := (cutoffTranslation_contDiff hχ θ).contDiffAt.hasStrictFDerivAt'
    (f' := J) hJac (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hInv := hStrict.to_local_left_inverse
    (Filter.Eventually.of_forall (cutoffInverse_translation χ hχ L hL hDf hθ))
  have hImage : cutoffTranslation χ θ z=y := cutoffTranslation_inverse χ hχ L hL hDf hθ y
  rw [hImage] at hInv
  exact hInv.hasFDerivAt

theorem cutoffInverse_fderiv {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (y : E) :
    fderiv ℝ (cutoffInverse χ hχ L hL hDf θ) y=
      (cutoffJacobianEquiv χ L hL hDf θ hθ (cutoffInverse χ hχ L hL hDf θ y)).symm.toContinuousLinearMap :=
  (cutoffInverse_hasFDerivAt χ hχ L hL hDf hθ y).fderiv

theorem cutoffInverse_fderiv_norm_le {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (y : E) :
    ‖fderiv ℝ (cutoffInverse χ hχ L hL hDf θ) y‖ ≤ 2 := by
  rw [cutoffInverse_fderiv χ hχ L hL hDf hθ y]
  exact cutoffJacobianEquiv_symm_norm_le χ L hL hDf θ hθ _

end Yau.LeafProofs.L17SmallTranslationAux
