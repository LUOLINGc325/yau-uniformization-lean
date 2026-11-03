import Yau.LeafProofs.L17SmallTranslationContraction

open Set Metric
open scoped Topology NNReal ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SmallTranslationAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L)

def cutoffInverse (θ y : E) : E :=
  if hθ : ‖θ‖ < smallTranslationRadius L then
    (cutoffInverseStep_contracting hχ hL hDf hθ y).fixedPoint (cutoffInverseStep χ θ y)
  else y

theorem cutoffInverse_step_fixed {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (y : E) :
    cutoffInverseStep χ θ y (cutoffInverse χ hχ L hL hDf θ y)=cutoffInverse χ hχ L hL hDf θ y := by
  simpa only [Function.IsFixedPt,cutoffInverse,dite_eq_left hθ] using
    (cutoffInverseStep_contracting hχ hL hDf hθ y).fixedPoint_isFixedPt

theorem cutoffTranslation_inverse {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (y : E) :
    cutoffTranslation χ θ (cutoffInverse χ hχ L hL hDf θ y)=y := by
  have h := cutoffInverse_step_fixed χ hχ L hL hDf hθ y
  exact (sub_eq_iff_eq_add.mp h).symm

theorem cutoffInverse_translation {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (z : E) :
    cutoffInverse χ hχ L hL hDf θ (cutoffTranslation χ θ z)=z := by
  have hz : Function.IsFixedPt (cutoffInverseStep χ θ (cutoffTranslation χ θ z)) z := by
    simp only [Function.IsFixedPt,cutoffInverseStep,cutoffTranslation,add_sub_cancel_right]
  have h := (cutoffInverseStep_contracting hχ hL hDf hθ (cutoffTranslation χ θ z)).fixedPoint_unique hz
  simpa only [cutoffInverse,dite_eq_left hθ] using h.symm

include hχ hL hDf in
theorem cutoffTranslation_injective {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) :
    Function.Injective (cutoffTranslation χ θ) :=
  Function.LeftInverse.injective (cutoffInverse_translation χ hχ L hL hDf hθ)

theorem cutoffInverse_lipschitz {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) :
    LipschitzWith 2 (cutoffInverse χ hχ L hL hDf θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro y w
  let u := cutoffInverse χ hχ L hL hDf θ y
  let v := cutoffInverse χ hχ L hL hDf θ w
  have hu : cutoffInverseStep χ θ y u=u := cutoffInverse_step_fixed χ hχ L hL hDf hθ y
  have hv : cutoffInverseStep χ θ w v=v := cutoffInverse_step_fixed χ hχ L hL hDf hθ w
  have hdiff := cutoffInverseStep_sub_norm_le hχ hL hDf hθ y u v
  have hid : u-v=(cutoffInverseStep χ θ y u-cutoffInverseStep χ θ y v)+(y-w) := by
    calc
      u-v=cutoffInverseStep χ θ y u-cutoffInverseStep χ θ w v :=
        (congrArg₂ (fun a b : E => a-b) hu hv).symm
      _ = (cutoffInverseStep χ θ y u-cutoffInverseStep χ θ y v)+(y-w) := by
        simp only [cutoffInverseStep]
        abel
  have hbound : ‖u-v‖ ≤ (1/4 : ℝ)*‖u-v‖+‖y-w‖ := by
    calc
      ‖u-v‖ = ‖(cutoffInverseStep χ θ y u-cutoffInverseStep χ θ y v)+(y-w)‖ := congrArg norm hid
      _ ≤ ‖cutoffInverseStep χ θ y u-cutoffInverseStep χ θ y v‖+‖y-w‖ := norm_add_le _ _
      _ ≤ (1/4 : ℝ)*‖u-v‖+‖y-w‖ := add_le_add hdiff le_rfl
  have hres : ‖u-v‖ ≤ (2 : ℝ)*‖y-w‖ := by linarith [norm_nonneg (u-v)]
  simpa only [dist_eq_norm,NNReal.coe_ofNat] using hres

def cutoffTranslationHomeomorph (θ : E) (hθ : ‖θ‖ < smallTranslationRadius L) : E ≃ₜ E where
  toEquiv := {
    toFun := cutoffTranslation χ θ
    invFun := cutoffInverse χ hχ L hL hDf θ
    left_inv := cutoffInverse_translation χ hχ L hL hDf hθ
    right_inv := cutoffTranslation_inverse χ hχ L hL hDf hθ }
  continuous_toFun := (cutoffTranslation_contDiff hχ θ).continuous
  continuous_invFun := (cutoffInverse_lipschitz χ hχ L hL hDf hθ).continuous

@[simp] theorem cutoffTranslationHomeomorph_apply (θ z : E) (hθ : ‖θ‖ < smallTranslationRadius L) :
    cutoffTranslationHomeomorph χ hχ L hL hDf θ hθ z=cutoffTranslation χ θ z := rfl

@[simp] theorem cutoffTranslationHomeomorph_symm_apply (θ y : E) (hθ : ‖θ‖ < smallTranslationRadius L) :
    (cutoffTranslationHomeomorph χ hχ L hL hDf θ hθ).symm y=cutoffInverse χ hχ L hL hDf θ y := rfl

@[simp] theorem cutoffInverse_zero_parameter (y : E) : cutoffInverse χ hχ L hL hDf 0 y=y := by
  simpa only [cutoffTranslation_zero_parameter] using cutoffInverse_translation χ hχ L hL hDf
    (θ := 0) (by simpa only [norm_zero] using smallTranslationRadius_pos hL) y

end Yau.LeafProofs.L17SmallTranslationAux
