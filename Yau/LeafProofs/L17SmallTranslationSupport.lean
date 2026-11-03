import Yau.LeafProofs.L17SmallTranslationInverse

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SmallTranslationAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L)

theorem cutoffInverse_of_not_small {θ : E} (hθ : ¬ ‖θ‖ < smallTranslationRadius L) (y : E) :
    cutoffInverse χ hχ L hL hDf θ y=y := by
  simp only [cutoffInverse,dite_eq_right hθ]

theorem cutoffInverse_fixed_of_zero {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L)
    {y : E} (hy : χ y=0) : cutoffInverse χ hχ L hL hDf θ y=y := by
  simpa only [cutoffTranslation_fixed_of_zero χ θ hy] using
    cutoffInverse_translation χ hχ L hL hDf hθ y

include hχ hL hDf in
theorem cutoffTranslation_mapsTo {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (S : Set E)
    (hS : ∀ z, z ∉ S → χ z=0) : MapsTo (cutoffTranslation χ θ) S S := by
  intro z hz
  by_contra hn
  have hfix := cutoffTranslation_fixed_of_zero χ θ (hS _ hn)
  have heq : cutoffTranslation χ θ z=z := cutoffTranslation_injective χ hχ L hL hDf hθ hfix
  exact hn (by rwa [heq])

theorem cutoffInverse_mapsTo {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (S : Set E)
    (hS : ∀ z, z ∉ S → χ z=0) : MapsTo (cutoffInverse χ hχ L hL hDf θ) S S := by
  intro y hy
  by_contra hn
  have hfix := cutoffTranslation_fixed_of_zero χ θ (hS _ hn)
  have heq : cutoffInverse χ hχ L hL hDf θ y=y :=
    hfix.symm.trans (cutoffTranslation_inverse χ hχ L hL hDf hθ y)
  exact hn (by rwa [heq])

end Yau.LeafProofs.L17SmallTranslationAux
