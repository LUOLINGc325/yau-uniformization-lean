import Yau.LeafProofs.L17TransitionFrames

/-! The pointwise Koszul calculation for a genuine coordinate change. -/

noncomputable section

namespace Yau.LeafProofs.L17Aux

theorem koszul_coordinate_change
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B₁ : E →L[ℝ] E →L[ℝ] ℝ) (B₂ : F →L[ℝ] F →L[ℝ] ℝ)
    (D₁ : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (D₂ : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (Γ₁ : E →L[ℝ] E →L[ℝ] E) (Γ₂ : F →L[ℝ] F →L[ℝ] F)
    (J : E →L[ℝ] F) (S : E →L[ℝ] E →L[ℝ] F)
    (hB₂ : ∀ u v, B₂ u v = B₂ v u)
    (hnondegenerate : ∀ u, (∀ v, B₂ u v = 0) → u = 0)
    (hJ : Function.Surjective J) (hS : ∀ u v, S u v = S v u)
    (hpullback : ∀ u v, B₁ u v = B₂ (J u) (J v))
    (hderivative : ∀ u v w, D₁ u v w =
      D₂ (J u) (J v) (J w) + B₂ (S u v) (J w) + B₂ (J v) (S u w))
    (hΓ₁ : ∀ u v w, B₁ (Γ₁ u v) w =
      (D₁ u v w + D₁ v u w - D₁ w u v) / 2)
    (hΓ₂ : ∀ u v w, B₂ (Γ₂ u v) w =
      (D₂ u v w + D₂ v u w - D₂ w u v) / 2)
    (u v : E) : J (Γ₁ u v) = S u v + Γ₂ (J u) (J v) := by
  apply sub_eq_zero.mp
  apply hnondegenerate
  intro x
  obtain ⟨w, rfl⟩ := hJ x
  have hfirst := hΓ₁ u v w
  rw [hpullback, hderivative, hderivative, hderivative,
    hS v u, hS w u, hS w v, hB₂ (S u w) (J v)] at hfirst
  have hsecond := hΓ₂ (J u) (J v) (J w)
  simp only [map_sub, sub_apply, map_add, add_apply]
  linarith

end Yau.LeafProofs.L17Aux
