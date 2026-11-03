import Yau.Proofs.C02CompactJets

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem compactJetNorm_congr {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (heq : f = g) (m : ℕ) (ρ : ℝ) : compactJetNorm f hf m ρ = compactJetNorm g hg m ρ := by
  subst g
  rfl

theorem compactJetNorm_isometry (L : F ≃ₗᵢ[ℝ] G) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (ρ : ℝ) :
    compactJetNorm (L ∘ f) (L.toContinuousLinearEquiv.contDiff.comp hf) m ρ = compactJetNorm f hf m ρ := by
  apply le_antisymm
  · apply compactJetNorm_le _ _ _ _ _ (compactJetNorm_nonneg f hf m ρ)
    intro x hx
    rw [L.norm_iteratedFDeriv_comp_left f x m]
    exact norm_iteratedFDeriv_le_compactJetNorm f hf m ρ hx
  · apply compactJetNorm_le _ _ _ _ _ (compactJetNorm_nonneg _ _ m ρ)
    intro x hx
    rw [← L.norm_iteratedFDeriv_comp_left f x m]
    exact norm_iteratedFDeriv_le_compactJetNorm _ _ m ρ hx

end Yau.Blueprint.C02Proof
