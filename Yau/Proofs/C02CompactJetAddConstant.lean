import Yau.Proofs.C02CompactJets

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compactJetNorm_const_add_succ (C : F) (f : E → F) (hf : ContDiff ℝ ∞ f) (m : ℕ) (ρ : ℝ) :
    compactJetNorm (fun y => C + f y) (contDiff_const.add hf) (m + 1) ρ = compactJetNorm f hf (m + 1) ρ := by
  have he (x : E) : ‖iteratedFDeriv ℝ (m + 1) (fun y => C + f y) x‖ =
      ‖iteratedFDeriv ℝ (m + 1) f x‖ := by
    rw [fun_iteratedFDeriv_add_apply (contDiffAt_const : ContDiffAt ℝ (m + 1) (fun _ : E => C) x)
      (hf.contDiffAt.of_le (by simp)), iteratedFDeriv_succ_const]
    simp
  apply le_antisymm
  · apply compactJetNorm_le _ _ _ _ _ (compactJetNorm_nonneg f hf (m + 1) ρ)
    intro x hx
    rw [he]
    exact norm_iteratedFDeriv_le_compactJetNorm f hf (m + 1) ρ hx
  · apply compactJetNorm_le _ _ _ _ _ (compactJetNorm_nonneg _ _ (m + 1) ρ)
    intro x hx
    rw [← he]
    exact norm_iteratedFDeriv_le_compactJetNorm _ _ (m + 1) ρ hx

end Yau.Blueprint.C02Proof
