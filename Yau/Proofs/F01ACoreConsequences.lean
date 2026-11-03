import Yau.Proofs.F01ANativeGlobalKahlerCore
import Yau.Proofs.F01ClosedTimeBounds

/-! Sign consequences retain the exact same global potential and logdet. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem localizedFlowCore_logdet_nonpositive
    {X : KahlerManifold n} {h : Flow X} {U P ρ : STF X}
    (hc : LocalizedFlowCore X h U P ρ) : ∀ x t, 0 ≤ t → P x t ≤ 0 := by
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, hρ, _⟩
  intro x t ht
  have hs := hρ x t ht
  rw [hs.1] at hs
  exact neg_nonneg.mp hs.2

theorem localizedFlowCore_potential_nonpositive
    {X : KahlerManifold n} {h : Flow X} {U P ρ : STF X}
    (hc : LocalizedFlowCore X h U P ρ) : ∀ x t, 0 ≤ t → U x t ≤ 0 := by
  have hP := localizedFlowCore_logdet_nonpositive hc
  rcases hc with ⟨_, _, _, _, _, _, hU0, hUt, _, _, _⟩
  intro x t ht
  have hsub : Icc (0 : ℝ) t ⊆ Ici 0 := fun _ hs => hs.1
  exact nonpositive_of_closed_nonpositive_derivative ht (hU0 x)
    (fun s hs => (hUt x s hs.1).mono hsub) (fun s hs => hP x s hs.1) t ⟨ht, le_rfl⟩

end Yau.NodeProofs.F01Aux
