import Yau.Proofs.F01AFinalAssembly
import Yau.Proofs.P04
import Yau.Proofs.P07

/-! Conditional application at the original F01 contract, with its exact
dimension and original-manifold quantifiers. The explicit remaining producer
parameter supplies a common global core and comparison only. It does not
assume LocalizedFlow, either growth conclusion, or a proper heat barrier.
No unconditional F01 proof is asserted in this module. -/
noncomputable section
namespace Yau.NodeProofs
open Yau Yau.Blueprint F01Aux

/-- The unresolved common global producer, without either original growth
clause or a proper heat barrier. It is only a parameter of the conditional
theorem below and is not an assumption of the original contract. -/
def F01GlobalCoreComparisonGap : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ), ControlledExhaustion X o u → CanonicalInitialData X o →
    ∃ (h : Flow X) (U P ρ : STF X) (η : ℝ), 0 < η ∧
      LocalizedFlowCore X h U P ρ ∧ SmoothRicciWeightComparison X u U P η

theorem F01_contract_of_global_core_comparison
    (hglobal : F01GlobalCoreComparisonGap) :
    Yau.BlueprintContracts.F01_contract := by
  intro n X o
  obtain ⟨u, hu⟩ := P07_proved n X o
  have hinitial := P04_proved n X o
  obtain ⟨h, U, P, ρ, η, hη, hcore, hcomparison⟩ := hglobal n X o u hu hinitial
  exact ⟨h, U, P, ρ, localizedFlow_of_core_and_smooth_comparison
    X o u hu h U P ρ hcore hη hcomparison hinitial⟩

end Yau.NodeProofs
