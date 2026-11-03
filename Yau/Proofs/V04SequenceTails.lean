import Yau.Proofs.V04FrequencySelection

/-! All eventual hypotheses are enforced by one common shift of the
original discs, frames and test columns. -/

open Filter
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_minimizing_sequence_tail {d : VariationData X q} {j : ℕ} {ε : ℝ}
    {F : ℕ → VariationDisc X} (hF : MinimizingSequence d j ε F)
    (P : ℕ → Prop) (hP : ∀ᶠ ν in atTop, P ν) :
    ∃ N : ℕ, MinimizingSequence d j ε (fun ν => F (ν + N)) ∧ ∀ ν, P (ν + N) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  exact ⟨N, minimizingSequence_nat_add hF N, fun ν => hN (ν + N) (Nat.le_add_left _ _)⟩

theorem admissible_energy_finite {d : VariationData X q} {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) : variationEnergy d j F ≠ ⊤ :=
  hF.2.2.2.2.2.2.2.2

theorem admissible_energy_ofReal_toReal {d : VariationData X q} {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    ENNReal.ofReal (variationEnergy d j F).toReal = variationEnergy d j F :=
  ENNReal.ofReal_toReal (admissible_energy_finite hF)

end Yau.Blueprint.V04Proof
