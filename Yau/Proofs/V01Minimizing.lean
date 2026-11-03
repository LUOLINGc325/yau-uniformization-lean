import spec.CHAIN.CONTRACTS
import Mathlib.Topology.Order.IsLUB

/-! A single minimizing family is chosen before any spectral parameter.
The infimum remains the original EReal infimum over all admissible discs. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_minimizingSequence (d : VariationData X q) (j : ℕ) (ε : ℝ)
    (hne : ∃ F, AdmissibleVariationDisc d j F) :
    ∃ F : ℕ → VariationDisc X, MinimizingSequence d j ε F := by
  classical
  let A := {F : VariationDisc X // AdmissibleVariationDisc d j F}
  let cost : A → EReal := fun F => (penalizedFunctional d j ε F.1 : EReal)
  have hcostne : (Set.range cost).Nonempty := by
    obtain ⟨F, hF⟩ := hne
    exact ⟨cost ⟨F, hF⟩, mem_range_self _⟩
  obtain ⟨u, _hanti, hlim, hu⟩ := exists_seq_tendsto_sInf hcostne
    (show BddBelow (Set.range cost) from ⟨⊥, fun _ _ => bot_le⟩)
  have hchoice (ν : ℕ) : ∃ F : A, cost F = u ν := hu ν
  choose F hF using hchoice
  have hinf : sInf (Set.range cost) = localizedInfimum d j ε := by
    simp only [sInf_range, cost, A, localizedInfimum, iInf_subtype]
  refine ⟨fun ν => (F ν).1, fun ν => (F ν).2, ?_⟩
  rw [hinf] at hlim
  convert hlim using 1
  funext ν
  exact hF ν

/-- The guarded invalid parameter set has an explicit total disc value. -/
def defaultVariationDisc (d : VariationData X q) : VariationDisc X :=
  { f := fun _ => (d.o, 0), w := fun _ => 0, s := 0 }

theorem exists_localizedMinimizers (d : VariationData X q)
    (hne : ∀ᶠ j in atTop, ∃ F, AdmissibleVariationDisc d j F) :
    ∃ F : ℕ → ℝ → ℕ → VariationDisc X, LocalizedMinimizers d F := by
  classical
  have hchoice (j : ℕ) (ε : ℝ) : ∃ F : ℕ → VariationDisc X,
      (∃ F₀, AdmissibleVariationDisc d j F₀) → MinimizingSequence d j ε F := by
    by_cases hj : ∃ F₀, AdmissibleVariationDisc d j F₀
    · obtain ⟨F, hF⟩ := exists_minimizingSequence d j ε hj
      exact ⟨F, fun _ => hF⟩
    · exact ⟨fun _ => defaultVariationDisc d, fun h => (hj h).elim⟩
  choose F hF using hchoice
  refine ⟨F, ?_⟩
  filter_upwards [hne] with j hj
  exact Eventually.of_forall (fun ε => hF j ε hj)

theorem exists_localizedMinimizers_of_localization (d : VariationData X q)
    (hLoc : LocalizationEstimates d) :
    ∃ F : ℕ → ℝ → ℕ → VariationDisc X, LocalizedMinimizers d F :=
  exists_localizedMinimizers d (hLoc.2.1.mono (fun _ h => h.1))

end Yau.Blueprint.V01Proof
