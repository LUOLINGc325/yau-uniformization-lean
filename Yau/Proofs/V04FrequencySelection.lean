import Yau.Blueprint.VariationContracts
import Yau.Proofs.V04OrderedLimits

/-! The original frequency-selection conclusion uses no geometric hypothesis.
All choices precede the sequence index, as required by the frozen interface. -/

open Filter
open scoped Topology

noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem frequencySelection (d : VariationData X q) : FrequencySelection d := by
  intro j F _ hzero
  obtain ⟨B, hB, hlim, hcap⟩ := exists_ordered_energy_cap
    (fun ε ν => 1 + (variationEnergy d j (F ε ν)).toReal)
    (fun ε ν => le_add_of_nonneg_right ENNReal.toReal_nonneg) hzero
  exact ⟨B, hB, hlim, hcap, intermediate_frequency_limits B hB hlim⟩

/-- A common finite shift preserves the actual minimizing sequence. -/
theorem minimizingSequence_nat_add {d : VariationData X q} {j : ℕ} {ε : ℝ}
    {F : ℕ → VariationDisc X} (hF : MinimizingSequence d j ε F) (N : ℕ) :
    MinimizingSequence d j ε (fun ν => F (ν + N)) :=
  ⟨fun ν => hF.1 (ν + N), hF.2.comp (tendsto_add_atTop_nat N)⟩

theorem seqUpperZero_nat_add_iff (a : ℕ → ℝ) (N : ℕ) :
    SeqUpperZero (fun ν => a (ν + N)) ↔ SeqUpperZero a := by
  unfold SeqUpperZero
  have hshift (p : ℕ → Prop) : (∀ᶠ ν in atTop, p (ν + N)) ↔ ∀ᶠ ν in atTop, p ν := by
    change (∀ᶠ ν in Filter.map (fun ν => ν + N) atTop, p ν) ↔ _
    rw [map_add_atTop_eq_nat]
  constructor
  · intro h r hr
    exact (hshift (fun ν => a ν ≤ r)).1 (h r hr)
  · intro h r hr
    exact (hshift (fun ν => a ν ≤ r)).2 (h r hr)

theorem epsSeqZero_nat_add_iff (a : ℝ → ℕ → ℝ) (N : ℕ) :
    EpsSeqZero (fun ε ν => a ε (ν + N)) ↔ EpsSeqZero a := by
  unfold EpsSeqZero
  have hshift (p : ℕ → Prop) : (∀ᶠ ν in atTop, p (ν + N)) ↔ ∀ᶠ ν in atTop, p ν := by
    change (∀ᶠ ν in Filter.map (fun ν => ν + N) atTop, p ν) ↔ _
    rw [map_add_atTop_eq_nat]
  constructor
  · intro h r hr
    filter_upwards [h r hr] with ε hε
    exact (hshift (fun ν => |a ε ν| ≤ r)).1 hε
  · intro h r hr
    filter_upwards [h r hr] with ε hε
    exact (hshift (fun ν => |a ε ν| ≤ r)).2 hε

end Yau.Blueprint.V04Proof
