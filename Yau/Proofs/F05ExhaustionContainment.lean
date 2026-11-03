import Yau.Proofs.HeatSmoothExhaustion

/-! Compact reference chart buffers eventually lie in every later member
of the actual nested smooth exhaustion. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_exhaustion_monotone {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O) :
    Monotone O :=
  monotone_nat_of_le_succ (fun j => subset_closure.trans (hO.2.1 j))

theorem F05_smooth_exhaustion_contains_compact {O : ℕ → Set M.Carrier}
    (hO : SmoothExhaustion O) {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → K ⊆ O j := by
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover O (fun j => (hO.1 j).1)
    (by rw [hO.2.2]; exact subset_univ K)
  refine ⟨s.sup id,?_⟩
  intro j hj x hx
  obtain ⟨k,hks,hxk⟩ := mem_iUnion₂.mp (hs hx)
  exact F05_smooth_exhaustion_monotone hO ((Finset.le_sup hks).trans hj) hxk

end Yau.Proofs.F05Aux
