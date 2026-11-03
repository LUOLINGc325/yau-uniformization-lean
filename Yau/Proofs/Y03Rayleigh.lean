import Yau.Blueprint.Alignment

/-! The positive Ricci-window infimum is an upper bound for every actual Rayleigh quotient. -/

noncomputable section

open scoped Matrix

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem relMinEigenvalue_le_of_pos {n : ℕ} {H A : Herm n}
    (hpos : 0 < relMinEigenvalue H A) (v : ComplexVector n) (hv : v ≠ 0) :
    relMinEigenvalue H A ≤ (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)).re /
      (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re := by
  let q : {v : ComplexVector n // v ≠ 0} → ℝ := fun v =>
    (star (WithLp.ofLp v.1) ⬝ᵥ (A *ᵥ WithLp.ofLp v.1)).re /
      (star (WithLp.ofLp v.1) ⬝ᵥ (H *ᵥ WithLp.ofLp v.1)).re
  have hbd : BddBelow (Set.range q) := by
    by_contra hn
    have hz := ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow (Set.range q) hn
    change 0 < sInf (Set.range q) at hpos
    rw [hz] at hpos
    norm_num at hpos
  exact ciInf_le hbd ⟨v, hv⟩

end Yau.Blueprint.Alignment.Y03Proof
