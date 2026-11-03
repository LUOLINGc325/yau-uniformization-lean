import Yau.Proofs.Y04MacroDegree

/-! Extract the final macro-endpoint subsequence without intersecting two tails. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y04Proof

open Yau Yau.Blueprint Y03Proof

theorem forwardDegreeControl_of_macro_bound
    {n : ℕ} {G : ℕ → PolyMap n} {Q : ℕ → ℝ}
    {N jBound j₀ : ℕ} {M hm B : ℝ}
    (hB : 0 < B)
    (hbound : ∀ j, j₀ ≤ j →
      ((forwardComp G (offset Q N M hm j₀ j)).degree : ℝ) ≤ B*Q j)
    (hgood : ∀ J, ∃ j, max J jBound ≤ j ∧
      Q j ≤ 3*Real.exp hm*macroClock hm j) :
    ForwardDegreeControl G (gridClock Q N M hm j₀) hm := by
  refine ⟨B*(3*Real.exp hm), by positivity, ?_⟩
  intro R
  obtain ⟨j, hj, hQj⟩ := hgood (j₀+R)
  have hj₀ : j₀ ≤ j := by omega
  refine ⟨j, offset Q N M hm j₀ j, by omega, ?_, ?_, ?_⟩
  · have := sub_le_offset Q N M hm j₀ j
    omega
  · exact gridClock_offset Q N M hm hj₀
  · rw [gridClock_offset Q N M hm hj₀]
    calc
      _ ≤ B*Q j := hbound j hj₀
      _ ≤ B*(3*Real.exp hm*macroClock hm j) := mul_le_mul_of_nonneg_left hQj hB.le
      _ = _ := by ring

end Yau.Blueprint.Alignment.Y04Proof
