import Yau.Proofs.Y04BadCharging
import spec.CHAIN.CONTRACTS

/-! Parameter choices precede the grid and preserve the original witness order. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau Yau.Blueprint Yau.Blueprint.Alignment
open Yau.Blueprint.Alignment.Y03Proof

/-- The flag threshold is chosen after the fixed degree bound and the window
width; it is independent of the later regular starting endpoint. -/
theorem exists_flag_threshold (Dstar N : ℕ) (hm b₀ : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      Real.log (Dstar : ℝ) + max 0 (Real.log (2 / b₀)) / (2 * N + 1 : ℝ) ≤
        M / (3 * (2 * N + 1 : ℝ)) ∧
      hm < M / (3 * (2 * N + 1 : ℝ)) := by
  let A := max 1 (max
    (Real.log (Dstar : ℝ) + max 0 (Real.log (2 / b₀)) / (2 * N + 1 : ℝ))
    (hm + 1))
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hden : 0 < (3 * (2 * N + 1 : ℝ)) := by positivity
  refine ⟨3 * (2 * N + 1 : ℝ) * A, mul_pos hden hA, ?_, ?_⟩
  · rw [mul_div_cancel_left₀ A (ne_of_gt hden)]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · rw [mul_div_cancel_left₀ A (ne_of_gt hden)]
    exact (lt_add_one hm).trans_le ((le_max_right _ _).trans (le_max_right _ _))

/-- The zero dimensional case cannot provide the positive clock increments
and determinant rate identity already produced by the original Y03 contract. -/
theorem zero_dimension_grid_rates_impossible
    {F : ℝ → ℝ → ComplexVector 0 → ComplexVector 0} {tk : ℕ → ℝ}
    {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ} {E : Frames 0}
    (hgrid : GridLayout Q N M hm j₀)
    (hframes : SingularFrames F tk E)
    (hrates : ∀ k, ∑ i, rate F tk E k i =
      (gridClock Q N M hm j₀ (k + 1) - gridClock Q N M hm j₀ k) /
        Real.log (tk (k + 1) / tk k)) : False := by
  have ht0 := (hframes 0).1
  have ht01 := (hframes 0).2.1
  have hratio : 1 < tk 1 / tk 0 := (one_lt_div ht0).2 ht01
  have hlog : 0 < Real.log (tk 1 / tk 0) := Real.log_pos hratio
  have hgap : 0 < gridClock Q N M hm j₀ 1 - gridClock Q N M hm j₀ 0 :=
    sub_pos.2 (hgrid.2.1 (by omega : 0 < 1))
  have hpos := div_pos hgap hlog
  have hz := hrates 0
  simp only [Fin.sum_univ_zero, zero_add] at hz
  linarith

end Yau.Proofs.Y01Aux
