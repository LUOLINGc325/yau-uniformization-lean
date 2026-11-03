import spec.CHAIN.CONTRACTS

/-! Removal of the actual vanishing properness penalty at a fixed point. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem le_of_all_small_positive_penalties {u v f : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → u - v - δ * f ≤ 0) : u ≤ v := by
  by_contra huv
  have hgap : 0 < u - v := sub_pos.mpr (lt_of_not_ge huv)
  let δ := min 1 ((u - v) / (2 * (|f| + 1)))
  have hden : 0 < 2 * (|f| + 1) := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hgap hden)
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδbound : δ * (2 * (|f| + 1)) ≤ u - v :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have htest := h δ hδ hδone
  have hmul := mul_le_mul_of_nonneg_left (le_abs_self f) hδ.le
  nlinarith

end Yau.NodeProofs.F01Aux
