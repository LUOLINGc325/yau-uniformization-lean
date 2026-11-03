import Yau.Proofs.C07Charts

/-! One positive transition radius works for every pair of the same uniformly bounded charts. -/

noncomputable section

namespace Yau.Proofs.C07Aux

theorem exists_transition_radius {r c C : ℝ} (hr : 0 < r) (hc : 0 < c) (hC : 0 < C) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧
      Real.sqrt (2 * C) * R ≤ Real.sqrt (2 * c) * r := by
  have hα : 0 < Real.sqrt (2 * c) * r := mul_pos (Real.sqrt_pos.2 (by positivity)) hr
  have hβ : 0 < Real.sqrt (2 * C) := Real.sqrt_pos.2 (by positivity)
  let R := min (r / 2) ((Real.sqrt (2 * c) * r) / (2 * Real.sqrt (2 * C)))
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  refine ⟨R, hR, (min_le_left _ _).trans_lt (by linarith), ?_⟩
  calc
    Real.sqrt (2 * C) * R ≤ Real.sqrt (2 * C) *
        ((Real.sqrt (2 * c) * r) / (2 * Real.sqrt (2 * C))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le
    _ = (Real.sqrt (2 * c) * r) / 2 := by field_simp <;> ring
    _ ≤ Real.sqrt (2 * c) * r := by linarith

end Yau.Proofs.C07Aux
