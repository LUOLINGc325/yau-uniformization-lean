import Yau.LeafProofs.L17UniformPartition

/-! The overlap budget is selected before the arbitrarily small chart scale. -/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.exists_uniform_partition_budget
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
      P.charts = A ∧ P.radius < ε ∧ P.radius ≤ 1 ∧ P.overlapBudget = N := by
  obtain ⟨N, hN⟩ := A.exists_uniform_net_cover hg
  refine ⟨N, ?_⟩
  intro ε hε
  let c := Real.sqrt (2 * (A.bound 0)⁻¹)
  let L := overlapScale A
  have hC := A.bound_pos 0
  have hc : 0 < c := by dsimp [c]; positivity
  have hL : 0 < L := overlapScale_pos A
  let ρ := min (min (ε / 2) (1 / 2)) (min (A.radius / 2) (c * A.radius / (8 * L)))
  have hr := A.radius_pos
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < A.radius :=
    (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt (by linarith)
  have hρε : ρ < ε :=
    (min_le_left _ _ |>.trans (min_le_left _ _)).trans_lt (by linarith)
  have hρone : ρ ≤ 1 := (min_le_left _ _ |>.trans (min_le_right _ _)).trans (by norm_num)
  have hρL : ρ ≤ c * A.radius / (8 * L) := (min_le_right _ _).trans (min_le_right _ _)
  have hbudget : L * ρ < c * (A.radius / 2) := by
    calc
      L * ρ ≤ L * (c * A.radius / (8 * L)) := mul_le_mul_of_nonneg_left hρL hL.le
      _ = c * A.radius / 8 := by field_simp
      _ < c * (A.radius / 2) := by nlinarith [mul_pos hc hr]
  obtain ⟨S, hcount, hsep, hcover, hover⟩ := hN ρ hρ hρr hbudget
  let := hcount.to_subtype
  refine ⟨⟨A, ρ, hρ, hρr, S, inferInstance, Subtype.val, N, ?_, ?_, ?_⟩,
    rfl, hρε, hρone, rfl⟩
  · simpa only [Subtype.range_val] using hsep
  · simpa only [Subtype.range_val] using hcover
  · rw [show Set.range (Subtype.val : S → M.Carrier) = S from Subtype.range_val]
    exact hover

end Yau.LeafProofs.L17Aux
