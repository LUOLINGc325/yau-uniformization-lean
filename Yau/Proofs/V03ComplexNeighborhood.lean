import Yau.Proofs.V03Elementary

/-! Compact parameter neighborhoods for a fixed complex direction. The
construction works in dimension zero and does not divide by the direction's
norm. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_compact_line_neighborhood {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (v : E) :
    ∃ (K : Set E) (R : ℝ), IsCompact K ∧ K ∈ 𝓝 x ∧ 0 < R ∧
      ∀ y ∈ K, ∀ t ∈ Metric.closedBall (0 : ℂ) R, y + t • v ∈ U := by
  letI : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let r : ℝ := ε / 4
  let R : ℝ := r / (1 + ‖v‖)
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hRv : R * ‖v‖ ≤ r := by
    dsimp [R]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1 + ‖v‖)]
    nlinarith
  refine ⟨Metric.closedBall x r, R, isCompact_closedBall _ _,
    Metric.closedBall_mem_nhds x hr, hR, ?_⟩
  intro y hy t ht
  have hty : ‖t‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ht
  have hyx : dist y x ≤ r := Metric.mem_closedBall.mp hy
  apply hεU
  rw [Metric.mem_ball]
  calc
    dist (y + t • v) x ≤ dist (y + t • v) y + dist y x := dist_triangle _ _ _
    _ = ‖t‖ * ‖v‖ + dist y x := by simp [dist_eq_norm, norm_smul]
    _ ≤ R * ‖v‖ + r :=
      add_le_add (mul_le_mul_of_nonneg_right hty (norm_nonneg v)) hyx
    _ ≤ 2 * r := by linarith
    _ < ε := by dsimp [r]; linarith

end Yau.Blueprint.V03Proof
