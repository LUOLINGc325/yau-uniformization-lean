import Yau.Proofs.F01BoundaryRatioSmooth

/-! An explicit open neighborhood of the compact rescaling parameters.
Every segment used in the boundary ratio lies in the original chart buffer,
including at scale zero and at nearby negative scales. -/
open Set Metric
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def bufferParameters (b : E) (r : ℝ) : Set (BoundaryParameters E) :=
  ball b (2 * r) ×ˢ (Ioo (-2 : ℝ) 2 ×ˢ ball 0 3)

theorem bufferParameters_isOpen (b : E) (r : ℝ) : IsOpen (bufferParameters b r) :=
  isOpen_ball.prod (isOpen_Ioo.prod isOpen_ball)

theorem bufferParameters_segment_mem (b : E) {r c : ℝ} (hr : 0 < r)
    (hc : 0 ≤ c) (hcr : c ≤ r / 12) {θ : BoundaryParameters E}
    (hθ : θ ∈ bufferParameters b r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segmentEvaluation c (θ, t) ∈ ball b (4 * r) := by
  have hb : ‖θ.1 - b‖ < 2 * r := by simpa only [mem_ball, dist_eq_norm] using hθ.1
  have hd : ‖θ.2.1‖ ≤ 2 := by
    rw [Real.norm_eq_abs]
    exact (abs_lt.mpr hθ.2.1).le
  have hz : ‖θ.2.2‖ ≤ 3 := by
    exact (show ‖θ.2.2‖ < 3 by simpa only [mem_ball, dist_zero_right] using hθ.2.2).le
  have ht' : ‖t‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hscale : ‖(t * (c * θ.2.1)) • θ.2.2‖ ≤ 6 * c := by
    calc
      _ = ‖t‖ * (c * ‖θ.2.1‖) * ‖θ.2.2‖ := by
        simp only [norm_smul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hc]
      _ ≤ 1 * (c * 2) * 3 := by gcongr
      _ = 6 * c := by ring
  have heq : segmentEvaluation c (θ, t) - b =
      (θ.1 - b) + (t * (c * θ.2.1)) • θ.2.2 := by
    dsimp [segmentEvaluation]
    abel
  apply mem_ball.mpr
  rw [dist_eq_norm, heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem compact_parameters_subset_buffer (b : E) {r : ℝ} (hr : 0 < r) :
    closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall 0 2) ⊆ bufferParameters b r := by
  rintro θ ⟨hb, hδ, hz⟩
  refine ⟨mem_ball.mpr ((mem_closedBall.mp hb).trans_lt (by linarith)), ?_, ?_⟩
  · exact ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
  · exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by norm_num))

theorem compact_parameters_isCompact [FiniteDimensional ℝ E] (b : E) (r : ℝ) :
    IsCompact (closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 2)) :=
  (isCompact_closedBall b r).prod (isCompact_Icc.prod (isCompact_closedBall 0 2))

end Yau.NodeProofs.F01Aux
