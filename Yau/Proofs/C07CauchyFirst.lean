import Mathlib

namespace Yau.Proofs.C07Aux

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A Banach-valued Cauchy estimate throughout the half ball.  Subtracting
the value at the moving center allows the exact Schwarz derivative estimate
to be used without assuming that center value vanishes. -/
theorem norm_fderiv_le_four_div {f : E → G} {R B : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hbound : ∀ z ∈ Metric.ball (0 : E) R, ‖f z‖ ≤ B)
    {z : E} (hz : z ∈ Metric.ball (0 : E) (R / 2)) :
    ‖fderiv ℂ f z‖ ≤ 4 * B / R := by
  have hzR : z ∈ Metric.ball (0 : E) R :=
    Metric.ball_subset_ball (by linarith) hz
  have hsub : Metric.ball z (R / 2) ⊆ Metric.ball (0 : E) R := by
    intro w hw
    have hdist := dist_triangle w z (0 : E)
    rw [Metric.mem_ball] at hw hz ⊢
    linarith
  have hmaps : Set.MapsTo f (Metric.ball z (R / 2)) (Metric.closedBall (f z) (2 * B)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hbound w (hsub hw), hbound z hzR])
  have h := Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) hmaps
    (by positivity : 0 < R / 2)
  exact h.trans_eq (by ring)

end Yau.Proofs.C07Aux
