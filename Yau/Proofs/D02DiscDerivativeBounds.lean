import Yau.Proofs.D02DiscInverse
import Yau.Proofs.D02UniformImmersionConstants

/-! A single Cauchy/Schwarz derivative bound on every smaller disc, for
every member of the original compact-boundary family. -/

open scoped Manifold Topology ContDiff ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem bounded_holomorphic_disc_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) (B : ℝ)
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ B)
    {r : ℝ} (hr : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖deriv f z‖ ≤ (2 * max B 0 + 1) / (1 - r) := by
  let R : ℝ := 1 - r
  have hR : 0 < R := by dsimp only [R]; linarith
  have hball : Metric.ball z R ⊆ Metric.ball (0 : ℂ) 1 := by
    intro w hw
    have htri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - z) z
    have hdist : ‖w - z‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    rw [Metric.mem_ball, dist_zero_right]
    dsimp only [R] at hdist
    linarith
  have hzD : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz.trans_lt hr
  have hmap : Set.MapsTo f (Metric.ball z R) (Metric.closedBall (f z) (2 * max B 0 + 1)) := by
    intro w hw
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) ≤ dist (f w) 0 + dist 0 (f z) := dist_triangle _ _ _
      _ = ‖f w‖ + ‖f z‖ := by simp
      _ ≤ 2 * max B 0 + 1 := by linarith [hb w (hball hw), hb z hzD, le_max_left B 0]
  exact Complex.norm_deriv_le_div_of_mapsTo_ball (hf.mono hball) hmap hR

theorem uniform_immersionDisc_derivative {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F)
    {K : Set (Pt X)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, r < 1 →
      ∀ f : ℂ → Pt X, IsHolomorphicDisc f →
        (∀ z : ℂ, ‖z‖ = 1 → f z ∈ K) → ∀ z : ℂ, ‖z‖ ≤ r →
          ‖deriv (fun w => F (f w)) z‖ ≤ B / (1 - r) := by
  obtain ⟨B, hB, hbound⟩ := immersion_uniformDisc_bound hF hK
  refine ⟨2 * max B 0 + 1, by positivity, fun r hr f hf hb z hz => ?_⟩
  exact bounded_holomorphic_disc_derivative (fun w => F (f w))
    ((immersionDisc_differentiableOn hF hf).mono Metric.ball_subset_closedBall) B
    (fun w hw => hbound f hf hb w (show ‖w‖ ≤ 1 from
      (show ‖w‖ < 1 from by simpa only [Metric.mem_ball, dist_zero_right] using hw).le)) hr hz

end Yau.NodeProofs.D02Aux
