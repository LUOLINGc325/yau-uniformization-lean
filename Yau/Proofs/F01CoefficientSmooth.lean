import Yau.Proofs.F01CoefficientExtensions

/-! Smoothness of the actual positive-scale coefficient on its whole fixed
coordinate ball, derived from the original smooth data and the gap budget. -/
open Set Metric
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem actual_coefficient_contDiffOn (b z₀ : E) {r c L M δ : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hcr : c ≤ r / 12) (hL : 0 < L) (hM : 0 ≤ M)
    {u : E → ℝ} {G : E → F}
    (hu : ContDiffOn ℝ ∞ u (ball b (4 * r)))
    (hG : ContDiffOn ℝ ∞ G (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ u y‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2)
    (hz₀ : z₀ ∈ closedBall b r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbase : 1 - u z₀ / L = δ) :
    ContDiffOn ℝ ∞ (fun z => interiorExtension u G L c (z₀, δ, z)) (ball (0 : E) 1) := by
  have hseg (z : E) (hz : z ∈ ball (0 : E) 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      z₀ + (t * (c * δ)) • z ∈ ball b (4 * r) := by
    have hz2 : z ∈ closedBall (0 : E) 2 :=
      mem_closedBall.mpr ((mem_ball.mp hz).le.trans (by norm_num))
    have hparam : (z₀, δ, z) ∈ closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 2) :=
      ⟨hz₀, ⟨hδ.le, hδ1⟩, hz2⟩
    exact bufferParameters_segment_mem (E := E) b hr hc hcr (θ := (z₀, δ, z))
      (compact_parameters_subset_buffer b hr hparam) ht
  have hmap : MapsTo (fun z : E => z₀ + (c * δ) • z) (ball 0 1) (ball b (4 * r)) := by
    intro z hz
    simpa only [one_mul] using hseg z hz 1 ⟨by norm_num, le_rfl⟩
  have heval : ContDiff ℝ ∞ (fun z : E => z₀ + (c * δ) • z) := by fun_prop
  have hv : ContDiffOn ℝ ∞ (fun z : E => u (z₀ + (c * δ) • z) / L) (ball 0 1) :=
    (hu.comp heval.contDiffOn hmap).div_const L
  have hprofile : ContDiffOn ℝ ∞
      (fun z : E => conformalProfile (u (z₀ + (c * δ) • z) / L)) (ball 0 1) := by
    apply conformalProfile_contDiffOn.comp hv
    intro z hz
    apply (div_lt_one hL).mpr
    have hn : ‖z‖ ≤ 2 := by
      have h : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
      linarith
    exact rescaled_point_below_level isOpen_ball hu z₀ z hL hc hM hδ hbase hn
      (hseg z hz) (fun t ht => hD _ (hseg z hz t ht)) hbudget
  simpa only [interiorExtension, scaledEvaluation, Pi.smul_def', Function.comp_def] using
    (contDiffOn_const.mul hprofile.exp).smul (hG.comp heval.contDiffOn hmap)

end Yau.NodeProofs.F01Aux
