import Yau.Proofs.F01InteriorExtension
import Yau.Proofs.F01BoundaryGram
import Yau.Proofs.F01NestedPartialJetBound

/-! The two smooth parameter families bound the actual conformal coefficient
at every positive scale, with all constants chosen before center and scale. -/
open Set Metric Filter
open scoped ContDiff Topology
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem boundaryExtension_eq_interiorExtension {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) (G : E → F)
    {L c δ : ℝ} (hL : L ≠ 0) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z₀ z : E) (hbase : 1 - u z₀ / L = δ)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, z₀ + (t * (c * δ)) • z ∈ U)
    (hRlo : 0 < boundaryRatio u L c z₀ δ z)
    (hRhi : boundaryRatio u L c z₀ δ z ≤ 3 / 2) :
    boundaryExtension u G L c (z₀, δ, z) = interiorExtension u G L c (z₀, δ, z) := by
  have hgap := boundary_gap_factorization hU hu z₀ z L c δ hL hbase hseg
  have hcanc := scaled_conformal_scalar_cancellation hδ hδsmall hRlo hRhi hgap c
  change (c ^ 2 / (boundaryRatio u L c z₀ δ z) ^ 2) • G (z₀ + (c * δ) • z) =
    ((c * δ) ^ 2 * Real.exp (conformalProfile (u (z₀ + (c * δ) • z) / L))) •
      G (z₀ + (c * δ) • z)
  rw [hcanc]

theorem actual_coefficient_all_derivative_budgets (b : E) {r c L M : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hcr : c ≤ r / 12) (hL : 0 < L) (hM : 0 ≤ M)
    {u : E → ℝ} {G : E → F}
    (hu : ContDiffOn ℝ ∞ u (ball b (4 * r)))
    (hG : ContDiffOn ℝ ∞ G (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ u y‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ k z₀ δ z,
      z₀ ∈ closedBall b r → 0 < δ → δ ≤ 1 → 1 - u z₀ / L = δ → z ∈ ball (0 : E) 1 →
      ‖iteratedFDeriv ℝ k (fun w => interiorExtension u G L c (z₀, δ, w)) z‖ ≤ C k := by
  obtain ⟨VB, hVB, hKB, hfB⟩ := boundaryExtension_smooth_neighborhood b hr hc hcr hL hM hu hG hD hbudget
  obtain ⟨CB, hCB, hboundB⟩ := compact_all_derivative_budgets hVB
    (compact_parameters_isCompact b r) hKB hfB
  obtain ⟨VI, hVI, hKI, hfI⟩ := interiorExtension_smooth_neighborhood b hr hc hcr hL hM hu hG hD hbudget
  obtain ⟨CI, hCI, hboundI⟩ := compact_all_derivative_budgets hVI
    (interiorParameters_isCompact b hr hu.continuousOn L) hKI hfI
  refine ⟨fun k => max (CB k) (CI k), fun k => (hCB k).trans_le (le_max_left _ _), ?_⟩
  intro k z₀ δ z hz₀ hδ hδ1 hbase hz
  have hz2 : z ∈ closedBall (0 : E) 2 :=
    mem_closedBall.mpr ((mem_ball.mp hz).le.trans (by norm_num))
  by_cases hsmall : δ ≤ 1 / 8
  · have hparam : (z₀, δ, z) ∈ closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 2) :=
      ⟨hz₀, ⟨hδ.le, hδ1⟩, hz2⟩
    have heq : (fun w => boundaryExtension u G L c (z₀, δ, w)) =ᶠ[𝓝 z]
        (fun w => interiorExtension u G L c (z₀, δ, w)) := by
      filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball (0 : E) 2 from
        mem_ball.mpr ((mem_ball.mp hz).trans (by norm_num)))] with w hw
      have hθK : (z₀, δ, w) ∈ closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 2) :=
        ⟨hz₀, ⟨hδ.le, hδ1⟩, ball_subset_closedBall hw⟩
      have hθB := compact_parameters_subset_buffer b hr hθK
      have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
          z₀ + (t * (c * δ)) • w ∈ ball b (4 * r) :=
        fun t ht => bufferParameters_segment_mem b hr hc hcr hθB ht
      have hnw : ‖w‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hθK.2.2
      have hb := boundaryRatio_budget_of_derivative_bound u z₀ w (δ := δ) hL hc hM hnw
        (fun t ht => hD _ (hseg t ht)) hbudget
      have hR := boundaryRatio_bounds_of_integral_budget u L c z₀ δ w hb
      exact boundaryExtension_eq_interiorExtension isOpen_ball hu G hL.ne' hδ hsmall z₀ w hbase hseg
        (by linarith [hR.1]) hR.2
    rw [← (heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact ((norm_iteratedFDeriv_fixedTwo_le hVB hfB z₀ δ (hKB hparam) k).trans
      (hboundB k _ hparam)).trans (le_max_left _ _)
  · have hparam : (z₀, δ, z) ∈ interiorParameters u L b r :=
      ⟨⟨hz₀, ⟨(lt_of_not_ge hsmall).le, hδ1⟩, hz2⟩, hbase⟩
    exact ((norm_iteratedFDeriv_fixedTwo_le hVI hfI z₀ δ (hKI hparam) k).trans
      (hboundI k _ hparam)).trans (le_max_right _ _)

end Yau.NodeProofs.F01Aux
