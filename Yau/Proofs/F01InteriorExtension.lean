import Yau.Proofs.F01BoundaryExtension
import Yau.Proofs.F01ConformalProfile

/-! The interior family uses the compact CLOSED GRAPH of the actual gap.
Its scale and center are linked by δ=1-u(z₀)/L. No rectangular family is
asserted smooth across the singular level u/L=1. -/
open Set Metric
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def interiorParameters (u : E → ℝ) (L : ℝ) (b : E) (r : ℝ) : Set (BoundaryParameters E) :=
  {θ ∈ closedBall b r ×ˢ (Icc (1 / 8 : ℝ) 1 ×ˢ closedBall (0 : E) 2) |
    1 - u θ.1 / L = θ.2.1}

theorem interiorParameters_isCompact (b : E) {r : ℝ} (hr : 0 < r)
    {u : E → ℝ} (hu : ContinuousOn u (ball b (4 * r))) (L : ℝ) :
    IsCompact (interiorParameters u L b r) := by
  let K := closedBall b r ×ˢ (Icc (1 / 8 : ℝ) 1 ×ˢ closedBall (0 : E) 2)
  have hK : IsCompact K :=
    (isCompact_closedBall b r).prod (isCompact_Icc.prod (isCompact_closedBall 0 2))
  have hmap : MapsTo (fun θ : BoundaryParameters E => θ.1) K (ball b (4 * r)) := by
    intro θ hθ
    exact mem_ball.mpr ((mem_closedBall.mp hθ.1).trans_lt (by linarith))
  have hleft : ContinuousOn (fun θ : BoundaryParameters E => 1 - u θ.1 / L) K :=
    continuousOn_const.sub ((hu.comp continuous_fst.continuousOn hmap).div_const L)
  have hright : ContinuousOn (fun θ : BoundaryParameters E => θ.2.1) K := by fun_prop
  exact hK.of_isClosed_subset (hK.isClosed.isClosed_eq hleft hright) (fun _ h => h.1)

def interiorExtension (u : E → ℝ) (G : E → F) (L c : ℝ)
    (θ : BoundaryParameters E) : F :=
  ((c * θ.2.1) ^ 2 * Real.exp (conformalProfile (u (scaledEvaluation c θ) / L))) •
    G (scaledEvaluation c θ)

theorem interiorExtension_smooth_neighborhood (b : E) {r c L M : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hcr : c ≤ r / 12) (hL : 0 < L) (hM : 0 ≤ M)
    {u : E → ℝ} {G : E → F}
    (hu : ContDiffOn ℝ ∞ u (ball b (4 * r)))
    (hG : ContDiffOn ℝ ∞ G (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ u y‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) :
    ∃ V : Set (BoundaryParameters E), IsOpen V ∧ interiorParameters u L b r ⊆ V ∧
      ContDiffOn ℝ ∞ (interiorExtension u G L c) V := by
  let B := bufferParameters b r
  have hB : IsOpen B := bufferParameters_isOpen b r
  have hseg : ∀ θ ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
      segmentEvaluation c (θ, t) ∈ ball b (4 * r) :=
    fun _ hθ _ ht => bufferParameters_segment_mem b hr hc hcr hθ ht
  have hmap : MapsTo (scaledEvaluation (E := E) c) B (ball b (4 * r)) := by
    intro θ hθ
    simpa only [segmentEvaluation, one_mul, scaledEvaluation] using hseg θ hθ 1 ⟨by norm_num, le_rfl⟩
  have hv : ContDiffOn ℝ ∞ (fun θ => u (scaledEvaluation c θ) / L) B :=
    (hu.comp (scaledEvaluation_contDiff c).contDiffOn hmap).div_const L
  let V := B ∩ (fun θ => u (scaledEvaluation c θ) / L) ⁻¹' Iio 1
  have hV : IsOpen V := hv.continuousOn.isOpen_inter_preimage hB isOpen_Iio
  refine ⟨V, hV, ?_, ?_⟩
  · intro θ hθ
    have hθK : θ ∈ closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 2) :=
      ⟨hθ.1.1, ⟨by linarith [hθ.1.2.1.1], hθ.1.2.1.2⟩, hθ.1.2.2⟩
    have hθB := compact_parameters_subset_buffer b hr hθK
    refine ⟨hθB, ?_⟩
    apply (div_lt_one hL).mpr
    have hz : ‖θ.2.2‖ ≤ 2 := by
      simpa only [mem_closedBall, dist_zero_right] using hθ.1.2.2
    exact rescaled_point_below_level isOpen_ball hu θ.1 θ.2.2 hL hc hM
      (by linarith [hθ.1.2.1.1]) hθ.2 hz
      (fun t ht => hseg θ hθB t ht) (fun t ht => hD _ (hseg θ hθB t ht)) hbudget
  · have hprofile : ContDiffOn ℝ ∞
        (fun θ : BoundaryParameters E => conformalProfile (u (scaledEvaluation c θ) / L)) V :=
      conformalProfile_contDiffOn.comp (hv.mono inter_subset_left) (fun _ hθ => hθ.2)
    have hscale : ContDiffOn ℝ ∞ (fun θ : BoundaryParameters E => (c * θ.2.1) ^ 2) V := by
      fun_prop
    have hGV := hG.comp (scaledEvaluation_contDiff c).contDiffOn hmap
    exact (hscale.mul hprofile.exp).smul (hGV.mono inter_subset_left)

theorem interiorExtension_all_derivative_budgets (b : E) {r c L M : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hcr : c ≤ r / 12) (hL : 0 < L) (hM : 0 ≤ M)
    {u : E → ℝ} {G : E → F}
    (hu : ContDiffOn ℝ ∞ u (ball b (4 * r)))
    (hG : ContDiffOn ℝ ∞ G (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ u y‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ k θ, θ ∈ interiorParameters u L b r →
      ‖iteratedFDeriv ℝ k (interiorExtension u G L c) θ‖ ≤ C k := by
  obtain ⟨V, hV, hKV, hf⟩ := interiorExtension_smooth_neighborhood b hr hc hcr hL hM hu hG hD hbudget
  exact compact_all_derivative_budgets hV
    (interiorParameters_isCompact b hr hu.continuousOn L) hKV hf

end Yau.NodeProofs.F01Aux
