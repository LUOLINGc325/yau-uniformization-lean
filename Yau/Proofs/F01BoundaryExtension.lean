import Yau.Proofs.F01ChartBuffer
import Yau.Proofs.F01BoundaryRatioBounds
import Yau.Proofs.F01CompactJets

/-! A genuine smooth extension of the rescaled boundary coefficient across
scale zero. Its open domain is derived from the actual segment integral and
the derivative budget; it is not supplied as a regularity assumption. -/
open Set Metric
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def scaledEvaluation (c : ℝ) (θ : BoundaryParameters E) : E :=
  θ.1 + (c * θ.2.1) • θ.2.2

theorem scaledEvaluation_contDiff (c : ℝ) : ContDiff ℝ ∞ (scaledEvaluation (E := E) c) := by
  unfold scaledEvaluation
  fun_prop

def boundaryExtension (u : E → ℝ) (G : E → F) (L c : ℝ)
    (θ : BoundaryParameters E) : F :=
  (c ^ 2 / (boundaryRatio u L c θ.1 θ.2.1 θ.2.2) ^ 2) • G (scaledEvaluation c θ)

theorem boundaryExtension_smooth_neighborhood (b : E) {r c L M : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hcr : c ≤ r / 12) (hL : 0 < L) (hM : 0 ≤ M)
    {u : E → ℝ} {G : E → F}
    (hu : ContDiffOn ℝ ∞ u (ball b (4 * r)))
    (hG : ContDiffOn ℝ ∞ G (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ u y‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) :
    ∃ V : Set (BoundaryParameters E), IsOpen V ∧
      closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 2) ⊆ V ∧
      ContDiffOn ℝ ∞ (boundaryExtension u G L c) V := by
  let B := bufferParameters b r
  let R : BoundaryParameters E → ℝ := fun θ => boundaryRatio u L c θ.1 θ.2.1 θ.2.2
  have hB : IsOpen B := bufferParameters_isOpen b r
  have hseg : ∀ θ ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
      segmentEvaluation c (θ, t) ∈ ball b (4 * r) :=
    fun _ hθ _ ht => bufferParameters_segment_mem b hr hc hcr hθ ht
  have hR : ContDiffOn ℝ ∞ R B :=
    boundaryRatio_contDiffOn isOpen_ball hu hB L c hseg
  let V := B ∩ R ⁻¹' Ioi 0
  have hV : IsOpen V := hR.continuousOn.isOpen_inter_preimage hB isOpen_Ioi
  refine ⟨V, hV, ?_, ?_⟩
  · intro θ hθ
    have hθB := compact_parameters_subset_buffer b hr hθ
    refine ⟨hθB, ?_⟩
    have hz : ‖θ.2.2‖ ≤ 2 := by
      simpa only [mem_closedBall, dist_zero_right] using hθ.2.2
    have hb := boundaryRatio_budget_of_derivative_bound u θ.1 θ.2.2
      (δ := θ.2.1) hL hc hM hz
      (fun t ht => hD _ (hseg θ hθB t ht)) hbudget
    have hrange := boundaryRatio_bounds_of_integral_budget u L c θ.1 θ.2.1 θ.2.2 hb
    change 0 < boundaryRatio u L c θ.1 θ.2.1 θ.2.2
    linarith [hrange.1]
  · have hRV := hR.mono (show V ⊆ B from inter_subset_left)
    have hscalar : ContDiffOn ℝ ∞ (fun θ : BoundaryParameters E => c ^ 2 / R θ ^ 2) V :=
      contDiffOn_const.div (hRV.pow 2) (fun θ hθ => pow_ne_zero 2 (ne_of_gt hθ.2))
    have hGV : ContDiffOn ℝ ∞ (fun θ : BoundaryParameters E => G (scaledEvaluation c θ)) V :=
      hG.comp (scaledEvaluation_contDiff c).contDiffOn (fun θ hθ => by
        simpa only [segmentEvaluation, one_mul, scaledEvaluation] using
          hseg θ hθ.1 1 ⟨by norm_num, le_rfl⟩)
    exact hscalar.smul hGV

theorem boundaryExtension_all_derivative_budgets (b : E) {r c L M : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hcr : c ≤ r / 12) (hL : 0 < L) (hM : 0 ≤ M)
    {u : E → ℝ} {G : E → F}
    (hu : ContDiffOn ℝ ∞ u (ball b (4 * r)))
    (hG : ContDiffOn ℝ ∞ G (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ u y‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ k θ,
      θ ∈ closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 2) →
      ‖iteratedFDeriv ℝ k (boundaryExtension u G L c) θ‖ ≤ C k := by
  obtain ⟨V, hV, hKV, hf⟩ := boundaryExtension_smooth_neighborhood b hr hc hcr hL hM hu hG hD hbudget
  exact compact_all_derivative_budgets hV (compact_parameters_isCompact b r) hKV hf

end Yau.NodeProofs.F01Aux
