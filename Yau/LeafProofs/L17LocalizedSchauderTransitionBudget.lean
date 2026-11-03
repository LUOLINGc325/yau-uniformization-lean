import Yau.LeafProofs.L17LocalizedSchauderUnitTerm
import Yau.LeafProofs.L17ScaledTransitionLipschitz

open Set Metric
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Both actual finite jet budgets are selected before the chart scale. -/
theorem exists_scaled_transition_pair_budget (A : BoundedChartFamily g) (k : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧
      (∀ (a : ChartScaleIndex M) z, z ∈ A.scaledTransitionDomain a → ∀ j, j ≤ k →
        ‖iteratedFDeriv ℝ j (A.scaledTransitionMap a) z‖ ≤ D) ∧
      ∀ (a : ChartScaleIndex M) z w, segment ℝ z w ⊆ A.scaledTransitionDomain a → ∀ j, j ≤ k →
        ‖iteratedFDeriv ℝ j (A.scaledTransitionMap a) w-iteratedFDeriv ℝ j (A.scaledTransitionMap a) z‖ ≤
          D*‖w-z‖ := by
  obtain ⟨D,hD,hNorm⟩ := A.scaledTransition_uniformJetBounds k
  obtain ⟨L,hL,hLip⟩ := A.exists_scaled_transition_jet_segment_budget k
  refine ⟨max D L,hD.trans (le_max_left _ _),?_,?_⟩
  · intro a z hz j hj
    exact (hNorm a z hz j hj).trans (le_max_left _ _)
  · intro a z w hSegment j hj
    exact (hLip a z w hSegment j hj).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem scaled_transition_value_lipschitz (A : BoundedChartFamily g) (a : ChartScaleIndex M)
    {D : ℝ} {z w : ComplexVector n}
    (hJet : ‖iteratedFDeriv ℝ 0 (A.scaledTransitionMap a) w-
      iteratedFDeriv ℝ 0 (A.scaledTransitionMap a) z‖ ≤ D*‖w-z‖) :
    ‖A.scaledTransitionMap a z-A.scaledTransitionMap a w‖ ≤ D*‖z-w‖ := by
  have hh : ‖A.scaledTransitionMap a w-A.scaledTransitionMap a z‖ ≤ D*‖w-z‖ := by
    simpa only [norm_iteratedFDeriv_zero_sub] using hJet
  calc
    _ = ‖A.scaledTransitionMap a w-A.scaledTransitionMap a z‖ := norm_sub_rev _ _
    _ ≤ D*‖w-z‖ := hh
    _ = _ := by rw [norm_sub_rev w z]

end Yau.LeafProofs.L17LocalizedSchauderAux
