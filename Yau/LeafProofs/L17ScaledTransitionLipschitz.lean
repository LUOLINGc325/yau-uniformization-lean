import Yau.LeafProofs.L17ScaledTransitionJets
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform Lipschitz bounds for every actual unit-scaled transition jet. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.exists_scaled_transition_jet_segment_budget
    (A : BoundedChartFamily g) (k : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (a : ChartScaleIndex M) (z w : ComplexVector n),
      segment ℝ z w ⊆ A.scaledTransitionDomain a → ∀ j, j ≤ k →
        ‖iteratedFDeriv ℝ j (A.scaledTransitionMap a) w -
            iteratedFDeriv ℝ j (A.scaledTransitionMap a) z‖ ≤ D * ‖w - z‖ := by
  obtain ⟨D, hD, hb⟩ := A.scaledTransition_uniformJetBounds (k + 1)
  refine ⟨D, hD, ?_⟩
  intro a z w hs j hj
  have hdiff : ∀ x ∈ segment ℝ z w,
      DifferentiableAt ℝ (iteratedFDeriv ℝ j (A.scaledTransitionMap a)) x := by
    intro x hx
    have hAt := (A.scaledTransition_smooth a).contDiffAt
      ((A.scaledTransitionDomain_isOpen a).mem_nhds (hs hx))
    have hjinf : (j : ℕ∞ω) < ∞ := by
      change ((j : ℕ∞) : ℕ∞ω) < ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)
    exact hAt.differentiableAt_iteratedFDeriv hjinf
  have hbound : ∀ x ∈ segment ℝ z w,
      ‖fderiv ℝ (iteratedFDeriv ℝ j (A.scaledTransitionMap a)) x‖ ≤ D := by
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    exact hb a x (hs hx) (j + 1) (by omega)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_segment z w)
    (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)

end Yau.LeafProofs.L17Aux
