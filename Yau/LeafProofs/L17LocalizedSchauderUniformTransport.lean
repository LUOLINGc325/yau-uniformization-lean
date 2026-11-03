import Yau.LeafProofs.L17LocalizedSchauderSourceFamilies

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- The all-chart cutoff transport constant is chosen before the partition,
its scale, the time cylinder, and the local family. -/
theorem exists_uniform_cutoff_transport_budget (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (k : ℕ) (hk : k ≤ 2) (C gamma : ℝ) (hC : 0 ≤ C) (hγ : 0 < gamma) (hγone : gamma ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : UniformChartPartition g), P.charts = A →
      ∀ (hρone : P.radius ≤ 1), 2*P.radius < A.radius → CutoffJetBounds P k C →
      ∀ (T F : ℝ), 0 ≤ F → ∀ (f : P.centers → Time T → ComplexVector n → ℝ),
      UnitLocalJetData P T k gamma F f → ∀ (p : P.centers) (q : M.Carrier) (t s : Time T)
      (z w : ComplexVector n), z ∈ ball 0 1 → w ∈ ball 0 1 → ∀ j, j ≤ k →
        ‖iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q t) z‖ ≤ K*F ∧
        ‖iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q t) z-
          iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q s) w‖ ≤
            K*F*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
  obtain ⟨D,hD,hNorm,hDiff⟩ := exists_scaled_transition_pair_budget A k
  let K := completeTransportJetBudget A k C D gamma
  have hKbase : transportJetBudget k C D gamma ≤ K := le_max_left _ _
  refine ⟨K,(transportJetBudget_pos k hC (zero_le_one.trans hD)).trans_le hKbase,?_⟩
  intro P hPA hρone hρr hCut T F hF f hf p q t s z w hz hw j hj
  have hTrans : TransitionJetBounds P.charts k D := by rw [hPA]; exact ⟨hNorm,hDiff⟩
  have hρr' : 2*P.radius < P.charts.radius := by rwa [hPA]
  constructor
  · exact (cutoffUnitFamily_norm_le P hg hρone hρr' hk hC hD hF hγ hγone f hf hCut hTrans p q t hz j hj).trans
      (mul_le_mul_of_nonneg_right hKbase hF)
  · simpa only [hPA] using
      cutoffUnitFamily_sub_le P hg hρone hρr' hk hC hD hF hγ hγone f hf hCut hTrans p q t s hz hw j hj

end Yau.LeafProofs.L17LocalizedSchauderAux
