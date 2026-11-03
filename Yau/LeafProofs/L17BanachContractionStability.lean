import Yau.LeafProofs.L17BanachContractionSolution

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BanachContractionAux

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem ball_equations_stability (e : X ≃L[ℝ] Y) (f₁ f₂ : Y) (N₁ N₂ : X → Y)
    {r L δ : ℝ}
    (hLip : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N₁ u-N₁ v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2)
    (hDelta : ∀ v, ‖v‖ ≤ r → ‖(f₁+N₁ v)-(f₂+N₂ v)‖ ≤ δ)
    {u₁ u₂ : X} (hu₁ : ‖u₁‖ ≤ r) (hu₂ : ‖u₂‖ ≤ r)
    (heq₁ : e u₁=f₁+N₁ u₁) (heq₂ : e u₂=f₂+N₂ u₂) :
    ‖u₁-u₂‖ ≤ 2*‖e.symm.toContinuousLinearMap‖*δ := by
  have h₁ := (equation_iff_fixed e f₁ N₁ u₁).mp heq₁
  have h₂ := (equation_iff_fixed e f₂ N₂ u₂).mp heq₂
  have hLip' := iterationMap_sub_norm_le e f₁ N₁ hLip hSmall hu₁ hu₂
  have hDelta' : ‖iterationMap e f₁ N₁ u₂-iterationMap e f₂ N₂ u₂‖
      ≤ ‖e.symm.toContinuousLinearMap‖*δ := by
    calc
      ‖iterationMap e f₁ N₁ u₂-iterationMap e f₂ N₂ u₂‖
          = ‖e.symm ((f₁+N₁ u₂)-(f₂+N₂ u₂))‖ := by rw [iterationMap,iterationMap,← map_sub]
      _ ≤ ‖e.symm.toContinuousLinearMap‖*‖(f₁+N₁ u₂)-(f₂+N₂ u₂)‖ :=
        e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.symm.toContinuousLinearMap‖*δ :=
        mul_le_mul_of_nonneg_left (hDelta u₂ hu₂) (norm_nonneg _)
  have hbound : ‖u₁-u₂‖ ≤ (1/2 : ℝ)*‖u₁-u₂‖+‖e.symm.toContinuousLinearMap‖*δ := by
    calc
      ‖u₁-u₂‖ = ‖(iterationMap e f₁ N₁ u₁-iterationMap e f₁ N₁ u₂)+
          (iterationMap e f₁ N₁ u₂-iterationMap e f₂ N₂ u₂)‖ := by rw [h₁,h₂]; congr 1; abel
      _ ≤ ‖iterationMap e f₁ N₁ u₁-iterationMap e f₁ N₁ u₂‖+
          ‖iterationMap e f₁ N₁ u₂-iterationMap e f₂ N₂ u₂‖ := norm_add_le _ _
      _ ≤ (1/2 : ℝ)*‖u₁-u₂‖+‖e.symm.toContinuousLinearMap‖*δ := add_le_add hLip' hDelta'
  linarith

variable [CompleteSpace X]

theorem ballSolution_stability (e : X ≃L[ℝ] Y) (f₁ f₂ : Y) (N₁ N₂ : X → Y)
    (r L : ℝ) (hr : 0 ≤ r)
    (hLip₁ : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N₁ u-N₁ v‖ ≤ L*‖u-v‖)
    (hLip₂ : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N₂ u-N₂ v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2)
    (hZero₁ : ‖e.symm (f₁+N₁ 0)‖ ≤ r/2) (hZero₂ : ‖e.symm (f₂+N₂ 0)‖ ≤ r/2)
    {δ : ℝ} (hDelta : ∀ v, ‖v‖ ≤ r → ‖(f₁+N₁ v)-(f₂+N₂ v)‖ ≤ δ) :
    ‖ballSolution e f₁ N₁ r L hr hLip₁ hSmall hZero₁-
      ballSolution e f₂ N₂ r L hr hLip₂ hSmall hZero₂‖ ≤ 2*‖e.symm.toContinuousLinearMap‖*δ :=
  ball_equations_stability e f₁ f₂ N₁ N₂ hLip₁ hSmall hDelta
    (ballSolution_mem e f₁ N₁ r L hr hLip₁ hSmall hZero₁)
    (ballSolution_mem e f₂ N₂ r L hr hLip₂ hSmall hZero₂)
    (ballSolution_equation e f₁ N₁ r L hr hLip₁ hSmall hZero₁)
    (ballSolution_equation e f₂ N₂ r L hr hLip₂ hSmall hZero₂)

end Yau.LeafProofs.L17BanachContractionAux
