import Yau.Proofs.F03JointSpatialWords

/-! Literal all-jet initial convergence supplies genuine compact spatial bounds through time zero. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem compact_spatial_word_bound_through_initial
    (u : E × ℝ → ℝ) (f : E → ℝ) {O : Set E} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioi 0)) (hf : ContDiffOn ℝ ∞ f O)
    (hu0 : ∀ x,u (x,0)=f x)
    (hInitial : ∀ K : Set E,IsCompact K → K ⊆ O → ∀ m : ℕ,∀ ε : ℝ,0 < ε →
      ∃ δ : ℝ,0 < δ ∧ ∀ t,0 < t → t < δ → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun y => u (y,t)-f y) x‖ < ε)
    (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O) (R : ℝ) (w : List E) :
    ∃ C : ℝ,0 < C ∧ ∀ t ∈ Icc 0 R,∀ x ∈ K,
      |directionalWordDerivative (fun y => u (y,t)) w x| ≤ C := by
  obtain ⟨δ,hδ,hClose⟩ := hInitial K hK hKO w.length 1 zero_lt_one
  obtain ⟨P,hP,hPositive⟩ := compact_positive_spatial_word_bound u hO hu K hK hKO hδ w
  obtain ⟨F,hF⟩ := hK.exists_bound_of_continuousOn
    ((directionalWordDerivative_contDiffOn hO hf w).continuousOn.mono hKO)
  let W := ∏ i : Fin w.length,‖w.get i‖
  have hW : 0 ≤ W := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  let C := max F 0+P+W+1
  have hFC : F ≤ C := by dsimp [C];linarith [le_max_left F 0]
  have hPC : P ≤ C := by dsimp [C];linarith [le_max_right F 0]
  refine ⟨C,by dsimp [C];positivity,fun t ht x hx => ?_⟩
  have hFx : |directionalWordDerivative f w x| ≤ F := by
    simpa only [Real.norm_eq_abs] using hF x hx
  rcases eq_or_lt_of_le ht.1 with ht0|ht0
  · subst t
    have he : (fun y => u (y,0))=f := funext hu0
    rw [he]
    exact hFx.trans hFC
  · by_cases htδ : t < δ
    · have hSlice : ContDiffOn ℝ ∞ (fun y => u (y,t)) O :=
        hu.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy => ⟨hy,ht0⟩)
      have hSmall := spatial_word_difference_le_of_tensor_bound hO (fun y => u (y,t)) f hSlice hf w
        (hKO hx) (hClose t ht0 htδ x hx).le
      have hTri : |directionalWordDerivative (fun y => u (y,t)) w x| ≤
          |directionalWordDerivative (fun y => u (y,t)) w x-directionalWordDerivative f w x|+
            |directionalWordDerivative f w x| := by
        convert abs_add_le (directionalWordDerivative (fun y => u (y,t)) w x-directionalWordDerivative f w x)
          (directionalWordDerivative f w x) using 1 <;> ring
      dsimp only [C,W]
      dsimp only [W] at hW
      nlinarith [le_max_left F 0]
    · exact (hPositive t ⟨le_of_not_gt htδ,ht.2⟩ x hx).trans hPC

end Yau.Proofs.F03Aux
