import Yau.Proofs.F03ParabolicC2
import Yau.Proofs.F03DirectionalTensor

/-! Actual spatial derivative words retain joint smoothness and compact positive-time bounds. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem joint_spatial_word_contDiffOn (u : E × ℝ → ℝ) {Q : Set (E × ℝ)}
    (hQ : IsOpen Q) (hu : ContDiffOn ℝ ∞ u Q) (w : List E) :
    ContDiffOn ℝ ∞ (fun p => directionalWordDerivative (fun x => u (x,p.2)) w p.1) Q := by
  induction w with
  | nil => exact hu
  | cons v w ih =>
    intro p hp
    have h := joint_spatial_fderiv_contDiffAt (m := ∞) (ih.contDiffAt (hQ.mem_nhds hp))
    exact (h.clm_apply contDiffAt_const).contDiffWithinAt

theorem compact_positive_spatial_word_bound (u : E × ℝ → ℝ) {O : Set E}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioi 0))
    (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    {δ R : ℝ} (hδ : 0 < δ) (w : List E) :
    ∃ C : ℝ,0 < C ∧ ∀ t ∈ Icc δ R,∀ x ∈ K,
      |directionalWordDerivative (fun y => u (y,t)) w x| ≤ C := by
  have hSub : K ×ˢ Icc δ R ⊆ O ×ˢ Ioi 0 :=
    fun p hp => ⟨hKO hp.1,hδ.trans_le hp.2.1⟩
  have hc := (joint_spatial_word_contDiffOn u (hO.prod isOpen_Ioi) hu w).continuousOn.mono hSub
  obtain ⟨C,hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,fun t ht x hx => ?_⟩
  have hh : |directionalWordDerivative (fun y => u (y,t)) w x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (x,t) ⟨hx,ht⟩
  exact hh.trans (by linarith [le_max_left C 0])

theorem spatial_word_difference_le_of_tensor_bound {O : Set E} (hO : IsOpen O)
    (u f : E → ℝ) (hu : ContDiffOn ℝ ∞ u O) (hf : ContDiffOn ℝ ∞ f O)
    (w : List E) {x : E} (hx : x ∈ O) {ε : ℝ}
    (hSmall : ‖iteratedFDeriv ℝ w.length (fun y => u y-f y) x‖ ≤ ε) :
    |directionalWordDerivative u w x-directionalWordDerivative f w x| ≤
      ε*∏ i : Fin w.length,‖w.get i‖ := by
  have hEval : directionalWordDerivative u w x-directionalWordDerivative f w x=
      iteratedFDeriv ℝ w.length (fun y => u y-f y) x (w.get) := by
    change directionalWordDerivative u w x-directionalWordDerivative f w x=
      iteratedFDeriv ℝ w.length (u-f) x (w.get)
    rw [iteratedFDeriv_sub_apply
      ((hu.contDiffAt (hO.mem_nhds hx)).of_le (by simp))
      ((hf.contDiffAt (hO.mem_nhds hx)).of_le (by simp)),ContinuousMultilinearMap.sub_apply,
      iteratedFDeriv_eq_directionalWord hO hu _ _ hx,
      iteratedFDeriv_eq_directionalWord hO hf _ _ hx,List.ofFn_get]
  rw [hEval,← Real.norm_eq_abs]
  exact (ContinuousMultilinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hSmall (Finset.prod_nonneg (fun i _ => norm_nonneg _)))

end Yau.Proofs.F03Aux
