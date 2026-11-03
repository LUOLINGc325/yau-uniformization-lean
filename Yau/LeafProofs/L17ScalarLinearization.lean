import Yau.LeafProofs.L17Neumann

noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.LeafProofs.L17Aux
open L17NeumannAux
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem subPerturbation_norm_le (e : X≃L[ℝ]Y) (D : X→L[ℝ]Y) :
    ‖-(e.symm.toContinuousLinearMap.comp D)‖≤‖e.symm.toContinuousLinearMap‖*‖D‖ := by
  rw [norm_neg]
  exact ContinuousLinearMap.opNorm_comp_le _ _

variable [CompleteSpace X]

def subPerturbationEquiv (e : X≃L[ℝ]Y) (D : X→L[ℝ]Y)
    (hD : ‖e.symm.toContinuousLinearMap‖*‖D‖<1) : X≃L[ℝ]Y :=
  (neumannEquiv (-(e.symm.toContinuousLinearMap.comp D))
    ((subPerturbation_norm_le e D).trans_lt hD)).trans e

theorem subPerturbationEquiv_apply (e : X≃L[ℝ]Y) (D : X→L[ℝ]Y)
    (hD : ‖e.symm.toContinuousLinearMap‖*‖D‖<1) (x : X) :
    subPerturbationEquiv e D hD x=e x-D x := by
  change e (x+(-(e.symm.toContinuousLinearMap.comp D)) x)=_
  simp only [neg_apply,ContinuousLinearMap.comp_apply,map_add,map_neg,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply,sub_eq_add_neg]

theorem subPerturbationEquiv_symm_eq (e : X≃L[ℝ]Y) (D : X→L[ℝ]Y)
    (hD : ‖e.symm.toContinuousLinearMap‖*‖D‖<1) :
    (subPerturbationEquiv e D hD).symm.toContinuousLinearMap=
      (neumannSeries (-(e.symm.toContinuousLinearMap.comp D))).comp e.symm.toContinuousLinearMap := by
  ext y
  rfl

theorem subPerturbationEquiv_symm_norm_le (e : X≃L[ℝ]Y) (D : X→L[ℝ]Y)
    (hD : ‖e.symm.toContinuousLinearMap‖*‖D‖<1)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*‖D‖≤1/4) :
    ‖(subPerturbationEquiv e D hD).symm.toContinuousLinearMap‖≤
      (4/3)*‖e.symm.toContinuousLinearMap‖ := by
  rw [subPerturbationEquiv_symm_eq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (neumann_norm_le_four_thirds
      ((subPerturbation_norm_le e D).trans hSmall)) (norm_nonneg _))

end Yau.LeafProofs.L17Aux
