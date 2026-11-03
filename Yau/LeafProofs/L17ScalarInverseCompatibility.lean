import Yau.LeafProofs.L17SchauderEmbedding
import Yau.LeafProofs.L17ParabolicOperator

/-! Actual scalar operators and their inverses agree under exponent descent. -/

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open L17HolderAux L17SchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem scalarParabolic_weaken (P : UniformChartPartition g) {T α β : ℝ}
    (hT : 0 < T) (hSmall : T ≤ P.radius^2) (hα : α ≤ 1) (hβα : β ≤ α) (hr : P.radius≤1) :
    (scalarParabolicCLM P T β hT hSmall (hβα.trans hα) hr).comp (schauderWeakenCLM P hT hSmall hβα) =
      (weakenCLM P hSmall hβα).comp (scalarParabolicCLM P T α hT hSmall hα hr) := by
  apply ContinuousLinearMap.ext
  intro u
  apply holderFun_injective P T β
  funext q
  change holderFun (scalarParabolicCLM P T β hT hSmall (hβα.trans hα) hr
    (schauderWeakenCLM P hT hSmall hβα u)) q =
    holderFun (weakenCLM P hSmall hβα (scalarParabolicCLM P T α hT hSmall hα hr u)) q
  rw [weakenCLM_value,scalarParabolicCLM_value,scalarParabolicCLM_value,schauderWeakenCLM_function]
  have hTime : timeFun (schauderWeakenCLM P hT hSmall hβα u)=timeFun u := rfl
  rw [hTime]

theorem scalarInverse_weaken (P : UniformChartPartition g) {T α β : ℝ}
    (hT : 0 < T) (hSmall : T ≤ P.radius^2) (hα : α ≤ 1) (hβα : β ≤ α) (hr : P.radius≤1)
    (Sα : SchauderSpace P T α hT ≃L[ℝ] HolderSpace P T α)
    (Sβ : SchauderSpace P T β hT ≃L[ℝ] HolderSpace P T β)
    (hSα : (Sα : SchauderSpace P T α hT →L[ℝ] HolderSpace P T α)=scalarParabolicCLM P T α hT hSmall hα hr)
    (hSβ : (Sβ : SchauderSpace P T β hT →L[ℝ] HolderSpace P T β)=scalarParabolicCLM P T β hT hSmall (hβα.trans hα) hr)
    (f : HolderSpace P T α) :
    schauderWeakenCLM P hT hSmall hβα (Sα.symm f)=Sβ.symm (weakenCLM P hSmall hβα f) := by
  apply Sβ.injective
  rw [Sβ.apply_symm_apply]
  change (Sβ : SchauderSpace P T β hT →L[ℝ] HolderSpace P T β)
    (schauderWeakenCLM P hT hSmall hβα (Sα.symm f)) = _
  rw [hSβ]
  have hComm := congrArg (fun L => L (Sα.symm f)) (scalarParabolic_weaken P hT hSmall hα hβα hr)
  simp only [ContinuousLinearMap.comp_apply] at hComm
  rw [hComm,← hSα]
  exact congrArg (weakenCLM P hSmall hβα) (Sα.apply_symm_apply f)

end Yau.LeafProofs.L17Aux
