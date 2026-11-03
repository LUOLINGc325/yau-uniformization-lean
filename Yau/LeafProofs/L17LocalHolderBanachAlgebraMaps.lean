import Yau.LeafProofs.L17LocalHolderBanachAlgebraRing

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalHolderBanachAlgebraAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]
    (P : UniformChartPartition g) (T gamma : ℝ)

theorem algebraMap_apply (r : ℝ) (q : LocalCylinder P T) :
    (algebraMap ℝ (LocalHolderBanach A P T gamma) r) q=algebraMap ℝ A r := by
  change (r • (1 : LocalHolderBanach A P T gamma)) q=algebraMap ℝ A r
  rw [smul_apply,one_apply]
  simp only [Algebra.smul_def,mul_one]

def evalAlgHom (q : LocalCylinder P T) : LocalHolderBanach A P T gamma →ₐ[ℝ] A where
  toFun u := u q
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  commutes' := fun r => algebraMap_apply A P T gamma r q

theorem evalAlgHom_apply (q : LocalCylinder P T) (u : LocalHolderBanach A P T gamma) :
    evalAlgHom A P T gamma q u=u q := rfl

theorem evalCLM_mul (q : LocalCylinder P T) (u v : LocalHolderBanach A P T gamma) :
    evalCLM A P T gamma q (u*v)=evalCLM A P T gamma q u*evalCLM A P T gamma q v := rfl

theorem evalCLM_one (q : LocalCylinder P T) : evalCLM A P T gamma q 1=1 := rfl

def constAlgHom : A →ₐ[ℝ] LocalHolderBanach A P T gamma where
  toFun := const A P T gamma
  map_one' := const_one A P T gamma
  map_mul' := const_mul A P T gamma
  map_zero' := const_zero A P T gamma
  map_add' := const_add A P T gamma
  commutes' := by
    intro r
    apply ext
    intro q
    exact (algebraMap_apply A P T gamma r q).symm

theorem constAlgHom_apply (a : A) : constAlgHom A P T gamma a=const A P T gamma a := rfl

theorem algebraMap_eq_const (r : ℝ) :
    algebraMap ℝ (LocalHolderBanach A P T gamma) r=const A P T gamma (algebraMap ℝ A r) := by
  apply ext
  intro q
  exact algebraMap_apply A P T gamma r q

theorem eval_const (q : LocalCylinder P T) (a : A) :
    evalAlgHom A P T gamma q (constAlgHom A P T gamma a)=a := rfl

theorem valueContinuousLinearEquiv_opNorm_le_half :
    ‖(valueContinuousLinearEquiv A P T gamma).toContinuousLinearMap‖ ≤ (1/2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  exact norm_value_le_half A P T gamma u

theorem valueContinuousLinearEquiv_symm_opNorm_le_two :
    ‖(valueContinuousLinearEquiv A P T gamma).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  exact (norm_ofLocal A P T gamma u).le

theorem valueContinuousLinearEquiv_apply (u : LocalHolderBanach A P T gamma) :
    valueContinuousLinearEquiv A P T gamma u=u.value := rfl

theorem valueContinuousLinearEquiv_symm_apply (u : LocalHolderSpace A P T gamma) :
    (valueContinuousLinearEquiv A P T gamma).symm u=(⟨u⟩ : LocalHolderBanach A P T gamma) := rfl

end Yau.LeafProofs.L17LocalHolderBanachAlgebraAux
