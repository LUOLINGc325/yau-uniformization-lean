import Yau.LeafProofs.L17SchauderSpaceLocal
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalHolderBanachAlgebraAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- A concrete local section, with the norm subsequently scaled by two. -/
structure LocalHolderBanach (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : UniformChartPartition g) (T gamma : ℝ) where
  value : LocalHolderSpace F P T gamma

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : UniformChartPartition g) (T gamma : ℝ)

def valueEquiv : LocalHolderBanach F P T gamma ≃ LocalHolderSpace F P T gamma where
  toFun := LocalHolderBanach.value
  invFun := fun u => ⟨u⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem value_injective : Function.Injective (LocalHolderBanach.value (F := F) (P := P) (T := T) (gamma := gamma)) :=
  (valueEquiv F P T gamma).injective

instance localHolderBanach_addCommGroup : AddCommGroup (LocalHolderBanach F P T gamma) :=
  (valueEquiv F P T gamma).addCommGroup

def valueAddEquiv : LocalHolderBanach F P T gamma ≃+ LocalHolderSpace F P T gamma :=
  { valueEquiv F P T gamma with map_add' := fun _ _ => rfl }

instance localHolderBanach_module : Module ℝ (LocalHolderBanach F P T gamma) :=
  (valueAddEquiv F P T gamma).module ℝ

@[simp] theorem value_zero : (0 : LocalHolderBanach F P T gamma).value=0 := rfl
@[simp] theorem value_add (u v : LocalHolderBanach F P T gamma) : (u+v).value=u.value+v.value := rfl
@[simp] theorem value_neg (u : LocalHolderBanach F P T gamma) : (-u).value=-u.value := rfl
@[simp] theorem value_sub (u v : LocalHolderBanach F P T gamma) : (u-v).value=u.value-v.value := rfl
@[simp] theorem value_smul (c : ℝ) (u : LocalHolderBanach F P T gamma) : (c • u).value=c • u.value := rfl

/-- The scaling is an actual additive bijection into the original complete graph. -/
def scaledValueAddEquiv : LocalHolderBanach F P T gamma ≃+ LocalHolderSpace F P T gamma where
  toFun u := (2 : ℝ) • u.value
  invFun u := ⟨(2 : ℝ)⁻¹ • u⟩
  left_inv := by
    intro u
    apply value_injective F P T gamma
    change (2 : ℝ)⁻¹ • ((2 : ℝ) • u.value)=u.value
    simp only [smul_smul,inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),one_smul]
  right_inv := by
    intro u
    change (2 : ℝ) • ((2 : ℝ)⁻¹ • u)=u
    simp only [smul_smul,mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),one_smul]
  map_add' := by intro u v; exact smul_add (2 : ℝ) u.value v.value

instance localHolderBanach_normedAddCommGroup : NormedAddCommGroup (LocalHolderBanach F P T gamma) :=
  NormedAddCommGroup.induced _ _ (scaledValueAddEquiv F P T gamma).toAddMonoidHom
    (scaledValueAddEquiv F P T gamma).injective

theorem norm_eq_twice (u : LocalHolderBanach F P T gamma) : ‖u‖=2*‖u.value‖ := by
  change ‖(2 : ℝ) • u.value‖=2*‖u.value‖
  rw [norm_smul]
  norm_num

instance localHolderBanach_normedSpace : NormedSpace ℝ (LocalHolderBanach F P T gamma) where
  __ := localHolderBanach_module F P T gamma
  norm_smul_le c u := by
    rw [norm_eq_twice,norm_eq_twice,value_smul,norm_smul]
    exact le_of_eq (by ring)

def scaledValueIsometryEquiv : LocalHolderBanach F P T gamma ≃ᵢ LocalHolderSpace F P T gamma :=
  { (scaledValueAddEquiv F P T gamma).toEquiv with isometry_toFun := fun _ _ => rfl }

instance localHolderBanach_completeSpace [CompleteSpace F] : CompleteSpace (LocalHolderBanach F P T gamma) :=
  (scaledValueIsometryEquiv F P T gamma).completeSpace

def valueLinearEquiv : LocalHolderBanach F P T gamma ≃ₗ[ℝ] LocalHolderSpace F P T gamma :=
  { valueAddEquiv F P T gamma with map_smul' := fun _ _ => rfl }

def valueContinuousLinearEquiv : LocalHolderBanach F P T gamma ≃L[ℝ] LocalHolderSpace F P T gamma :=
  (valueLinearEquiv F P T gamma).toContinuousLinearEquivOfBounds (1/2) 2
    (fun u => by rw [norm_eq_twice]; change ‖u.value‖ ≤ (1/2 : ℝ)*(2*‖u.value‖); linarith)
    (fun u => by change ‖(⟨u⟩ : LocalHolderBanach F P T gamma)‖ ≤ 2*‖u‖; rw [norm_eq_twice])

theorem norm_value_le_half (u : LocalHolderBanach F P T gamma) : ‖u.value‖ ≤ (1/2 : ℝ)*‖u‖ := by
  rw [norm_eq_twice]
  linarith

theorem norm_ofLocal (u : LocalHolderSpace F P T gamma) :
    ‖(⟨u⟩ : LocalHolderBanach F P T gamma)‖=2*‖u‖ := norm_eq_twice F P T gamma _

def evalCLM (q : LocalCylinder P T) : LocalHolderBanach F P T gamma →L[ℝ] F :=
  (localEvalCLM F P T gamma q).comp (valueContinuousLinearEquiv F P T gamma).toContinuousLinearMap

theorem evalCLM_apply (q : LocalCylinder P T) (u : LocalHolderBanach F P T gamma) :
    evalCLM F P T gamma q u=localFun F u.value q := rfl

theorem evalCLM_norm_le_half (q : LocalCylinder P T) : ‖evalCLM F P T gamma q‖ ≤ (1/2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  exact (localValue_norm_le F u.value q).trans (norm_value_le_half F P T gamma u)

end Yau.LeafProofs.L17LocalHolderBanachAlgebraAux
