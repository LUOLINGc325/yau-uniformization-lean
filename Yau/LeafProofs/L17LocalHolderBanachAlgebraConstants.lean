import Yau.LeafProofs.L17LocalHolderBanachAlgebraBasic

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalHolderBanachAlgebraAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : UniformChartPartition g) (T gamma : ℝ)

instance localHolderBanach_coeFun : CoeFun (LocalHolderBanach F P T gamma) (fun _ => LocalCylinder P T → F) :=
  ⟨fun u => localFun F u.value⟩

theorem apply_injective : Function.Injective (fun u : LocalHolderBanach F P T gamma => (u : LocalCylinder P T → F)) := by
  intro u v huv
  apply value_injective F P T gamma
  exact localFun_injective F P T gamma huv

@[ext] theorem ext (u v : LocalHolderBanach F P T gamma) (h : ∀ q, u q=v q) : u=v :=
  apply_injective F P T gamma (funext h)

@[simp] theorem zero_apply (q : LocalCylinder P T) : (0 : LocalHolderBanach F P T gamma) q=0 := rfl
@[simp] theorem add_apply (u v : LocalHolderBanach F P T gamma) (q : LocalCylinder P T) : (u+v) q=u q+v q := rfl
@[simp] theorem neg_apply (u : LocalHolderBanach F P T gamma) (q : LocalCylinder P T) : (-u) q=-(u q) := rfl
@[simp] theorem sub_apply (u v : LocalHolderBanach F P T gamma) (q : LocalCylinder P T) : (u-v) q=u q-v q := rfl
@[simp] theorem smul_apply (c : ℝ) (u : LocalHolderBanach F P T gamma) (q : LocalCylinder P T) : (c • u) q=c • u q := rfl
@[simp] theorem nsmul_apply (c : ℕ) (u : LocalHolderBanach F P T gamma) (q : LocalCylinder P T) : (c • u) q=c • u q := rfl
@[simp] theorem zsmul_apply (c : ℤ) (u : LocalHolderBanach F P T gamma) (q : LocalCylinder P T) : (c • u) q=c • u q := rfl

/-- Constants are actual members of the local value/quotient graph, even
when the local cylinder is empty. -/
def localConst (a : F) : LocalHolderSpace F P T gamma :=
  localOfBounds F P T gamma (fun _ => a) continuous_const ‖a‖ 0
    (fun _ => le_rfl) (fun _ => by simp only [sub_self,smul_zero,norm_zero,le_refl])

theorem localConst_value (a : F) (q : LocalCylinder P T) : localFun F (localConst F P T gamma a) q=a := rfl

theorem localConst_norm_le (a : F) : ‖localConst F P T gamma a‖ ≤ ‖a‖ := by
  have h := localOfBounds_norm_le F P T gamma (fun _ => a) continuous_const ‖a‖ 0
    (norm_nonneg a) le_rfl (fun _ => le_rfl)
    (fun _ => by simp only [sub_self,smul_zero,norm_zero,le_refl])
  simpa only [localConst,max_eq_left (norm_nonneg a)] using h

def const (a : F) : LocalHolderBanach F P T gamma := ⟨localConst F P T gamma a⟩

@[simp] theorem const_apply (a : F) (q : LocalCylinder P T) : const F P T gamma a q=a := rfl

theorem const_zero : const F P T gamma 0=0 := by apply ext; intro q; rfl
theorem const_add (a b : F) : const F P T gamma (a+b)=const F P T gamma a+const F P T gamma b := by
  apply ext; intro q; rfl
theorem const_smul (c : ℝ) (a : F) : const F P T gamma (c • a)=c • const F P T gamma a := by
  apply ext; intro q; rfl

theorem const_norm_le (a : F) : ‖const F P T gamma a‖ ≤ 2*‖a‖ := by
  rw [norm_eq_twice]
  exact mul_le_mul_of_nonneg_left (localConst_norm_le F P T gamma a) (by norm_num)

def constLinearMap : F →ₗ[ℝ] LocalHolderBanach F P T gamma where
  toFun := const F P T gamma
  map_add' := const_add F P T gamma
  map_smul' := const_smul F P T gamma

def constCLM : F →L[ℝ] LocalHolderBanach F P T gamma :=
  (constLinearMap F P T gamma).mkContinuous 2 (const_norm_le F P T gamma)

theorem constCLM_apply (a : F) : constCLM F P T gamma a=const F P T gamma a := rfl
theorem constCLM_opNorm_le : ‖constCLM F P T gamma‖ ≤ 2 :=
  (constLinearMap F P T gamma).mkContinuous_norm_le (by norm_num) (const_norm_le F P T gamma)

end Yau.LeafProofs.L17LocalHolderBanachAlgebraAux
