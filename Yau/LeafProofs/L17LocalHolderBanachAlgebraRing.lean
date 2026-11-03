import Yau.LeafProofs.L17LocalHolderBanachAlgebraConstants
import Yau.LeafProofs.L17LocalHolderAlgebraBilinear
import Mathlib.Algebra.Ring.InjSurj

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalHolderBanachAlgebraAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17SchauderAux
open Yau.LeafProofs.L17LocalHolderAlgebraAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]
    (P : UniformChartPartition g) (T gamma : ℝ)

theorem multiplication_opNorm_le_one : ‖ContinuousLinearMap.mul ℝ A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  have hInner : ‖ContinuousLinearMap.mul ℝ A a‖ ≤ ‖a‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
    intro b
    exact norm_mul_le a b
  simpa only [one_mul] using hInner

def rawProduct (u v : LocalHolderSpace A P T gamma) : LocalHolderSpace A P T gamma :=
  localBilinearCLM (ContinuousLinearMap.mul ℝ A) u v

theorem rawProduct_norm_le (u v : LocalHolderSpace A P T gamma) :
    ‖rawProduct A P T gamma u v‖ ≤ 2*‖u‖*‖v‖ := by
  have h := localBilinearElement_norm_le (ContinuousLinearMap.mul ℝ A) u v
  exact h.trans (by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (multiplication_opNorm_le_one A) (by norm_num : (0 : ℝ) ≤ 2))

instance localHolderBanach_mul : Mul (LocalHolderBanach A P T gamma) :=
  ⟨fun u v => ⟨rawProduct A P T gamma u.value v.value⟩⟩
instance localHolderBanach_one : One (LocalHolderBanach A P T gamma) := ⟨const A P T gamma 1⟩
instance localHolderBanach_natCast : NatCast (LocalHolderBanach A P T gamma) := ⟨fun m => const A P T gamma (m : A)⟩
instance localHolderBanach_intCast : IntCast (LocalHolderBanach A P T gamma) := ⟨fun m => const A P T gamma (m : A)⟩
instance localHolderBanach_pow : Pow (LocalHolderBanach A P T gamma) ℕ := ⟨fun u m => npowRec m u⟩

@[simp] theorem value_mul (u v : LocalHolderBanach A P T gamma) :
    (u*v).value=rawProduct A P T gamma u.value v.value := rfl

@[simp] theorem mul_apply (u v : LocalHolderBanach A P T gamma) (q : LocalCylinder P T) :
    (u*v) q=u q*v q := rfl
@[simp] theorem one_apply (q : LocalCylinder P T) : (1 : LocalHolderBanach A P T gamma) q=1 := rfl
@[simp] theorem natCast_apply (m : ℕ) (q : LocalCylinder P T) : (m : LocalHolderBanach A P T gamma) q=(m : A) := rfl
@[simp] theorem intCast_apply (m : ℤ) (q : LocalCylinder P T) : (m : LocalHolderBanach A P T gamma) q=(m : A) := rfl

@[simp] theorem pow_apply (u : LocalHolderBanach A P T gamma) (m : ℕ) (q : LocalCylinder P T) :
    (u^m) q=(u q)^m := by
  induction m with
  | zero =>
    change (1 : LocalHolderBanach A P T gamma) q=(u q)^0
    rw [one_apply,pow_zero]
  | succ m ih =>
    change ((u^m)*u) q=(u q)^(m+1)
    rw [mul_apply,ih,pow_succ]

instance localHolderBanach_ring : Ring (LocalHolderBanach A P T gamma) :=
  Function.Injective.ring (fun u : LocalHolderBanach A P T gamma => (u : LocalCylinder P T → A))
    (apply_injective A P T gamma) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u m => funext (pow_apply A P T gamma u m)) (fun _ => rfl) (fun _ => rfl)

theorem norm_mul_le_actual (u v : LocalHolderBanach A P T gamma) : ‖u*v‖ ≤ ‖u‖*‖v‖ := by
  rw [norm_eq_twice,norm_eq_twice,norm_eq_twice,value_mul]
  exact (mul_le_mul_of_nonneg_left (rawProduct_norm_le A P T gamma u.value v.value)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

instance localHolderBanach_normedRing : NormedRing (LocalHolderBanach A P T gamma) where
  __ := localHolderBanach_ring A P T gamma
  __ := localHolderBanach_normedAddCommGroup A P T gamma
  dist_eq u v := dist_eq_norm_neg_add u v
  norm_mul_le := norm_mul_le_actual A P T gamma

theorem const_mul (a b : A) : const A P T gamma (a*b)=const A P T gamma a*const A P T gamma b := by
  apply ext
  intro q
  rfl

theorem const_one : const A P T gamma 1=1 := rfl

theorem norm_one_le_twice : ‖(1 : LocalHolderBanach A P T gamma)‖ ≤ 2*‖(1 : A)‖ :=
  const_norm_le A P T gamma 1

instance localHolderBanach_algebra : Algebra ℝ (LocalHolderBanach A P T gamma) :=
  Algebra.ofModule
    (fun c u v => by apply ext; intro q; exact smul_mul_assoc c (u q) (v q))
    (fun c u v => by apply ext; intro q; exact mul_smul_comm c (u q) (v q))

instance localHolderBanach_normedAlgebra : NormedAlgebra ℝ (LocalHolderBanach A P T gamma) where
  __ := localHolderBanach_algebra A P T gamma
  norm_smul_le := (localHolderBanach_normedSpace A P T gamma).norm_smul_le

end Yau.LeafProofs.L17LocalHolderBanachAlgebraAux
