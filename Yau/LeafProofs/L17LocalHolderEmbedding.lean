import Yau.LeafProofs.L17SchauderSpaceLocal
import Yau.LeafProofs.L17HolderEmbedding

/-! Exponent descent for the actual finite-dimensional local jet Holder graph. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17SchauderAux

open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem local_weighted_difference_weaken_le
    (P : UniformChartPartition g) {T α β : ℝ} (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (u : LocalHolderSpace F P T α) (i : ChartPairs P T) :
    ‖pairWeight P T β i • (localFun F u (localRight P T i) -
      localFun F u (localLeft P T i))‖ ≤ (3 : ℝ) ^ (α - β) * ‖u‖ := by
  have h := localWeighted_difference_norm_le F u i
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pairWeight_pos P T α i)] at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pairWeight_pos P T β i)]
  calc
    _ ≤ ((3 : ℝ) ^ (α - β) * pairWeight P T α i) *
        ‖localFun F u (localRight P T i) - localFun F u (localLeft P T i)‖ :=
      mul_le_mul_of_nonneg_right (pairWeight_weaken_le P hT hβα i) (norm_nonneg _)
    _ = (3 : ℝ) ^ (α - β) * (pairWeight P T α i *
        ‖localFun F u (localRight P T i) - localFun F u (localLeft P T i)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_pos_of_pos (by norm_num) _).le

def localWeakenElement (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : LocalHolderSpace F P T α) :
    LocalHolderSpace F P T β :=
  localOfBounds F P T β (localFun F u) u.val.1.continuous ‖u‖
    ((3 : ℝ) ^ (α - β) * ‖u‖) (localValue_norm_le F u)
    (local_weighted_difference_weaken_le F P hT hβα u)

theorem localWeakenElement_value (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : LocalHolderSpace F P T α) :
    localFun F (localWeakenElement F P hT hβα u) = localFun F u := rfl

theorem localWeakenElement_norm_le (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : LocalHolderSpace F P T α) :
    ‖localWeakenElement F P hT hβα u‖ ≤ (3 : ℝ) ^ (α - β) * ‖u‖ := by
  have hK := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) (sub_nonneg.mpr hβα)
  apply (localOfBounds_norm_le F P T β (localFun F u) u.val.1.continuous ‖u‖
    ((3 : ℝ) ^ (α - β) * ‖u‖) (norm_nonneg _) (by positivity)
    (localValue_norm_le F u) (local_weighted_difference_weaken_le F P hT hβα u)).trans
  exact max_le (by nlinarith [norm_nonneg u]) le_rfl

def localWeakenLinearMap (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    LocalHolderSpace F P T α →ₗ[ℝ] LocalHolderSpace F P T β where
  toFun := localWeakenElement F P hT hβα
  map_add' u v := by
    apply localFun_injective F P T β
    ext q
    rfl
  map_smul' c u := by
    apply localFun_injective F P T β
    ext q
    rfl

def localWeakenCLM (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    LocalHolderSpace F P T α →L[ℝ] LocalHolderSpace F P T β :=
  (localWeakenLinearMap F P hT hβα).mkContinuous ((3 : ℝ) ^ (α - β))
    (localWeakenElement_norm_le F P hT hβα)

theorem localWeakenCLM_value (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : LocalHolderSpace F P T α) :
    localFun F (localWeakenCLM F P hT hβα u) = localFun F u := rfl

theorem localWeakenCLM_opNorm_le (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    ‖localWeakenCLM F P hT hβα‖ ≤ (3 : ℝ) ^ (α - β) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_pos_of_pos (by norm_num) _).le
    (localWeakenElement_norm_le F P hT hβα)

theorem localWeakenCLM_injective (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    Function.Injective (localWeakenCLM F P hT hβα) := by
  intro u v huv
  apply localFun_injective F P T α
  exact congrArg (fun w : LocalHolderSpace F P T β => localFun F w) huv

end Yau.LeafProofs.L17SchauderAux
