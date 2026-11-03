import Yau.LeafProofs.L17LocalHolderBanachAlgebra
import Yau.LeafProofs.L17HolderEmbedding

open Set Metric
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux

theorem time_difference_holder_bound {T γ a d : ℝ} (hT : 0<T) (hγ : 0≤γ)
    (hγ2 : γ≤2) (ha : 0≤a) (haT : a≤T) (had : Real.sqrt a≤d) :
    a≤T^(1-γ/2)*d^γ := by
  by_cases hz : a=0
  · rw [hz]
    exact mul_nonneg (Real.rpow_pos_of_pos hT _).le
      (Real.rpow_nonneg ((Real.sqrt_nonneg a).trans had) _)
  · have hapos : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
    have hsplit : a=a^(1-γ/2)*(Real.sqrt a)^γ := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul ha,← Real.rpow_add hapos]
      have he : 1-γ/2+(1/2:ℝ)*γ=1 := by ring
      rw [he,Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul (Real.rpow_le_rpow ha haT (by linarith))
      (Real.rpow_le_rpow (Real.sqrt_nonneg a) had hγ) (Real.rpow_nonneg (Real.sqrt_nonneg a) γ)
      (Real.rpow_nonneg hT.le _)

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem weighted_time_difference (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hγ : 0≤γ) (hγ2 : γ≤2) (hr : P.radius≤1) (i : ChartPairs P T) :
    ‖pairWeight P T γ i • ((i.2.val.2.2 : ℝ)-(i.2.val.1.2 : ℝ))‖ ≤ T^(1-γ/2) := by
  let a : ℝ := |(i.2.val.2.2 : ℝ)-(i.2.val.1.2 : ℝ)|
  let d := parabolicDistance i.2.val.1 i.2.val.2
  have hd : 0<d := parabolicDistance_pos_of_ne i.2.property
  have haT : a≤T := by
    dsimp only [a]
    apply abs_le.mpr
    constructor <;> linarith [i.2.val.1.2.property.1,i.2.val.1.2.property.2,
      i.2.val.2.2.property.1,i.2.val.2.2.property.2]
  have had : Real.sqrt a≤d := by
    dsimp only [a,d,parabolicDistance]
    rw [abs_sub_comm]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hdiff := time_difference_holder_bound hT hγ hγ2 (abs_nonneg _) haT had
  have hρ : P.radius^γ≤1 := Real.rpow_le_one P.radius_pos.le hr hγ
  rw [norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (pairWeight_pos P T γ i)]
  change (P.radius^γ/d^γ)*a≤_
  calc
    _ ≤ (P.radius^γ/d^γ)*(T^(1-γ/2)*d^γ) :=
      mul_le_mul_of_nonneg_left hdiff (div_nonneg (Real.rpow_nonneg P.radius_pos.le _) (Real.rpow_nonneg hd.le _))
    _ = P.radius^γ*T^(1-γ/2) := by field_simp [(Real.rpow_pos_of_pos hd γ).ne']
    _ ≤ T^(1-γ/2) := (mul_le_mul_of_nonneg_right hρ (Real.rpow_nonneg hT.le _)).trans_eq (one_mul _)

theorem local_time_continuous (P : UniformChartPartition g) (T : ℝ) :
    Continuous (fun q : LocalCylinder P T => (q.2.2 : ℝ)) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact continuous_subtype_val.comp continuous_snd

def timeFactorHolder (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hγ : 0≤γ) (hγ2 : γ≤2) (hr : P.radius≤1) : LocalHolderSpace ℝ P T γ :=
  localOfBounds ℝ P T γ (fun q => (q.2.2 : ℝ)) (local_time_continuous P T)
    T (T^(1-γ/2)) (fun q => by simpa only [Real.norm_eq_abs,abs_of_nonneg q.2.2.property.1] using q.2.2.property.2)
    (weighted_time_difference P hT hγ hγ2 hr)

theorem timeFactorHolder_norm_le (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hTone : T≤1) (hγ : 0≤γ) (hγ2 : γ≤2) (hr : P.radius≤1) :
    ‖timeFactorHolder P hT hγ hγ2 hr‖ ≤ T^(1-γ/2) := by
  apply (localOfBounds_norm_le ℝ P T γ _ _ _ _ hT.le (Real.rpow_nonneg hT.le _) _ _).trans
  apply max_le
  · simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hT hTone (show 1-γ/2≤1 by linarith))
  · exact le_rfl

def timeFactorBanach (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hγ : 0≤γ) (hγ2 : γ≤2) (hr : P.radius≤1) : LocalHolderBanach ℝ P T γ :=
  ⟨timeFactorHolder P hT hγ hγ2 hr⟩

theorem timeFactorBanach_value (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hγ : 0≤γ) (hγ2 : γ≤2) (hr : P.radius≤1) (q : LocalCylinder P T) :
    timeFactorBanach P hT hγ hγ2 hr q=(q.2.2 : ℝ) := rfl

theorem timeFactorBanach_norm_le (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hTone : T≤1) (hγ : 0≤γ) (hγ2 : γ≤2) (hr : P.radius≤1) :
    ‖timeFactorBanach P hT hγ hγ2 hr‖ ≤ 2*T^(1-γ/2) := by
  rw [norm_eq_twice]
  exact mul_le_mul_of_nonneg_left (timeFactorHolder_norm_le P hT hTone hγ hγ2 hr) (by norm_num)

end Yau.LeafProofs.L17Aux
