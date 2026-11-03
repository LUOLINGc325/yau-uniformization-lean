import Yau.LeafProofs.L17HolderSpace

/-! The actual same-cylinder embedding from a larger to a smaller Holder exponent. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17HolderAux

open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem parabolicDistance_le_three_radius
    (P : UniformChartPartition g) {T : ℝ} (hT : T ≤ P.radius ^ 2)
    (q r : ChartCylinder P T) : parabolicDistance q r ≤ 3 * P.radius := by
  have hq : ‖(q.1 : ComplexVector n)‖ < P.radius := by
    simpa only [mem_ball, dist_zero_right] using q.1.property
  have hr : ‖(r.1 : ComplexVector n)‖ < P.radius := by
    simpa only [mem_ball, dist_zero_right] using r.1.property
  have habs : |(q.2 : ℝ) - (r.2 : ℝ)| ≤ T := by
    apply abs_sub_le_iff.mpr
    constructor <;> linarith [q.2.property.1, q.2.property.2, r.2.property.1, r.2.property.2]
  have hs := Real.sqrt_le_sqrt (habs.trans hT)
  rw [Real.sqrt_sq P.radius_pos.le] at hs
  unfold parabolicDistance
  linarith [norm_sub_le (q.1 : ComplexVector n) (r.1 : ComplexVector n)]

theorem pairWeight_weaken_le
    (P : UniformChartPartition g) {T α β : ℝ} (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (i : ChartPairs P T) : pairWeight P T β i ≤ (3 : ℝ) ^ (α - β) * pairWeight P T α i := by
  let d := parabolicDistance i.2.val.1 i.2.val.2
  have hd : 0 < d := parabolicDistance_pos_of_ne i.2.property
  have hr := P.radius_pos
  have hratio : (d / P.radius) ^ (α - β) ≤ (3 : ℝ) ^ (α - β) :=
    Real.rpow_le_rpow (by positivity)
      ((div_le_iff₀ hr).mpr (parabolicDistance_le_three_radius P hT _ _))
      (sub_nonneg.mpr hβα)
  have heq : pairWeight P T β i = (d / P.radius) ^ (α - β) * pairWeight P T α i := by
    change P.radius ^ β / d ^ β = (d / P.radius) ^ (α - β) * (P.radius ^ α / d ^ α)
    rw [Real.div_rpow hd.le hr.le, Real.rpow_sub hd, Real.rpow_sub hr]
    have hdα := (Real.rpow_pos_of_pos hd α).ne'
    have hdβ := (Real.rpow_pos_of_pos hd β).ne'
    have hrα := (Real.rpow_pos_of_pos hr α).ne'
    have hrβ := (Real.rpow_pos_of_pos hr β).ne'
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right hratio (pairWeight_pos P T α i).le

theorem weighted_difference_weaken_le
    (P : UniformChartPartition g) {T α β : ℝ} (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (u : HolderSpace P T α) (i : ChartPairs P T) :
    |pairWeight P T β i * (holderFun u (chartRight P T i) - holderFun u (chartLeft P T i))| ≤
      (3 : ℝ) ^ (α - β) * ‖u‖ := by
  have h := weighted_difference_abs_le_norm u i
  rw [abs_mul, abs_of_pos (pairWeight_pos P T α i)] at h
  rw [abs_mul, abs_of_pos (pairWeight_pos P T β i)]
  calc
    _ ≤ ((3 : ℝ) ^ (α - β) * pairWeight P T α i) *
        |holderFun u (chartRight P T i) - holderFun u (chartLeft P T i)| :=
      mul_le_mul_of_nonneg_right (pairWeight_weaken_le P hT hβα i) (abs_nonneg _)
    _ = (3 : ℝ) ^ (α - β) * (pairWeight P T α i *
        |holderFun u (chartRight P T i) - holderFun u (chartLeft P T i)|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_pos_of_pos (by norm_num) _).le

def weakenElement (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : HolderSpace P T α) : HolderSpace P T β :=
  ofBounds P T β (holderFun u) u.val.1.continuous ‖u‖ ((3 : ℝ) ^ (α - β) * ‖u‖)
    (value_abs_le_norm u) (weighted_difference_weaken_le P hT hβα u)

theorem weakenElement_value (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : HolderSpace P T α) :
    holderFun (weakenElement P hT hβα u) = holderFun u := rfl

theorem weakenElement_norm_le (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : HolderSpace P T α) :
    ‖weakenElement P hT hβα u‖ ≤ (3 : ℝ) ^ (α - β) * ‖u‖ := by
  have hK := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) (sub_nonneg.mpr hβα)
  apply (ofBounds_norm_le P T β (holderFun u) u.val.1.continuous ‖u‖
    ((3 : ℝ) ^ (α - β) * ‖u‖) (norm_nonneg _) (by positivity)
    (value_abs_le_norm u) (weighted_difference_weaken_le P hT hβα u)).trans
  exact max_le (by nlinarith [norm_nonneg u]) le_rfl

def weakenLinearMap (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) : HolderSpace P T α →ₗ[ℝ] HolderSpace P T β where
  toFun := weakenElement P hT hβα
  map_add' u v := by
    apply holderFun_injective P T β
    ext x
    rfl
  map_smul' c u := by
    apply holderFun_injective P T β
    ext x
    rfl

def weakenCLM (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) : HolderSpace P T α →L[ℝ] HolderSpace P T β :=
  (weakenLinearMap P hT hβα).mkContinuous ((3 : ℝ) ^ (α - β))
    (weakenElement_norm_le P hT hβα)

theorem weakenCLM_value (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : HolderSpace P T α) :
    holderFun (weakenCLM P hT hβα u) = holderFun u := rfl

theorem weakenCLM_opNorm_le (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    ‖weakenCLM P hT hβα‖ ≤ (3 : ℝ) ^ (α - β) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_pos_of_pos (by norm_num) _).le
    (weakenElement_norm_le P hT hβα)

theorem weakenCLM_injective (P : UniformChartPartition g) {T α β : ℝ}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) : Function.Injective (weakenCLM P hT hβα) := by
  intro u v huv
  apply holderFun_injective P T α
  exact congrArg (fun w : HolderSpace P T β => holderFun w) huv

def alphaBetaHolderEmbedding (P : UniformChartPartition g) {T : ℝ}
    (hT : T ≤ P.radius ^ 2) : HolderSpace P T (1 / 2) →L[ℝ] HolderSpace P T (1 / 4) :=
  weakenCLM P hT (by norm_num)

end Yau.LeafProofs.L17HolderAux
