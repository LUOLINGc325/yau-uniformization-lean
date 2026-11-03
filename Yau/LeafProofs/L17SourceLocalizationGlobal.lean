import Yau.LeafProofs.L17SourceLocalizationBounds

/-! The genuine support collar controls mixed inside/outside pairs. The
result is a uniform estimate on the entire coordinate space and all real times. -/

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L17SourceLocalizationAux
open L17Aux L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem rawParabolicDistance_symm (q r : Yau.Parabolic.Point n) :
    Yau.Parabolic.parabolicDistance r q = Yau.Parabolic.parabolicDistance q r := by
  simp only [Yau.Parabolic.parabolicDistance]
  rw [norm_sub_rev r.1 q.1, abs_sub_comm r.2 q.2]

theorem localizedSource_far_bound (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (hγ : 0 ≤ γ) (f : HolderSpace P T γ) (p : P.centers)
    (q r : Yau.Parabolic.Point n) (hq : q.1 ∉ ball (0 : ComplexVector n) P.radius) :
    |localizedSource P T hT f p r| ≤
      (2 : ℝ) ^ γ * ‖f‖ * (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ := by
  have hDγ : 0 ≤ (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ := Real.rpow_nonneg
    (div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le) _
  by_cases hs : localizedSource P T hT f p r = 0
  · rw [hs, abs_zero]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (norm_nonneg _)) hDγ
  have hr : r.1 ∈ ball (0 : ComplexVector n) P.radius := by
    by_contra hn
    exact hs (by simp only [localizedSource, hn, ite_false])
  have hw : P.weight p (P.charts.chart p r.1) ≠ 0 := by
    intro hn
    exact hs (by simp only [localizedSource, hr, ite_true, hn, zero_mul])
  have hhalf := weight_coordinate_mem_closedBall P p hr hw
  have hnormr : ‖r.1‖ ≤ P.radius / 2 := by simpa only [mem_closedBall, dist_zero_right] using hhalf
  have hnormq : P.radius ≤ ‖q.1‖ := by
    have hh : ¬ ‖q.1‖ < P.radius := by simpa only [mem_ball, dist_zero_right] using hq
    exact not_lt.mp hh
  have hTri : ‖q.1‖ ≤ ‖q.1-r.1‖ + ‖r.1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (q.1-r.1) r.1
  have hsep : (1 / 2 : ℝ) ≤ Yau.Parabolic.parabolicDistance q r / P.radius := by
    apply (le_div_iff₀ P.radius_pos).mpr
    dsimp only [Yau.Parabolic.parabolicDistance]
    nlinarith [Real.sqrt_nonneg |q.2-r.2|]
  have hPow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hsep hγ
  have hUnit : (2 : ℝ) ^ γ * (1 / 2 : ℝ) ^ γ = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hOne : 1 ≤ (2 : ℝ) ^ γ * (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ :=
    hUnit.symm.le.trans (mul_le_mul_of_nonneg_left hPow (Real.rpow_nonneg (by norm_num) _))
  calc
    _ ≤ ‖f‖ := localizedSource_abs_le_norm P T hT f p r
    _ = ‖f‖ * 1 := by ring
    _ ≤ ‖f‖ * ((2 : ℝ) ^ γ * (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ) :=
      mul_le_mul_of_nonneg_left hOne (norm_nonneg f)
    _ = _ := by ring

def sourceHolderConstant (K γ : ℝ) : ℝ := (2 * K + 1) * (2 : ℝ) ^ γ

theorem sourceHolderConstant_bounds {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) :
    0 ≤ sourceHolderConstant K γ ∧ 2 * K ≤ sourceHolderConstant K γ ∧
      (2 : ℝ) ^ γ ≤ sourceHolderConstant K γ := by
  have hp : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγ
  have hp0 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) γ
  unfold sourceHolderConstant
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith [mul_nonneg hK (sub_nonneg.mpr hp)]
  · nlinarith [mul_nonneg hK hp0]

theorem localizedSource_global_difference (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K) (f η : HolderSpace P T γ) (p : P.centers)
    (hη : ∀ x, holderFun η x = P.weight p x.1) (hηK : ‖η‖ ≤ K)
    (q r : Yau.Parabolic.Point n) :
    |localizedSource P T hT f p r - localizedSource P T hT f p q| ≤
      sourceHolderConstant K γ * ‖f‖ * (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ := by
  have hC := sourceHolderConstant_bounds hK hγ
  have hD : 0 ≤ (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ := Real.rpow_nonneg
    (div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le) _
  have hCoeff (a : ℝ) (ha : a ≤ sourceHolderConstant K γ) :
      a * ‖f‖ * (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ ≤
      sourceHolderConstant K γ * ‖f‖ * (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hD
  by_cases hq : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · by_cases hr : r.1 ∈ ball (0 : ComplexVector n) P.radius
    · exact (localizedSource_inside_difference P T hT hγ hK f η p hη hηK q r hq hr).trans (hCoeff _ hC.2.1)
    · have hZero : localizedSource P T hT f p r = 0 := by simp only [localizedSource, hr, ite_false]
      rw [hZero, zero_sub, abs_neg]
      have hh := localizedSource_far_bound P T hT hγ f p r q hr
      rw [rawParabolicDistance_symm] at hh
      exact hh.trans (hCoeff _ hC.2.2)
  · have hZero : localizedSource P T hT f p q = 0 := by simp only [localizedSource, hq, ite_false]
    rw [hZero, sub_zero]
    exact (localizedSource_far_bound P T hT hγ f p q r hq).trans (hCoeff _ hC.2.2)

end Yau.LeafProofs.L17SourceLocalizationAux
