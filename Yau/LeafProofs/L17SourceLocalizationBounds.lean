import Yau.LeafProofs.L17SourceLocalizationBasic

/-! The actual localized source is a selected-chart product, with true
uniform value and interior parabolic difference bounds. -/

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L17SourceLocalizationAux
open L17Aux L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem localizedSource_abs_le_norm (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : ComplexVector n × ℝ) :
    |localizedSource P T hT f p q| ≤ ‖f‖ := by
  by_cases hq : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · rw [localizedSource, if_pos hq, abs_mul, abs_of_nonneg (P.weight_nonneg p _)]
    exact (mul_le_mul (P.weight_le_one p _) (value_abs_le_norm f _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  · simp only [localizedSource, hq, ite_false, abs_zero]
    exact norm_nonneg _

theorem localizedSource_inside_eq_product (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f η : HolderSpace P T γ) (p : P.centers)
    (hη : ∀ x, holderFun η x = P.weight p x.1)
    (q : ComplexVector n × ℝ) (hq : q.1 ∈ ball (0 : ComplexVector n) P.radius) :
    localizedSource P T hT f p q = holderFun (productElement η f)
      (chartPoint P T p (⟨q.1,hq⟩,timeClamp T hT q.2)) := by
  simp only [localizedSource, hq, ite_true, productElement_value, hη, chartPoint]

theorem localizedSource_inside_difference (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K) (f η : HolderSpace P T γ) (p : P.centers)
    (hη : ∀ x, holderFun η x = P.weight p x.1) (hηK : ‖η‖ ≤ K)
    (q r : Yau.Parabolic.Point n)
    (hq : q.1 ∈ ball (0 : ComplexVector n) P.radius) (hr : r.1 ∈ ball (0 : ComplexVector n) P.radius) :
    |localizedSource P T hT f p r - localizedSource P T hT f p q| ≤
      2 * K * ‖f‖ * (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ := by
  let cq : ChartCylinder P T := (⟨q.1,hq⟩,timeClamp T hT q.2)
  let cr : ChartCylinder P T := (⟨r.1,hr⟩,timeClamp T hT r.2)
  let u := productElement η f
  have hNorm : ‖u‖ ≤ 2 * K * ‖f‖ := (productElement_norm_le η f).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηK (by norm_num)) (norm_nonneg _)))
  have hD : L17HolderAux.parabolicDistance cq cr ≤ Yau.Parabolic.parabolicDistance q r := by
    change ‖q.1-r.1‖ + Real.sqrt |(timeClamp T hT q.2 : ℝ)-(timeClamp T hT r.2 : ℝ)| ≤
      ‖q.1-r.1‖ + Real.sqrt |q.2-r.2|
    exact add_le_add (le_refl _) (timeClamp_sqrt_abs_sub_le T hT r.2 q.2)
  have hDq : 0 ≤ L17HolderAux.parabolicDistance cq cr := by
    dsimp [L17HolderAux.parabolicDistance]
    positivity
  have hDr : 0 ≤ Yau.Parabolic.parabolicDistance q r := by
    dsimp [Yau.Parabolic.parabolicDistance]
    positivity
  rw [localizedSource_inside_eq_product P T hT f η p hη r hr,
    localizedSource_inside_eq_product P T hT f η p hη q hq]
  change |holderFun u (chartPoint P T p cr) - holderFun u (chartPoint P T p cq)| ≤ _
  by_cases hne : cq ≠ cr
  · exact (chart_difference_bound u p cq cr hne).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg hDq P.radius_pos.le)
        (div_le_div_of_nonneg_right hD P.radius_pos.le) hγ) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hNorm (Real.rpow_nonneg (div_nonneg hDr P.radius_pos.le) _)))
  · have he : cq = cr := not_ne_iff.mp hne
    rw [he, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) (norm_nonneg f))
      (Real.rpow_nonneg (div_nonneg hDr P.radius_pos.le) _)

end Yau.LeafProofs.L17SourceLocalizationAux
