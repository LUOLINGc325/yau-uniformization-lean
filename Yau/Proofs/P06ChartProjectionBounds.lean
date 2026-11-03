import Yau.Proofs.P06FormDomain

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

def chartFunctional (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (A : RealForm M k) (z : ComplexVector n) : ℝ := φ z * L (chartForm A x z)

theorem chartFunctional_memLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    MemLp (chartFunctional x φ L A) 2 (lebesgueC n) := by
  have hm := L.comp_memLp' (HodgeDivergenceWeak.chart_cutoff_memLp g μ hμ A hA x φ hφ hcφ hφO)
  apply hm.ae_eq
  filter_upwards [] with z
  by_cases hz : z ∈ chartTarget x
  · simp only [Function.comp_def, chartFormPullbackZero, ite_eq_left hz, map_smul,
      smul_eq_mul, chartFunctional]
  · have hzφ : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
    simp only [Function.comp_def, hzφ, zero_smul, map_zero, chartFunctional, zero_mul]

theorem chartFunctional_point_bound (g : SmoothMetric M) (x : M.Carrier)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) (z : ComplexVector n),
      (chartFunctional x φ L A z) ^ 2 ≤ C *
        (chartTarget x).indicator (fun w => Real.sqrt (realMetricFn g.form x w).det *
          formNormSq g.form A (chartInv x w)) z := by
  classical
  obtain ⟨c, hc, hcmp⟩ := formNormSq_chart_weighted_comparison (k := k) g x hcφ hφO
  obtain ⟨m, hm⟩ := hφ.continuous.bounded_above_of_compact_support hcφ
  let N := L.comp (modelFormReconstruction n k)
  let B : ℝ := (max m 0) ^ 2 * ‖N‖ ^ 2 * c
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hc.le
  refine ⟨B + 1, by linarith, ?_⟩
  intro A z
  let W : ComplexVector n → ℝ := (chartTarget x).indicator
    (fun w => Real.sqrt (realMetricFn g.form x w).det * formNormSq g.form A (chartInv x w))
  have hW (w : ComplexVector n) : 0 ≤ W w := by
    by_cases hw : w ∈ chartTarget x
    · simpa only [W, Set.indicator_of_mem hw] using
        mul_nonneg (Real.sqrt_nonneg _) (formNormSq_nonneg g.form A _)
    · simp only [W, Set.indicator_of_notMem hw, le_refl]
  by_cases hz : z ∈ tsupport φ
  · have hzt := hφO hz
    have hR : 0 ≤ c * W z := mul_nonneg hc.le (hW z)
    have hcoef : ‖modelFormCoefficientMap n k (chartForm A x z)‖ ≤ Real.sqrt (c * W z) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro I
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt hR, Real.norm_eq_abs, sq_abs]
      simpa only [modelFormCoefficientMap_apply, chartForm_apply_basis, W, Set.indicator_of_mem hzt] using
        (hcmp A z hz).1 I
    have hN : N (modelFormCoefficientMap n k (chartForm A x z)) = L (chartForm A x z) := by
      rw [ContinuousLinearMap.comp_apply, modelFormReconstruction_coefficient]
    have hL : ‖L (chartForm A x z)‖ ≤ ‖N‖ * Real.sqrt (c * W z) := by
      rw [← hN]
      exact (N.le_opNorm _).trans (mul_le_mul_of_nonneg_left hcoef (norm_nonneg _))
    have hprod : ‖chartFunctional x φ L A z‖ ≤ max m 0 * (‖N‖ * Real.sqrt (c * W z)) := by
      rw [chartFunctional, norm_mul]
      exact mul_le_mul ((hm z).trans (le_max_left m 0)) hL (norm_nonneg _) (le_max_right m 0)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hprod 2
    simp only [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hR] at hs
    calc
      _ ≤ B * W z := by simpa only [B, mul_assoc] using hs
      _ ≤ (B + 1) * W z := mul_le_mul_of_nonneg_right (by linarith) (hW z)
  · have hzφ : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp only [chartFunctional, hzφ, zero_mul, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (by linarith) (hW z)

theorem chartFunctional_integral_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) (hA : L2RealForm g.form μ A),
      (∫ z, (chartFunctional x φ L A z) ^ 2 ∂lebesgueC n) ≤
        C * ‖realizeActualForm g μ A hA‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := chartFunctional_point_bound g x φ hφ hcφ hφO L
  refine ⟨C, hC, ?_⟩
  intro A hA
  let W : ComplexVector n → ℝ := (chartTarget x).indicator
    (fun z => Real.sqrt (realMetricFn g.form x z).det * formNormSq g.form A (chartInv x z))
  have ht : MeasurableSet (chartTarget x) := (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
  have hiA := formNormSq_integrable g μ A hA
  have hWT : IntegrableOn (fun z => Real.sqrt (realMetricFn g.form x z).det *
      formNormSq g.form A (chartInv x z)) (chartTarget x) (lebesgueC n) := by
    simpa only [smul_eq_mul] using
      Yau.LeafProofs.L18Aux.integrableOn_chart_volume_smul g μ hμ x hiA.integrableOn
  have hW : Integrable W (lebesgueC n) := (integrable_indicator_iff ht).mpr hWT
  have hi := (memLp_two_iff_integrable_sq
    (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L A hA).aestronglyMeasurable).mp
      (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L A hA)
  have hbint := integral_mono hi (hW.const_mul C) (hb A)
  have htransport := Yau.LeafProofs.L18Aux.integral_chart_volume_ae g μ hμ x hiA.aestronglyMeasurable.restrict
  simp only [smul_eq_mul] at htransport
  have hWle : (∫ z, W z ∂lebesgueC n) ≤ ∫ y, formNormSq g.form A y ∂μ := by
    rw [integral_indicator ht, ← htransport]
    exact setIntegral_le_integral hiA (Filter.Eventually.of_forall (formNormSq_nonneg g.form A))
  rw [integral_const_mul] at hbint
  rw [realizeActualForm_norm_sq]
  exact hbint.trans (mul_le_mul_of_nonneg_left hWle hC.le)

end Yau.NodeProofs.P06Aux
