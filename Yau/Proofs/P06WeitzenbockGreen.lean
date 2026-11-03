import Yau.Proofs.P06WeitzenbockNaturality

noncomputable section
open Filter MeasureTheory
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L03
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem integral_modelTest_rough_gradient (g : SmoothMetric M) (c : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P) (hPO : tsupport P ⊆ chartTarget c)
    (A : RealForm M 2) (hA : SmoothRealForm A) :
    (∫ z in chartTarget c, Real.sqrt (realMetricFn g.form c z).det *
      (chartGradientPair g.form A (chartFormPushforward c P) c z -
        chartRoughPair g.form A (chartFormPushforward c P) c z) ∂lebesgueC n) = 0 := by
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  let B := chartFormPushforward c P
  let F : FormComponents n 2 := fun z I => P z (fun r => realVec (I r))
  let U := covariantD g.form c (formComponents A c)
  let V := raisedFirstComponents g.form c U
  let Q := tensorMetricFlux g.form c F V
  have hB : SmoothRealForm B := chartFormPushforward_smooth c P hP hcP hPO
  have hU := covariantD_contDiffOn g.form (L12Aux.metricSmooth_of_smoothMetric g)
    c (formComponents A c) (hA c)
  have hV (a : RIdx n) (I : Fin 2 → RIdx n) :
      ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget c) :=
    raisedFirstComponents_contDiffOn g c U hU a I
  have hQ (a : RIdx n) : ContDiff ℝ ∞ (Q a) ∧ HasCompactSupport (Q a) ∧
      tsupport (Q a) ⊆ tsupport P :=
    tensorMetricFlux_modelTest_properties g c P hP hcP hPO V hV a
  have hcoeff {z : ComplexVector n} (hz : z ∈ chartTarget c) : formComponents B c z = F z := by
    funext I
    rw [← chartForm_apply_basis B c z I, chartFormPushforward_to_chart c P hz]
  have hd {z : ComplexVector n} (hz : z ∈ chartTarget c) (a : RIdx n) :
      rDeriv (tensorMetricFlux g.form c (formComponents B c) V a) z a = rDeriv (Q a) z a := by
    have heq : tensorMetricFlux g.form c (formComponents B c) V a =ᶠ[𝓝 z] Q a := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
      simp only [tensorMetricFlux, hcoeff hw, Q]
    exact congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec a)) heq.fderiv_eq
  have hp {z : ComplexVector n} (hz : z ∈ chartTarget c) :
      Real.sqrt (realMetricFn g.form c z).det *
        (chartGradientPair g.form A B c z - chartRoughPair g.form A B c z) =
        (1 / 2 : ℝ) * ∑ a, rDeriv (Q a) z a := by
    rw [← tensorGreen_raised_covariant g A B hA c hz]
    simp_rw [← hd hz, tensorMetricFlux_derivative g c (formComponents B c) V (hB c) hV hz]
    rw [← Finset.mul_sum]
    ring
  have hqi (a : RIdx n) : Integrable (fun z => rDeriv (Q a) z a) (lebesgueC n) :=
    ((((hQ a).1.of_le (by simp) : ContDiff ℝ 1 (Q a)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hQ a).2.1.fderiv_apply ℝ (realVec a))
  have hz : (∫ z in chartTarget c, ∑ a, rDeriv (Q a) z a ∂lebesgueC n) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    · rw [integral_finsetSum Finset.univ (fun a _ => hqi a)]
      apply Finset.sum_eq_zero
      intro a _
      exact integral_compact_fderiv_eq_zero (lebesgueC n) ((hQ a).1.of_le (by simp))
        (hQ a).2.1 (realVec a)
    · apply Finset.sum_eq_zero
      intro a _
      have hn : z ∉ tsupport (Q a) := fun hh => hz (hPO ((hQ a).2.2 hh))
      simp only [rDeriv, fderiv_of_notMem_tsupport ℝ hn, ContinuousLinearMap.zero_apply]
  calc
    _ = ∫ z in chartTarget c, (1 / 2 : ℝ) * ∑ a, rDeriv (Q a) z a ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) c).measurableSet
      intro z hz
      exact hp hz
    _ = (1 / 2 : ℝ) * (∫ z in chartTarget c, ∑ a, rDeriv (Q a) z a ∂lebesgueC n) :=
      integral_const_mul _ _
    _ = 0 := by rw [hz, mul_zero]

theorem integral_rough_gradient_chartSupport (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (c : M.Carrier) (hBc : closure {y | B y ≠ 0} ⊆ (extChartAt (ComplexModel n) c).source) :
    (∫ y, gradientPair g.form A B y - roughPair g.form A B y ∂μ) = 0 := by
  have hs := L12Aux.metricSmooth_of_smoothMetric g
  let f := fun y => gradientPair g.form A B y - roughPair g.form A B y
  have hf : Continuous f :=
    (L18Aux.continuous_of_smoothFn (gradientPair_smooth g.form hs A B hA hB)).sub
      (L18Aux.continuous_of_smoothFn (roughPair_smooth g.form hs A B hA hB))
  have hfzero (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) c).source) : f y = 0 := by
    dsimp only [f]
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hy (hBc ((gradientPair_support_subset g.form A B) hh))),
      image_eq_zero_of_notMem_tsupport (fun hh => hy (hBc ((roughPair_support_subset g.form A B) hh))), sub_self]
  have hp := chartFormPullbackZero_properties c B hB hcB hBc
  have hlocal := integral_modelTest_rough_gradient g c (chartFormPullbackZero c B)
    hp.1 hp.2.1 hp.2.2.1 A hA
  rw [chartFormPushforward_pullbackZero c B hBc] at hlocal
  calc
    _ = ∫ y in (extChartAt (ComplexModel n) c).source, f y ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hfzero).symm
    _ = ∫ z in chartTarget c, Real.sqrt (realMetricFn g.form c z).det * f (chartInv c z)
        ∂lebesgueC n := L18Aux.integral_chart_volume g μ hμ c f hf.measurable
    _ = 0 := by
      convert hlocal using 1
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) c).measurableSet
      intro z hz
      simp only [f, gradientPair_in_chart g.form hs A B hA hB c hz,
        roughPair_in_chart g.form hs A B hA c hz]

theorem formComponents_finite_sum {ι : Type*} [Fintype ι] (B : ι → RealForm M 2)
    (c : M.Carrier) : formComponents (∑ i, B i) c = fun z I => ∑ i, formComponents (B i) c z I := by
  funext z I
  simp [formComponents]

theorem roughPair_finite_sum {ι : Type*} [Fintype ι] (h : HermitianField M)
    (A : RealForm M 2) (B : ι → RealForm M 2) (x : M.Carrier) :
    roughPair h A (∑ i, B i) x = ∑ i, roughPair h A (B i) x := by
  rw [roughPair, chartRoughPair, formComponents_finite_sum,
    tensorCoefficientPairing_fintypeSum_left, Finset.mul_sum]
  rfl

theorem gradientPair_finite_sum {ι : Type*} [Fintype ι] (h : HermitianField M)
    (A : RealForm M 2) (B : ι → RealForm M 2) (hB : ∀ i, SmoothRealForm (B i)) (x : M.Carrier) :
    gradientPair h A (∑ i, B i) x = ∑ i, gradientPair h A (B i) x := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hd (i : ι) (I : Fin 2 → RIdx n) :
      DifferentiableAt ℝ (fun w => formComponents (B i) x w I) (chartPt x x) :=
    (((hB i) x I).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have he (a : RIdx n) :
      (fun I => covariantComponents h x (formComponents (∑ i, B i) x) (chartPt x x) a I) =
        fun I => ∑ i, covariantComponents h x (formComponents (B i) x) (chartPt x x) a I := by
    funext I
    rw [formComponents_finite_sum]
    exact covariantComponents_fintypeSum_at h x (fun i => formComponents (B i) x) _ hd a I
  simp only [gradientPair, chartGradientPair, he, tensorCoefficientPairing_fintypeSum_left,
    Finset.mul_sum]
  exact (L03.sum_three_rotate _).symm

theorem integral_rough_eq_gradient (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ y, roughPair g.form A B y ∂μ) = ∫ y, gradientPair g.form A B y ∂μ := by
  classical
  obtain ⟨s, p, hp, _, hps, hsum⟩ := L18Aux.exists_finite_smooth_partition hcB
  let Bs : s → RealForm M 2 := fun i => multiplyRealForm (p i) B
  have hBs (i : s) : SmoothRealForm (Bs i) := smoothRealForm_multiply (p i) B (hp i) hB
  have hcBs (i : s) : CompactlySupportedRealForm (Bs i) :=
    compactlySupportedRealForm_multiply (p i) B hcB
  have hsBs (i : s) : closure {y | Bs i y ≠ 0} ⊆
      (extChartAt (ComplexModel n) (i : M.Carrier)).source :=
    (multiplyRealForm_support_subset_scalar (p i) B).trans (hps i)
  have hsumB : (∑ i, Bs i) = B := by
    funext y
    simp only [Finset.sum_apply, Bs, multiplyRealForm]
    rw [← Finset.sum_smul]
    by_cases hy : B y = 0
    · simp only [hy, smul_zero]
    · rw [hsum y (subset_closure hy), one_smul]
  have hpiece (i : s) : (∫ y, roughPair g.form A (Bs i) y ∂μ) =
      ∫ y, gradientPair g.form A (Bs i) y ∂μ := by
    have he := integral_rough_gradient_chartSupport g μ hμ A (Bs i) hA (hBs i) (hcBs i)
      (i : M.Carrier) (hsBs i)
    rw [integral_sub (gradientPair_integrable g μ hμ A (Bs i) hA (hBs i) (hcBs i))
      (roughPair_integrable g μ hμ A (Bs i) hA (hBs i) (hcBs i))] at he
    exact (sub_eq_zero.mp he).symm
  rw [← hsumB]
  simp only [roughPair_finite_sum, gradientPair_finite_sum g.form A Bs hBs]
  rw [integral_finsetSum Finset.univ (fun i _ => roughPair_integrable g μ hμ A (Bs i) hA (hBs i) (hcBs i)),
    integral_finsetSum Finset.univ (fun i _ => gradientPair_integrable g μ hμ A (Bs i) hA (hBs i) (hcBs i))]
  exact Finset.sum_congr rfl (fun i _ => hpiece i)

end Yau.NodeProofs.P06Weitzenbock
