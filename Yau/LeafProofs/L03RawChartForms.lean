import Yau.LeafProofs.L03ChartMeasure

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- A real smooth compact cutoff inside an open chart, with exact value one
and zero derivative on the specified compact set. -/
theorem exists_model_chart_cutoff {O K : Set (ComplexVector n)}
    (hO : IsOpen O) (hcK : IsCompact K) (hKO : K ⊆ O) :
    ∃ χ : ComplexVector n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      (∀ z, χ z ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ z ∈ K, χ z = 1 ∧ fderiv ℝ χ z = 0) := by
  obtain ⟨Ω, hΩ, hKΩ, hΩO, hcΩ⟩ := exists_open_between_and_isCompact_closure hcK hO hKO
  obtain ⟨χ, hχ, hχrange0, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hΩ hcK.isClosed hKΩ
  have hχrange (z : ComplexVector n) : χ z ∈ Set.Icc (0 : ℝ) 1 := hχrange0 (Set.mem_range_self z)
  refine ⟨χ, hχ, ?_, ?_, hχrange, ?_⟩
  · change IsCompact (tsupport χ)
    simpa only [tsupport, hχsupport] using hcΩ
  · simpa only [tsupport, hχsupport] using hΩO
  · intro z hz
    have hz1 : χ z = 1 := (hχone z).mp hz
    refine ⟨hz1, ?_⟩
    apply IsLocalMax.fderiv_eq_zero
    exact Filter.Eventually.of_forall fun y => by rw [hz1]; exact (hχrange y).2

/-- Compact model forms admit an exact finite expansion using smooth
chart-supported test frames and measurable scalar coefficients. -/
theorem chartFormPushforward_basis_expansion {α : Type*} [Fintype α]
    (x : M.Carrier) (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (b : Basis α ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ))
    (χ : ComplexVector n → ℝ) (hχP : ∀ z, χ z • P z = P z)
    (y : M.Carrier) (v : Fin k → TangentVector M y) :
    chartFormPushforward x P y v = ∑ c, b.repr (L18Aux.chartPushforwardZero x P y) c *
      chartFormPushforward x (fun z => χ z • b c) y v := by
  classical
  by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
  · simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_pos hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    let z := chartPt x y
    let t := (tangentCoordsRealContinuousLinearMap x y) ∘ v
    have he := congrArg (fun Q : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ => Q t) (b.sum_repr (P z))
    have hev : (∑ c, b.repr (P z) c * b c t) = P z t := by
      simpa only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] using he
    calc
      _ = (χ z • P z) t := congrArg (fun Q : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ => Q t) (hχP z).symm
      _ = χ z * ∑ c, b.repr (P z) c * b c t := by rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hev]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
  · simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_neg hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, map_zero, Finsupp.zero_apply, zero_mul,
      Finset.sum_const_zero]
    rfl

/-- Raw compact model forms have the exact all-chart AE measurable
coefficients required by the original form L² definition. No smoothness of
any raw input is used. -/
theorem chartFormPushforward_coefficients_aestronglyMeasurable
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : AEStronglyMeasurable P (lebesgueC n)) (hcP : HasCompactSupport P)
    (hPO : tsupport P ⊆ chartTarget x) :
    ∀ a (I : Fin k → RIdx n), AEStronglyMeasurable
      (fun y => chartFormPushforward x P y (fun r => chartVec a y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) a).source) := by
  classical
  obtain ⟨χ, hχ, hcχ, hχO, _, hχK⟩ := exists_model_chart_cutoff
    (isOpen_extChartAt_target (I := ComplexModel n) x) hcP hPO
  let b := Module.finBasis ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
  let Ξ := L18Aux.chartPushforwardZero x P
  have hΞ := chartPushforwardZero_aestronglyMeasurable g μ hμ x P hP
  have hχP (z : ComplexVector n) : χ z • P z = P z := by
    by_cases hz : P z = 0
    · rw [hz, smul_zero]
    · rw [(hχK z (subset_tsupport P hz)).1, one_smul]
  have hB (c : Fin (finrank ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ))) :
      SmoothRealForm (chartFormPushforward x (fun z => χ z • b c)) := by
    have hs : tsupport (fun z => χ z • b c) ⊆ tsupport χ := by
      apply closure_mono
      intro z hz hzero
      exact hz (by change χ z • b c = 0; rw [hzero, zero_smul])
    exact chartFormPushforward_smooth x _ (hχ.smul contDiff_const)
      (hcχ.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hχO)
  intro a I
  have hs : AEStronglyMeasurable (fun y => ∑ c, b.repr (Ξ y) c *
      chartFormPushforward x (fun z => χ z • b c) y (fun r => chartVec a y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) a).source) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro c _
    have hc : AEStronglyMeasurable (fun y => b.repr (Ξ y) c) μ :=
      (b.coord c).toContinuousLinearMap.continuous.comp_aestronglyMeasurable hΞ
    exact (hc.mono_measure Measure.restrict_le_self).mul
      (smoothRealForm_coefficient_aestronglyMeasurable μ _ (hB c) a I)
  apply hs.congr
  exact Filter.Eventually.of_forall fun y =>
    (chartFormPushforward_basis_expansion x P b χ hχP y (fun r => chartVec a y (realVec (I r)))).symm

/-- Every raw chart pushforward vanishes pointwise off the chart source. -/
theorem chartFormPushforward_eq_zero_off (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) :
    chartFormPushforward x P y = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_neg hy,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rfl

/-- The actual raw compact chart pushforward is L² for the actual metric
and volume whenever its model field is ordinary Euclidean L². -/
theorem chartFormPushforward_l2_of_memLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : MemLp P 2 (lebesgueC n)) (hcP : HasCompactSupport P)
    (hPO : tsupport P ⊆ chartTarget x) : L2RealForm g.form μ (chartFormPushforward x P) := by
  let A := chartFormPushforward x P
  have hcoeff := chartFormPushforward_coefficients_aestronglyMeasurable g μ hμ x P
    hP.aestronglyMeasurable hcP hPO
  have hma : AEStronglyMeasurable (formNormSq g.form A) μ :=
    formInner_aestronglyMeasurable_of_coefficients g μ A A hcoeff hcoeff
  have hfm := L18Aux.aestronglyMeasurable_chartInv_of_volume g μ hμ x
    (hma.mono_measure Measure.restrict_le_self)
  have ht : MeasurableSet (chartTarget x) := (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
  obtain ⟨D, hD, hcmp⟩ := formNormSq_chart_weighted_opNorm_comparison (k := k) g x hcP hPO
  have hPi : Integrable (fun z => ‖P z‖ ^ 2) (lebesgueC n) :=
    (memLp_two_iff_integrable_sq_norm hP.aestronglyMeasurable).mp hP
  let F := fun z => Real.sqrt (realMetricFn g.form x z).det * formNormSq g.form A (chartInv x z)
  have hmF : AEStronglyMeasurable F ((lebesgueC n).restrict (chartTarget x)) :=
    ((L18Aux.volumeDensity_continuousOn g x).aestronglyMeasurable ht).mul hfm
  have hb : ∀ᵐ z ∂(lebesgueC n).restrict (chartTarget x), F z ≤ D * ‖P z‖ ^ 2 := by
    filter_upwards [ae_restrict_mem ht] with z hz
    by_cases hzP : z ∈ tsupport P
    · have h := hcmp A z hzP
      simpa only [A, chartFormPushforward_to_chart x P hz] using h
    · have hPz : P z = 0 := image_eq_zero_of_notMem_tsupport hzP
      have hcz : chartForm A x z = 0 := by rw [chartFormPushforward_to_chart x P hz, hPz]
      have hn := formNormSq_chartInv_eq_zero_of_chartForm_eq_zero g.form A x hz hcz
      simp only [F, hn, mul_zero, hPz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), le_refl]
  have hFi : Integrable F ((lebesgueC n).restrict (chartTarget x)) :=
    (hPi.const_mul D).integrableOn.mono_nonneg hmF
      (Filter.Eventually.of_forall fun z => mul_nonneg (Real.sqrt_nonneg _) (formNormSq_nonneg g.form A _)) hb
  have hzero (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) :
      formNormSq g.form A y = 0 :=
    (formNormSq_eq_zero_iff g.form A y).mpr (chartFormPushforward_eq_zero_off x P y hy)
  have hi : Integrable (formNormSq g.form A) μ :=
    integrable_of_chart_volume_zero_off g μ hμ x hzero hfm (by
      simpa only [F, IntegrableOn, smul_eq_mul] using hFi)
  refine ⟨hcoeff, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun y => formNormSq_nonneg g.form A y)).mp hi.2

end Yau.LeafProofs.L03
