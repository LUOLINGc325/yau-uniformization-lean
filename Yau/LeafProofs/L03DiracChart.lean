import Yau.LeafProofs.L03ChartApprox

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- A compact chart-supported model field has a genuinely smooth, compact
computed Dirac output, even though the raw chart coefficients are only locally
smooth. The operator does not enlarge its topological support. -/
theorem modelDiracJetCLM_compact_apply_properties (g : SmoothMetric M) (x : M.Carrier)
    (G : ComplexVector n → modelGradedFiber n) (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G) (hGO : tsupport G ⊆ chartTarget x) :
    let H := fun z => modelDiracJetCLM g.form x z (G z, fderiv ℝ G z)
    ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ tsupport G := by
  let H := fun z => modelDiracJetCLM g.form x z (G z, fderiv ℝ G z)
  have hzero (z : ComplexVector n) (hz : z ∉ tsupport G) : H z = 0 := by
    simp only [H, image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
    exact map_zero _
  have hs : tsupport H ⊆ tsupport G := by
    apply closure_minimal _ (isClosed_tsupport G)
    intro z hz
    by_contra hzG
    exact hz (hzero z hzG)
  have hHOn : ContDiffOn ℝ ∞ H (chartTarget x) :=
    (contDiffOn_clm_apply.mpr (modelDiracJetCLM_contDiffOn g x)).clm_apply
      (hG.contDiffOn.prodMk ((hG.fderiv_right (m := ∞) (by simp)).contDiffOn))
  refine ⟨?_, hcG.of_isClosed_subset (isClosed_tsupport H) hs, hs⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport G
  · exact hHOn.contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (hGO hz))
  · have heq : H =ᶠ[𝓝 z] (fun _ => (0 : modelGradedFiber n)) := by
      filter_upwards [(isClosed_tsupport G).compl_mem_nhds hz] with w hw
      exact hzero w hw
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- The true coefficients multiplying the cutoff commutator are globally
smooth and supported in the original compact cutoff, despite being assembled
from coefficients defined on the chart. -/
theorem diracScalar_cutoff_derivative_properties {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (r c : α) (i : RIdx n) :
    let R := fun z => diracScalarDerivativeCoefficient g.form x b r c i z *
      fderiv ℝ χ z (realModelBasis n i)
    ContDiff ℝ ∞ R ∧ HasCompactSupport R ∧ tsupport R ⊆ tsupport χ := by
  let d := fun z => fderiv ℝ χ z (realModelBasis n i)
  have hd : ContDiff ℝ ∞ d :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcd : HasCompactSupport d := hcχ.fderiv_apply ℝ (realModelBasis n i)
  have hsd : tsupport d ⊆ tsupport χ := tsupport_fderiv_apply_subset ℝ (realModelBasis n i)
  have h := scalar_cutoff_contDiff_properties
    (isOpen_extChartAt_target (I := ComplexModel n) x) d hd hcd (hsd.trans hχO)
    (diracScalarDerivativeCoefficient g.form x b r c i)
    (diracScalarDerivativeCoefficient_contDiffOn g x b r c i)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [d, mul_comm] using h.1
  · simpa only [d, mul_comm] using h.2.1
  · simpa only [d, mul_comm] using h.2.2.trans hsd

/-- Chart values and pointwise vanishing off its source suffice to identify
an actual form with the pushforward of its model expression. -/
theorem chartFormPushforward_eq_of_chart_and_zero_off (x : M.Carrier)
    (A : RealForm M k) (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hchart : ∀ z ∈ chartTarget x, chartForm A x z = P z)
    (hoff : ∀ y, y ∉ (extChartAt (ComplexModel n) x).source → A y = 0) :
    chartFormPushforward x P = A := by
  funext y
  by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
  · apply ContinuousAlternatingMap.ext
    intro v
    have hi : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
    have hz : chartPt x y ∈ chartTarget x := (extChartAt (ComplexModel n) x).map_source hy
    simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_pos hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [← hchart (chartPt x y) hz]
    simp only [chartForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      Function.comp_def, chartRealContinuousLinearMap_apply, tangentCoordsRealContinuousLinearMap_apply]
    change A (chartInv x (chartPt x y))
      (fun i => chartVec x (chartInv x (chartPt x y)) (tangentCoords x y (v i))) = A y v
    rw [hi]
    congr 1
    funext i
    exact L12Aux.chartVec_tangentCoords x y hy (v i)
  · apply ContinuousAlternatingMap.ext
    intro v
    simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_neg hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hoff y hy]
    rfl

/-- The computed manifold Dirac output of a compact chart test is exactly
pushforward of the computed model first-jet output. -/
theorem modelGradedChartPushforward_dirac_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (G : ComplexVector n → modelGradedFiber n) (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G) (hGO : tsupport G ⊆ chartTarget x) :
    diracRealForm g.form (modelGradedChartPushforward x G) =
      modelGradedChartPushforward x
        (fun z => modelDiracJetCLM g.form x z (G z, fderiv ℝ G z)) := by
  let A := modelGradedChartPushforward x G
  have hA := modelGradedChartPushforward_properties x G hG hcG hGO
  have hz := diracRealForm_eq_zero_outside_chart g μ hμ A (fun j => (hA j).1) x
    (fun j => (hA j).2.2)
  funext j
  symm
  apply chartFormPushforward_eq_of_chart_and_zero_off
  · intro z hzO
    rw [← modelGradedProjection_chart (diracRealForm g.form A) x z j]
    congr 1
    exact modelGradedChartPushforward_dirac_to_chart g μ hμ x G hG hcG hGO hzO
  · exact hz j

/-- On a single fixed compact chart set, the actual graded metric L²
error is bounded by the ordinary model-fibre L² error with one fixed constant. -/
theorem modelGradedChartPushforward_l2_distance_bound (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A)
    (hcA : ∀ j, CompactlySupportedRealForm (A j)) (x : M.Carrier)
    (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    {K : Set (ComplexVector n)} (hcK : IsCompact K) (hKO : K ⊆ chartTarget x)
    (hAK : tsupport (modelGradedChartPullbackZero A x) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G : ComplexVector n → modelGradedFiber n,
      ContDiff ℝ ∞ G → tsupport G ⊆ K →
        OperatorCandidates.gradedDistanceSq g.form μ (modelGradedChartPushforward x G) A ≤
          ENNReal.ofReal (C * ∫ z, ‖G z - modelGradedChartPullbackZero A x z‖ ^ 2 ∂lebesgueC n) := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let U := modelGradedChartPullbackZero A x
  have hUiK (i : Fin (2 * n + 1)) : tsupport (chartFormPullbackZero x (A i.val)) ⊆ K := by
    apply Set.Subset.trans _ hAK
    apply closure_mono
    intro z hz hzero
    exact hz (congrFun hzero i)
  choose D hD hbound using fun i : Fin (2 * n + 1) =>
    chartFormPushforward_l2_distance_bound g μ hμ (A i.val) (hA.2 i.val) (hcA i.val) x
      (hAx i.val) hcK hKO (hUiK i)
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => (hD i).le), ?_⟩
  intro G hG hGK
  have hcG : HasCompactSupport G := hcK.of_isClosed_subset (isClosed_tsupport _) hGK
  have hGm : MemLp G 2 (lebesgueC n) := hG.continuous.memLp_of_hasCompactSupport hcG
  have hUm : MemLp U 2 (lebesgueC n) := MemLp.of_eval (fun i =>
    chartFormPullbackZero_memLp g μ hμ (A i.val) (hA.2 i.val) (hcA i.val) x (hAx i.val))
  have hdiff : MemLp (U - G) 2 (lebesgueC n) := hUm.sub hGm
  have hi : Integrable (fun z => ‖U z - G z‖ ^ 2) (lebesgueC n) :=
    (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).mp hdiff
  have hdeg (i : Fin (2 * n + 1)) :
      formL2DistanceSq g.form μ (modelGradedChartPushforward x G i.val) (A i.val) ≤
        ENNReal.ofReal (D i * ∫ z, ‖G z - U z‖ ^ 2 ∂lebesgueC n) := by
    let L : modelGradedFiber n →L[ℝ] ((ComplexVector n) [⋀^Fin i.val]→L[ℝ] ℝ) :=
      ContinuousLinearMap.proj i
    let P := fun z => G z i
    have hP : ContDiff ℝ ∞ P := L.contDiff.comp hG
    have hPK : tsupport P ⊆ K := by
      apply Set.Subset.trans _ hGK
      apply closure_mono
      intro z hz hzero
      exact hz (congrFun hzero i)
    have hPm : MemLp P 2 (lebesgueC n) := L.comp_memLp' hGm
    have hd : MemLp (chartFormPullbackZero x (A i.val) - P) 2 (lebesgueC n) :=
      (chartFormPullbackZero_memLp g μ hμ (A i.val) (hA.2 i.val) (hcA i.val) x (hAx i.val)).sub hPm
    have hdi : Integrable (fun z => ‖chartFormPullbackZero x (A i.val) z - P z‖ ^ 2) (lebesgueC n) :=
      (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
    have hnorm : (eLpNorm (chartFormPullbackZero x (A i.val) - P) 2 (lebesgueC n)) ^ 2 ≤
        ENNReal.ofReal (∫ z, ‖G z - U z‖ ^ 2 ∂lebesgueC n) := by
      rw [← ofReal_integral_norm_sq_eq_eLpNorm_sq (lebesgueC n) hd]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ∫ z, ‖U z - G z‖ ^ 2 ∂lebesgueC n := integral_mono hdi hi (fun z => by
          exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm (U z - G z) i))
        _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun z => by rw [norm_sub_rev])
    have hp := hbound i P hP hPK
    have heq : modelGradedChartPushforward x G i.val = chartFormPushforward x P := by
      change chartFormPushforward x (fun z => modelGradedProjection n i.val (G z)) = _
      congr 1
      funext z
      simp only [modelGradedProjection, dif_pos i.isLt, ContinuousLinearMap.proj_apply]
      rfl
    rw [heq]
    exact hp.trans (by
      rw [ENNReal.ofReal_mul (hD i).le]
      exact mul_le_mul le_rfl hnorm (by positivity) (by positivity))
  calc
    _ ≤ ∑ i : Fin (2 * n + 1), ENNReal.ofReal (D i * ∫ z, ‖G z - U z‖ ^ 2 ∂lebesgueC n) :=
      Finset.sum_le_sum (fun i _ => hdeg i)
    _ = ENNReal.ofReal ((∑ i, D i) * ∫ z, ‖G z - U z‖ ^ 2 ∂lebesgueC n) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact mul_nonneg (hD i).le (integral_nonneg fun z => sq_nonneg _)

end Yau.LeafProofs.L03
