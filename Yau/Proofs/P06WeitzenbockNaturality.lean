import Yau.Proofs.P06WeitzenbockEnergy

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem formComponents_frame_change (A : RealForm M 2) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    formComponents A c z = tensorFrameTransform (realChartJacobian c d z)
      (formComponents A d (L12Aux.realChartChange c d z)) := by
  apply tensorEvalCLM_injective
  rw [form_tensorEval, realChartJacobian, tensorEvalCLM_frameTransform, form_tensorEval]
  exact congrArg ContinuousAlternatingMap.toContinuousMultilinearMap
    (L03.chartForm_pullback A c d hz hy)

theorem secondCovariant_frame_change (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    covariantD h c (covariantD h c (formComponents A c)) z =
      tensorFrameTransform (realChartJacobian c d z)
        (covariantD h d (covariantD h d (formComponents A d))
          (L12Aux.realChartChange c d z)) := by
  apply tensorEvalCLM_injective
  rw [realChartJacobian, tensorEvalCLM_frameTransform]
  apply covariantD_chart_change h hs c d _ _ hz hy
  · intro v
    exact ((covariantD_contDiffOn h hs c (formComponents A c) (hA c) v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  · intro v
    have hd : L12Aux.realChartChange c d z ∈ chartTarget d :=
      (extChartAt (ComplexModel n) d).map_source hy
    exact ((covariantD_contDiffOn h hs d (formComponents A d) (hA d) v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) d).mem_nhds hd)).differentiableAt (by simp)
  · intro w hw
    have he := congrArg tensorEvalCLM (covariantD_form_chart_change h hs A hA c d hw.1 hw.2)
    simpa only [realChartJacobian, tensorEvalCLM_frameTransform] using he

theorem tensorFrameTransform_neg {r : ℕ} (D : Matrix (RIdx n) (RIdx n) ℝ)
    (T : CovTensor n r) : tensorFrameTransform D (-T) = -tensorFrameTransform D T := by
  funext v
  simp only [tensorFrameTransform, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem roughTwo_frame_change (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    roughTwoComponents h A c z = tensorFrameTransform (realChartJacobian c d z)
      (roughTwoComponents h A d (L12Aux.realChartChange c d z)) := by
  have hr (e : M.Carrier) (w : ComplexVector n) : roughTwoComponents h A e w =
      -tensorMetricTrace (realMetricFn h e w)⁻¹
        (covariantD h e (covariantD h e (formComponents A e)) w) := by
    funext I
    rfl
  rw [hr, secondCovariant_frame_change h hs A hA c d hz hy,
    tensorMetricTrace_frameTransform, inverseMetric_chart_change h c d hz hy,
    hr, tensorFrameTransform_neg]

theorem covTensorPair_frame_change {r : ℕ}
    (Gc Gd J : Matrix (RIdx n) (RIdx n) ℝ)
    (hInv : J * Gc⁻¹ * Jᵀ = Gd⁻¹) (A B : CovTensor n r) :
    covTensorPair Gc (tensorFrameTransform J A) (tensorFrameTransform J B) =
      covTensorPair Gd A B := by
  unfold covTensorPair
  rw [tensor_contraction_frameTransform, hInv]

theorem covTensorPair_first_slot (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A B : CovTensor n 3) :
    covTensorPair G A B = ∑ a, ∑ b, G⁻¹ a b *
      L03.tensorCoefficientPairing G⁻¹ (fun I => A (Fin.cons a I))
        (fun I => B (Fin.cons b I)) := by
  unfold covTensorPair
  rw [sum_tensor_cons]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext I
    rw [sum_tensor_cons]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  simp only [L03.tensorCoefficientPairing, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem chartGradientPair_eq_covTensorPair (h : HermitianField M) (A B : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) :
    chartGradientPair h A B c z = (1 / 2 : ℝ) * covTensorPair (realMetricFn h c z)
      (covariantD h c (formComponents B c) z) (covariantD h c (formComponents A c) z) := by
  rw [covTensorPair_first_slot]
  simp only [chartGradientPair, covariantD_form_cons]

theorem chartGradientPair_frame_change (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    chartGradientPair h A B c z =
      chartGradientPair h A B d (L12Aux.realChartChange c d z) := by
  rw [chartGradientPair_eq_covTensorPair, chartGradientPair_eq_covTensorPair,
    covariantD_form_chart_change h hs A hA c d hz hy,
    covariantD_form_chart_change h hs B hB c d hz hy,
    covTensorPair_frame_change _ _ _ (inverseMetric_chart_change h c d hz hy)]

theorem chartRoughPair_frame_change (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    chartRoughPair h A B c z = chartRoughPair h A B d (L12Aux.realChartChange c d z) := by
  change (1 / 2 : ℝ) * covTensorPair (realMetricFn h c z)
      (formComponents B c z) (roughTwoComponents h A c z) =
    (1 / 2 : ℝ) * covTensorPair (realMetricFn h d (L12Aux.realChartChange c d z))
      (formComponents B d (L12Aux.realChartChange c d z))
      (roughTwoComponents h A d (L12Aux.realChartChange c d z))
  rw [formComponents_frame_change B c d hz hy, roughTwo_frame_change h hs A hA c d hz hy,
    covTensorPair_frame_change _ _ _ (inverseMetric_chart_change h c d hz hy)]

def gradientPair (h : HermitianField M) (A B : RealForm M 2) (x : M.Carrier) : ℝ :=
  chartGradientPair h A B x (chartPt x x)

def roughPair (h : HermitianField M) (A B : RealForm M 2) (x : M.Carrier) : ℝ :=
  chartRoughPair h A B x (chartPt x x)

def curvaturePair (h : HermitianField M) (A B : RealForm M 2) (x : M.Carrier) : ℝ :=
  chartCurvaturePair h A B x (chartPt x x)

theorem gradientPair_in_chart (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    gradientPair h A B (chartInv c z) = chartGradientPair h A B c z := by
  symm
  exact chartGradientPair_frame_change h hs A B hA hB c (chartInv c z) hz
    (mem_extChartAt_source _)

theorem roughPair_in_chart (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    roughPair h A B (chartInv c z) = chartRoughPair h A B c z := by
  symm
  exact chartRoughPair_frame_change h hs A B hA c (chartInv c z) hz
    (mem_extChartAt_source _)

theorem curvaturePair_in_chart (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    curvaturePair h A B (chartInv c z) = chartCurvaturePair h A B c z := by
  let y := chartInv c z
  have hy : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hp := hodgePair_eq_rough_add_curvature h hs A B hA c hz
  have hq := hodgePair_eq_rough_add_curvature h hs A B hA y
    (z := chartPt y y) (mem_extChartAt_target y)
  rw [hy] at hq
  have hr := roughPair_in_chart h hs A B hA c hz
  change chartRoughPair h A B y (chartPt y y) = chartRoughPair h A B c z at hr
  change chartCurvaturePair h A B y (chartPt y y) = _
  linarith

theorem gradientPair_smooth (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    SmoothFn (gradientPair h A B) := by
  intro c
  have hU := covariantD_contDiffOn h hs c (formComponents A c) (hA c)
  have hV := covariantD_contDiffOn h hs c (formComponents B c) (hB c)
  have hp := L03.tensorCoefficientPairing_contDiffOn
    (fun z => (realMetricFn h c z)⁻¹) (covariantD h c (formComponents B c))
    (covariantD h c (formComponents A c)) (chartTarget c)
    (realMetricFn_inverse_contDiffOn h hs c) hV hU
  apply (contDiffOn_const.mul hp).congr
  intro z hz
  rw [show inChart c (gradientPair h A B) z = gradientPair h A B (chartInv c z) from rfl,
    gradientPair_in_chart h hs A B hA hB c hz, chartGradientPair_eq_covTensorPair]
  rfl

theorem roughPair_smooth (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    SmoothFn (roughPair h A B) := by
  intro c
  have hU := covariantD_contDiffOn h hs c (formComponents A c) (hA c)
  have hR (I : Fin 2 → RIdx n) : ContDiffOn ℝ ∞
      (fun z => roughTwoComponents h A c z I) (chartTarget c) := by
    simp only [roughTwo_eq_codifferential_covariant]
    exact codifferentialComponents_smooth h hs c _ hU I
  have hp := L03.tensorCoefficientPairing_contDiffOn
    (fun z => (realMetricFn h c z)⁻¹) (formComponents B c) (roughTwoComponents h A c)
    (chartTarget c) (realMetricFn_inverse_contDiffOn h hs c) (hB c) hR
  apply (contDiffOn_const.mul hp).congr
  intro z hz
  rw [show inChart c (roughPair h A B) z = roughPair h A B (chartInv c z) from rfl,
    roughPair_in_chart h hs A B hA c hz]
  rfl

theorem covariantD_form_zero_of_eventuallyEq_zero (h : HermitianField M)
    (B : RealForm M 2) (x : M.Carrier) (hB : ∀ᶠ y in 𝓝 x, B y = 0) :
    covariantD h x (formComponents B x) (chartPt x x) = 0 := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hloc : formComponents B x =ᶠ[𝓝 (chartPt x x)] 0 := by
    have he : ∀ᶠ y in 𝓝 (chartInv x (chartPt x x)), B y = (0 : RealForm M 2) y := by
      simpa only [hx, Pi.zero_apply] using hB
    simpa only [L03.formComponents_zero] using
      L03.formComponents_eventuallyEq_of_eventuallyEq x (z := chartPt x x) (mem_extChartAt_target x) he
  have hd := covariantD_eventuallyEq h x _ _ (chartPt x x) hloc
  rw [hd]
  funext v
  simp [covariantD, rDeriv]

theorem gradientPair_support_subset (h : HermitianField M) (A B : RealForm M 2) :
    tsupport (gradientPair h A B) ⊆ closure {x | B x ≠ 0} := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he : ∀ᶠ y in 𝓝 x, B y = 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with y hy
    by_contra hzero
    exact hy (subset_closure hzero)
  have hd := covariantD_form_zero_of_eventuallyEq_zero h B x he
  have hz : gradientPair h A B x = 0 := by
    rw [gradientPair, chartGradientPair_eq_covTensorPair, hd]
    simp [covTensorPair]
  exact hx hz

theorem roughPair_support_subset (h : HermitianField M) (A B : RealForm M 2) :
    tsupport (roughPair h A B) ⊆ closure {x | B x ≠ 0} := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply subset_closure
  intro hzero
  have hc := (L03.formComponents_center_eq_zero_iff B x).mpr hzero
  apply hx
  simp only [roughPair, chartRoughPair, hc, Pi.zero_apply, L03.tensorCoefficientPairing,
    zero_mul, Finset.sum_const_zero, mul_zero]

theorem gradientPair_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    Integrable (gradientPair g.form A B) μ :=
  L18Aux.smoothFn_integrable_compact g μ hμ
    (gradientPair_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g) A B hA hB)
    (hcB.of_isClosed_subset (isClosed_tsupport _) (gradientPair_support_subset g.form A B))

theorem roughPair_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    Integrable (roughPair g.form A B) μ :=
  L18Aux.smoothFn_integrable_compact g μ hμ
    (roughPair_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g) A B hA hB)
    (hcB.of_isClosed_subset (isClosed_tsupport _) (roughPair_support_subset g.form A B))

end Yau.NodeProofs.P06Weitzenbock
