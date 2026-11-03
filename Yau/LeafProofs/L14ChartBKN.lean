import Yau.LeafProofs.L14EnergyRegularity

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem oneFormPushforward_compact (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    IsCompact (closure {x | oneFormPushforward (r := r) E a F x ≠ (0 : NQForm E 1) x}) := by
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  exact hK.of_isClosed_subset isClosed_closure (oneFormPushforward_support E a F hc hs)

theorem topFormPushforward_compact (a : M.Carrier)
    (F : ComplexVector n → ComplexVector r)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    IsCompact (closure {x | topFormPushforward (r := r) E a F x ≠ (0 : NQForm E 0) x}) := by
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  exact hK.of_isClosed_subset isClosed_closure (topFormPushforward_support E a F hc hs)

theorem raisedBarTensor_oneFormPushforward (g : HermitianField M)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    raisedBarTensor (r := r) E g (oneFormPushforward (r := r) E a F) a z =
      fun α => localBarMatrix (fun w i α => chartOneRaise g a F w i α) z α := by
  funext α i j
  have he : (fun w => raisedOneCoefficientsMatrix (r := r) E g
      (oneFormPushforward (r := r) E a F) a w j α) =ᶠ[𝓝 z]
      (fun w => chartOneRaise g a F w j α) := by
    filter_upwards [(localDomain_isOpen E a).mem_nhds hz] with w hw
    simp only [raisedOneCoefficientsMatrix, oneCoefficientsMatrix, Matrix.mul_apply,
      oneFormPushforward_coefficients E a F w hw, chartOneRaise, WithLp.ofLp_toLp]
  change wirtBar _ z (stdVec i) = wirtBar _ z (stdVec i)
  unfold wirtBar
  rw [he.fderiv_eq]

theorem integral_of_compact_chart_density_real
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : M.Carrier) (P : M.Carrier → ℝ) (Q : ComplexVector n → ℝ)
    (hP : Integrable P μ)
    (hPzero : ∀ x, x ∉ (extChartAt (ComplexModel n) a).source → P x = 0)
    (hQzero : ∀ z, z ∉ chartTarget a → Q z = 0)
    (hlocal : ∀ z ∈ chartTarget a,
      Real.sqrt (realMetricFn g.form a z).det * P (chartInv a z) = (2 : ℝ) ^ n * Q z) :
    (∫ x, P x ∂μ) = (2 : ℝ) ^ n * ∫ z, Q z ∂lebesgueC n := by
  have hm := hP.aestronglyMeasurable.mono_measure
    (Measure.restrict_le_self (s := (extChartAt (ComplexModel n) a).source))
  calc
    _ = ∫ x in (extChartAt (ComplexModel n) a).source, P x ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hPzero).symm
    _ = ∫ z in chartTarget a, Real.sqrt (realMetricFn g.form a z).det • P (chartInv a z) ∂lebesgueC n :=
      L18Aux.integral_chart_volume_ae g μ hμ a hm
    _ = ∫ z in chartTarget a, (2 : ℝ) ^ n * Q z ∂lebesgueC n :=
      setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet hlocal
    _ = (2 : ℝ) ^ n * ∫ z in chartTarget a, Q z ∂lebesgueC n := integral_const_mul _ _
    _ = _ := congrArg (fun w : ℝ => (2 : ℝ) ^ n * w)
      (setIntegral_eq_integral_of_forall_compl_eq_zero hQzero)

theorem bknResidual_oneFormPushforward_inChart (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
    let W := fun w i α => chartOneRaise g.form a F w i α
    let A := fun w α => chartDbarAdjoint (r := r) E g.form h φ a F w α
    bknResidual (r := r) E g.form h φ (oneFormPushforward (r := r) E a F)
      (twoFormPushforward (r := r) E a (modelOneDbar F))
      (topFormPushforward (r := r) E a (chartDbarAdjoint (r := r) E g.form h φ a F)) (chartInv a z) =
      ((hMat g.form a z).det.re)⁻¹ *
        ((star (A z) ⬝ᵥ K z *ᵥ A z).re + localCurlEnergy (hMat g.form a z) (K z) F z -
          localPositiveEnergy (hMat g.form a z) (K z) W z -
          Real.exp (-inChart a φ z) * nakanoQuadratic (weightedCurvature (r := r) E h φ a z) (W z)) := by
  rw [bknResidual, bknDifferentialEnergy_inChart E hE g h φ _
    (oneFormPushforward_smooth E hE a F hF hc hs) _ _ a z hz,
    curvatureFormEnergy_inChart E hE g.form h hh φ hφ _ a z hz,
    topFormPushforward_coefficients E a _ z hz,
    raisedBarTensor_oneFormPushforward E g.form a F z hz]
  simp_rw [twoFormPushforward_coefficients E a (modelOneDbar F) (modelOneDbar_skew F) z hz]
  have hW (i : Fin n) (α : Fin r) :
      raisedOneCoefficientsMatrix (r := r) E g.form (oneFormPushforward (r := r) E a F) a z i α =
        chartOneRaise g.form a F z i α := by
    simp only [raisedOneCoefficientsMatrix, oneCoefficientsMatrix, Matrix.mul_apply,
      oneFormPushforward_coefficients E a F z hz, chartOneRaise, WithLp.ofLp_toLp]
  simp_rw [hW]
  change ((hMat g.form a z).det.re)⁻¹ *
      (localCurlEnergy (hMat g.form a z) _ F z + _ - localPositiveEnergy (hMat g.form a z) _ _ z) -
      ((hMat g.form a z).det.re)⁻¹ * _ * Real.exp (-φ (chartInv a z)) = _
  simp only [inChart]
  ring

theorem bknResidual_oneFormPushforward_integral_zero (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    (∫ x, bknResidual (r := r) E g.form h φ (oneFormPushforward (r := r) E a F)
      (twoFormPushforward (r := r) E a (modelOneDbar F))
      (topFormPushforward (r := r) E a (chartDbarAdjoint (r := r) E g.form h φ a F)) x ∂μ) = 0 := by
  classical
  let O := localDomain (r := r) E a
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let W := fun w i α => chartOneRaise g.form a F w i α
  let δ := chartDbarAdjoint (r := r) E g.form h φ a F
  let A := fun w α => δ w α
  let J := fun z => (star (A z) ⬝ᵥ K z *ᵥ A z).re + localCurlEnergy (hMat g.form a z) (K z) F z -
    localPositiveEnergy (hMat g.form a z) (K z) W z -
    Real.exp (-inChart a φ z) * nakanoQuadratic (weightedCurvature (r := r) E h φ a z) (W z)
  let u := oneFormPushforward (r := r) E a F
  let f := twoFormPushforward (r := r) E a (modelOneDbar F)
  let S := topFormPushforward (r := r) E a δ
  let P := bknResidual (r := r) E g.form h φ u f S
  let Q := O.indicator J
  have hδ := chartDbarAdjoint_contDiff E g h hh φ hφ a F hF hs
  have hsδ : tsupport δ ⊆ O := (tsupport_chartDbarAdjoint_subset E g.form h φ a F).trans hs
  have hcδ : HasCompactSupport δ := hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_chartDbarAdjoint_subset E g.form h φ a F)
  have hsD : tsupport (modelOneDbar F) ⊆ O := (tsupport_modelOneDbar_subset F).trans hs
  have hcD : HasCompactSupport (modelOneDbar F) := hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_modelOneDbar_subset F)
  have hP : Integrable P μ := bknResidual_integrable E hE g μ hμ h hh φ hφ u
    (oneFormPushforward_smooth E hE a F hF hc hs) (oneFormPushforward_compact E a F hc hs)
    f (twoFormPushforward_smooth E hE a _ (modelOneDbar_skew F) (modelOneDbar_contDiff F hF) hcD hsD)
      (twoFormPushforward_compact E a _ hcD hsD)
    S (topFormPushforward_smooth E hE a δ hδ hcδ hsδ) (topFormPushforward_compact E a δ hcδ hsδ)
  have huSource : closure {x | u x ≠ (0 : NQForm E 1) x} ⊆ bundleChartSource (r := r) E a := by
    apply (oneFormPushforward_support E a F hc hs).trans
    rintro x ⟨z, hz, rfl⟩
    exact ⟨(extChartAt (ComplexModel n) a).map_target (hs hz).1, (hs hz).2⟩
  have hPzero (x : M.Carrier) (hx : x ∉ bundleChartSource (r := r) E a) : P x = 0 := by
    have hux : u x = (0 : NQForm E 1) x := by exact dif_neg hx
    have hfx : f x = (0 : NQForm E 2) x := by exact dif_neg hx
    have hSx : S x = (0 : NQForm E 0) x := by exact dif_neg hx
    have hpx := positiveFormEnergy_eq_zero_off_support (r := r) E g.form h φ u x (fun h => hx (huSource h))
    have hcx := curvatureFormEnergy_eq_zero_of_value_zero (r := r) E g.form h φ u x hux
    change BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) +
      BundleDbar.formNormSq (r := r) E g.form h S x * Real.exp (-φ x) -
      positiveFormEnergy (r := r) E g.form h φ u x - curvatureFormEnergy (r := r) E g.form h φ u x = 0
    rw [formNormSq_congr_at E g.form h f (0 : NQForm E 2) x hfx,
      formNormSq_congr_at E g.form h S (0 : NQForm E 0) x hSx, formNormSq_zero, formNormSq_zero,
      hpx, hcx]
    ring
  have hQzero (z : ComplexVector n) (hz : z ∉ chartTarget a) : Q z = 0 := by
    exact Set.indicator_of_notMem (fun h => hz h.1) J
  have hlocal (z : ComplexVector n) (hz : z ∈ chartTarget a) :
      Real.sqrt (realMetricFn g.form a z).det * P (chartInv a z) = (2 : ℝ) ^ n * Q z := by
    by_cases hzo : z ∈ O
    · change Real.sqrt (realMetricFn g.form a z).det *
        bknResidual (r := r) E g.form h φ u f S (chartInv a z) = _
      rw [bknResidual_oneFormPushforward_inChart E hE g h hh φ hφ a F hF hc hs z hzo,
        realMetricFn_sqrt_det g.form a z hz]
      rw [show Q z = J z from Set.indicator_of_mem hzo J]
      change ((2 : ℝ) ^ n * (hMat g.form a z).det.re) *
        (((hMat g.form a z).det.re)⁻¹ * J z) = (2 : ℝ) ^ n * J z
      field_simp [ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz)]
    · rw [hPzero _ (fun hx => hzo ⟨hz, hx.2⟩), show Q z = 0 from Set.indicator_of_notMem hzo J]
      ring
  have hi := integral_of_compact_chart_density_real g μ hμ a P Q hP
    (fun x hx => hPzero x (fun hy => hx hy.1)) hQzero hlocal
  have hJ : (∫ z in O, J z ∂lebesgueC n) = 0 :=
    (weighted_local_bkn_integral E g h hh φ hφ a F hF hc hs).2
  change (∫ x, P x ∂μ) = 0
  rw [hi]
  change (2 : ℝ) ^ n * ∫ z, O.indicator J z ∂lebesgueC n = 0
  rw [integral_indicator (localDomain_isOpen E a).measurableSet, hJ, mul_zero]

theorem bknResidual_oneFormPushforward_integrable (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    Integrable (bknResidual (r := r) E g.form h φ (oneFormPushforward (r := r) E a F)
      (twoFormPushforward (r := r) E a (modelOneDbar F))
      (topFormPushforward (r := r) E a (chartDbarAdjoint (r := r) E g.form h φ a F))) μ := by
  let δ := chartDbarAdjoint (r := r) E g.form h φ a F
  have hδ := chartDbarAdjoint_contDiff E g h hh φ hφ a F hF hs
  have hsδ := (tsupport_chartDbarAdjoint_subset E g.form h φ a F).trans hs
  have hcδ : HasCompactSupport δ := hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_chartDbarAdjoint_subset E g.form h φ a F)
  have hsD := (tsupport_modelOneDbar_subset F).trans hs
  have hcD : HasCompactSupport (modelOneDbar F) := hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_modelOneDbar_subset F)
  exact bknResidual_integrable E hE g μ hμ h hh φ hφ _
    (oneFormPushforward_smooth E hE a F hF hc hs) (oneFormPushforward_compact E a F hc hs)
    _ (twoFormPushforward_smooth E hE a _ (modelOneDbar_skew F) (modelOneDbar_contDiff F hF) hcD hsD)
      (twoFormPushforward_compact E a _ hcD hsD)
    _ (topFormPushforward_smooth E hE a δ hδ hcδ hsδ) (topFormPushforward_compact E a δ hcδ hsδ)

end Yau.LeafProofs.L14Aux
