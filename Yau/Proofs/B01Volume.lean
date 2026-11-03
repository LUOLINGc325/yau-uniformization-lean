import Yau.Proofs.B01Metric

open scoped Manifold Topology ContDiff ENNReal Matrix
open MeasureTheory Set

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

private def complexOneRealEquiv : ℂ ≃ₗᵢ[ℝ] ComplexVector 1 :=
  { complexOneEquiv.toLinearEquiv.restrictScalars ℝ with
    norm_map' := complexOneEquiv.norm_map }

theorem complexOneEquiv_measurePreserving :
    MeasurePreserving complexOneEquiv (volume : Measure ℂ) (volume : Measure (ComplexVector 1)) :=
  complexOneRealEquiv.measurePreserving

theorem complexOneEquiv_symm_measurePreserving :
    MeasurePreserving complexOneEquiv.symm (volume : Measure (ComplexVector 1)) (volume : Measure ℂ) :=
  complexOneRealEquiv.symm.measurePreserving

theorem complexLinearMap_real_det (A : ℂ →L[ℂ] ℂ) :
    (A.restrictScalars ℝ).det = Complex.normSq (A 1) := by
  change (A.toLinearMap.restrictScalars ℝ).det = _
  rw [LinearMap.det_restrictScalars, LinearMap.det_ring, Algebra.norm_complex_eq]
  rfl

theorem complexOneEquiv_one : complexOneEquiv (1 : ℂ) = stdVec 0 := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [stdVec]

variable {M : ComplexManifold 1}

theorem discArea_apply_image (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (s : Set M.Carrier) (hs : MeasurableSet s) :
    BundlePresentation.discArea c s = (volume : Measure ℂ) (c '' s) := by
  have hme := disc_measurableEmbedding c hc
  have he := congrArg (fun ν : Measure ℂ => ν (c '' s)) (discArea_map c hc)
  rw [hme.map_apply, hme.injective.preimage_image,
    Measure.restrict_apply (hme.measurableSet_image' hs)] at he
  have hsub : c '' s ⊆ puncturedUnitDisc := by
    rintro _ ⟨x, _, rfl⟩
    exact disc_mem c hc x
  simpa only [Set.inter_eq_left.mpr hsub] using he

theorem flatDiscField_hMat_det (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {z : ComplexVector 1} (hz : z ∈ chartTarget a) :
    (hMat (flatDiscField c hc) a z).det =
      (Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0)) : ℂ) := by
  rw [Matrix.det_fin_one]
  change (1 : ℂ) * star (discDerivative c (chartInv a z) (chartVec a (chartInv a z) (stdVec 0))) *
    discDerivative c (chartInv a z) (chartVec a (chartInv a z) (stdVec 0)) = _
  rw [one_mul, discDerivative_chartVec c hc a hz]
  rw [mul_comm, Complex.star_def, Complex.mul_conj]

theorem flatDiscField_volumeDensity (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {z : ComplexVector 1} (hz : z ∈ chartTarget a) :
    Real.sqrt (realMetricFn (flatDiscField c hc) a z).det =
      2 * Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0)) := by
  rw [LeafProofs.realMetricFn_sqrt_det _ _ _ hz, flatDiscField_hMat_det c hc a hz]
  simp only [pow_one, Complex.ofReal_re]

theorem chartImage_measurableSet (a : M.Carrier) (s : Set M.Carrier)
    (hs : MeasurableSet s) (hsub : s ⊆ (chartAt (ComplexVector 1) a).source) :
    MeasurableSet (chartPt a '' s) := by
  have he : s ∩ (extChartAt (ComplexModel 1) a).source = s :=
    Set.inter_eq_left.mpr (by simpa only [extChartAt_source] using hsub)
  rw [← he, LeafProofs.chart_image_eq_extension_preimage]
  exact (hs.preimage (LeafProofs.chartInvExtension_measurable a)).inter
    (isOpen_extChartAt_target (I := ComplexModel 1) a).measurableSet

def scalarChartMap (c : DiscCoordinate M) (a : M.Carrier) (t : ℂ) : ℂ :=
  c (chartInv a (complexOneEquiv t))

def scalarChartDerivative (c : DiscCoordinate M) (a : M.Carrier) (t : ℂ) : ℂ →L[ℂ] ℂ :=
  (fderiv ℂ (fun w => c (chartInv a w)) (complexOneEquiv t)).comp
    complexOneEquiv.toContinuousLinearEquiv.toContinuousLinearMap

theorem scalarChartMap_hasFDerivAt (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {t : ℂ} (ht : complexOneEquiv t ∈ chartTarget a) :
    HasFDerivAt (scalarChartMap c a) (scalarChartDerivative c a t) t :=
  ((disc_inChart_contDiffAt c hc a ht).differentiableAt (by simp)).hasFDerivAt.comp t
    complexOneEquiv.toContinuousLinearEquiv.hasFDerivAt

theorem scalarChartDerivative_real_det (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {t : ℂ} (ht : complexOneEquiv t ∈ chartTarget a) :
    ((scalarChartDerivative c a t).restrictScalars ℝ).det =
      Complex.normSq (wirt (fun w => c (chartInv a w)) (complexOneEquiv t) (stdVec 0)) := by
  rw [complexLinearMap_real_det]
  change Complex.normSq (fderiv ℂ (fun w => c (chartInv a w)) (complexOneEquiv t)
    (complexOneEquiv (1 : ℂ))) = _
  rw [complexOneEquiv_one, LeafProofs.L14Aux.wirt_eq_fderiv_of_complex_differentiable
    _ _ _ ((disc_inChart_contDiffAt c hc a ht).differentiableAt (by simp))]

theorem scalarChart_lintegral (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) (s : Set M.Carrier) (hs : MeasurableSet s)
    (hsub : s ⊆ (chartAt (ComplexVector 1) a).source) (G : ℂ → ℝ≥0∞) :
    (∫⁻ z in c '' s, G z ∂(volume : Measure ℂ)) =
      ∫⁻ z in chartPt a '' s, ENNReal.ofReal
        (Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0))) * G (c (chartInv a z))
          ∂(volume : Measure (ComplexVector 1)) := by
  let S : Set ℂ := complexOneEquiv ⁻¹' (chartPt a '' s)
  have hS : MeasurableSet S :=
    (chartImage_measurableSet a s hs hsub).preimage complexOneEquiv.continuous.measurable
  have htarget {t : ℂ} (ht : t ∈ S) : complexOneEquiv t ∈ chartTarget a := by
    obtain ⟨x, hx, he⟩ := ht
    rw [← he]
    exact (extChartAt (ComplexModel 1) a).map_source (by simpa only [extChartAt_source] using hsub hx)
  have hinj : InjOn (scalarChartMap c a) S := by
    intro t ht u hu he
    apply complexOneEquiv.injective
    have hx := disc_injective c hc he
    exact ((extChartAt (ComplexModel 1) a).right_inv (htarget ht)).symm.trans
      ((congrArg (chartPt a) hx).trans ((extChartAt (ComplexModel 1) a).right_inv (htarget hu)))
  have himage : scalarChartMap c a '' S = c '' s := by
    ext y
    constructor
    · rintro ⟨t, ⟨x, hx, he⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      unfold scalarChartMap
      rw [← he]
      exact congrArg c ((extChartAt (ComplexModel 1) a).left_inv
        (by simpa only [extChartAt_source] using hsub hx)).symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨complexOneEquiv.symm (chartPt a x), ?_, ?_⟩
      · change complexOneEquiv (complexOneEquiv.symm (chartPt a x)) ∈ chartPt a '' s
        rw [complexOneEquiv.apply_symm_apply]
        exact ⟨x, hx, rfl⟩
      · unfold scalarChartMap
        rw [complexOneEquiv.apply_symm_apply]
        exact congrArg c ((extChartAt (ComplexModel 1) a).left_inv
          (by simpa only [extChartAt_source] using hsub hx))
  have hJ := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := (volume : Measure ℂ))
    hS (fun t ht => ((scalarChartMap_hasFDerivAt c hc a (htarget ht)).restrictScalars ℝ).hasFDerivWithinAt)
    hinj G
  rw [himage] at hJ
  have hJ' : (∫⁻ z in c '' s, G z ∂(volume : Measure ℂ)) =
      ∫⁻ t in S, ENNReal.ofReal (Complex.normSq
        (wirt (fun w => c (chartInv a w)) (complexOneEquiv t) (stdVec 0))) *
          G (c (chartInv a (complexOneEquiv t))) ∂volume := by
    apply hJ.trans
    apply setLIntegral_congr_fun hS
    intro t ht
    change ENNReal.ofReal |((scalarChartDerivative c a t).restrictScalars ℝ).det| *
        G (c (chartInv a (complexOneEquiv t))) =
      ENNReal.ofReal (Complex.normSq (wirt (fun w => c (chartInv a w)) (complexOneEquiv t) (stdVec 0))) *
        G (c (chartInv a (complexOneEquiv t)))
    rw [scalarChartDerivative_real_det c hc a (htarget ht), abs_of_nonneg (Complex.normSq_nonneg _)]
  exact hJ'.trans (complexOneEquiv_measurePreserving.setLIntegral_comp_preimage_emb
    complexOneEquiv.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
      (fun z : ComplexVector 1 => ENNReal.ofReal (Complex.normSq
        (wirt (fun w => c (chartInv a w)) z (stdVec 0))) * G (c (chartInv a z))) (chartPt a '' s))

theorem scalarChart_area (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) (s : Set M.Carrier) (hs : MeasurableSet s)
    (hsub : s ⊆ (chartAt (ComplexVector 1) a).source) :
    (volume : Measure ℂ) (c '' s) =
      ∫⁻ z in chartPt a '' s, ENNReal.ofReal
        (Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0)))
          ∂(volume : Measure (ComplexVector 1)) := by
  simpa only [setLIntegral_one, mul_one] using scalarChart_lintegral c hc a s hs hsub (fun _ => 1)

theorem flatDiscField_volume (c : DiscCoordinate M) (hc : IsDiscCoordinate c) :
    IsRiemannianVolume (flatDiscField c hc) ((2 : ℝ≥0∞) • BundlePresentation.discArea c) := by
  intro a s hs hsub
  rw [Measure.smul_apply, smul_eq_mul, discArea_apply_image c hc s hs,
    scalarChart_area c hc a s hs hsub]
  rw [LeafProofs.lebesgueC_eq_volume]
  rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply setLIntegral_congr_fun (chartImage_measurableSet a s hs hsub)
  rintro z ⟨x, hx, rfl⟩
  have hz : chartPt a x ∈ chartTarget a :=
    (extChartAt (ComplexModel 1) a).map_source (by simpa only [extChartAt_source] using hsub hx)
  change (2 : ℝ≥0∞) * ENNReal.ofReal (Complex.normSq
      (wirt (fun w => c (chartInv a w)) (chartPt a x) (stdVec 0))) =
    ENNReal.ofReal (Real.sqrt (realMetricFn (flatDiscField c hc) a (chartPt a x)).det)
  rw [flatDiscField_volumeDensity c hc a hz, ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem setLIntegral_discArea_image (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (s : Set M.Carrier) (hs : MeasurableSet s) (F : M.Carrier → ℝ≥0∞) :
    (∫⁻ x in s, F x ∂BundlePresentation.discArea c) =
      ∫⁻ z in c '' s, F (c.symm z) ∂(volume : Measure ℂ) := by
  have hsub : c '' s ⊆ puncturedUnitDisc := by
    rintro _ ⟨x, _, rfl⟩
    exact disc_mem c hc x
  have he := setLIntegral_discArea c hc (c '' s)
    ((disc_measurableEmbedding c hc).measurableSet_image' hs) hsub F
  rw [(disc_injective c hc).preimage_image] at he
  exact he

theorem discPullbackMetric_volumeDensity (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (η : ℂ → ℝ) (hη : ∀ z ∈ puncturedUnitDisc, 0 < η z)
    (a : M.Carrier) {z : ComplexVector 1} (hz : z ∈ chartTarget a) :
    Real.sqrt (realMetricFn (discPullbackMetric c hc η hη) a z).det =
      2 * η (c (chartInv a z)) *
        Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0)) := by
  have hd : (hMat (discPullbackMetric c hc η hη) a z).det =
      (η (c (chartInv a z)) : ℂ) *
        (Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0)) : ℂ) := by
    rw [Matrix.det_fin_one]
    change (η (c (chartInv a z)) : ℂ) *
      star (discDerivative c (chartInv a z) (chartVec a (chartInv a z) (stdVec 0))) *
        discDerivative c (chartInv a z) (chartVec a (chartInv a z) (stdVec 0)) = _
    rw [discDerivative_chartVec c hc a hz]
    rw [mul_assoc, mul_comm (star _) _, Complex.star_def, Complex.mul_conj]
  rw [LeafProofs.realMetricFn_sqrt_det _ _ _ hz, hd]
  simp only [pow_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

def discPullbackMeasure (c : DiscCoordinate M) (η : ℂ → ℝ) : Measure M.Carrier :=
  (BundlePresentation.discArea c).withDensity (fun x => ENNReal.ofReal (2 * η (c x)))

theorem discPullbackMetric_volume (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (η : ℂ → ℝ) (hη : ∀ z ∈ puncturedUnitDisc, 0 < η z) :
    IsRiemannianVolume (discPullbackMetric c hc η hη) (discPullbackMeasure c η) := by
  intro a s hs hsub
  rw [discPullbackMeasure, withDensity_apply _ hs,
    setLIntegral_discArea_image c hc s hs, LeafProofs.lebesgueC_eq_volume]
  calc
    (∫⁻ z in c '' s, ENNReal.ofReal (2 * η (c (c.symm z))) ∂(volume : Measure ℂ)) =
        ∫⁻ z in c '' s, ENNReal.ofReal (2 * η z) ∂(volume : Measure ℂ) := by
      apply setLIntegral_congr_fun ((disc_measurableEmbedding c hc).measurableSet_image' hs)
      rintro z ⟨x, hx, rfl⟩
      change ENNReal.ofReal (2 * η (c (c.symm (c x)))) = ENNReal.ofReal (2 * η (c x))
      rw [disc_left_inv c hc]
    _ = ∫⁻ z in chartPt a '' s,
        ENNReal.ofReal (Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0))) *
          ENNReal.ofReal (2 * η (c (chartInv a z))) ∂(volume : Measure (ComplexVector 1)) :=
      scalarChart_lintegral c hc a s hs hsub (fun z => ENNReal.ofReal (2 * η z))
    _ = _ := by
      apply setLIntegral_congr_fun (chartImage_measurableSet a s hs hsub)
      rintro z ⟨x, hx, rfl⟩
      have hz : chartPt a x ∈ chartTarget a := (extChartAt (ComplexModel 1) a).map_source
        (by simpa only [extChartAt_source] using hsub hx)
      change ENNReal.ofReal (Complex.normSq
          (wirt (fun w => c (chartInv a w)) (chartPt a x) (stdVec 0))) *
          ENNReal.ofReal (2 * η (c (chartInv a (chartPt a x)))) =
        ENNReal.ofReal (Real.sqrt (realMetricFn (discPullbackMetric c hc η hη) a (chartPt a x)).det)
      rw [← ENNReal.ofReal_mul (Complex.normSq_nonneg _), discPullbackMetric_volumeDensity c hc η hη a hz]
      congr 1
      ring

end Yau.Proofs.B01Aux
