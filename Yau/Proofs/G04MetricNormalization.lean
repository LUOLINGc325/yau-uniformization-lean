import Yau.Proofs.G01Realification
import Yau.LeafProofs.L18

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem realMetricInChart_apply_complex (h : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (u v : ComplexVector n) :
    L12Aux.realMetricInChart h x z u v =
      2 * ((h (chartInv x z)).toFun
        (chartVec x (chartInv x z) u) (chartVec x (chartInv x z) v)).re := by
  rw [L12Aux.realMetricInChart_apply, L12Aux.underlyingRealRiemannianMetric_inner,
    L12Aux.realTangentEquiv_realChartVec x z u hz,
    L12Aux.realTangentEquiv_realChartVec x z v hz]

theorem metricTensor (h : HermitianField M) : PaperMetricTensorNormalization h := by
  refine ⟨?_, ?_, ?_⟩
  · intro x z hz
    rw [G01Aux.realMetricFn_eq_rawReal,
      G01Aux.rawReal_eq_iota _ (L12Aux.hMat_isHermitian h x z)]
  · intro x u v
    have hx : chartInv x (chartPt x x) = x :=
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
    have hu : (∑ a, realCoord (tangentCoords x x u) a • chartVec x x (realVec a)) = u := by
      rw [← L12Aux.chartVec_real_sum, L12Aux.sum_realCoord_realVec,
        L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x)]
    have hv : (∑ a, realCoord (tangentCoords x x v) a • chartVec x x (realVec a)) = v := by
      rw [← L12Aux.chartVec_real_sum, L12Aux.sum_realCoord_realVec,
        L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x)]
    change (∑ a, ∑ b, 2 * ((h (chartInv x (chartPt x x))).toFun
      (chartVec x (chartInv x (chartPt x x)) (realVec a))
      (chartVec x (chartInv x (chartPt x x)) (realVec b))).re *
      realCoord (tangentCoords x x u) a * realCoord (tangentCoords x x v) b) = _
    rw [hx]
    change _ = L12Aux.hermitianRealBilin (h x) u v
    conv_rhs => rw [← hu, ← hv]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, L12Aux.hermitianRealBilin_apply]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro x u v
    have hx : chartInv x (chartPt x x) = x :=
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
    have hu : (∑ a, realCoord (tangentCoords x x u) a • chartVec x x (realVec a)) = u := by
      rw [← L12Aux.chartVec_real_sum, L12Aux.sum_realCoord_realVec,
        L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x)]
    have hv : (∑ a, realCoord (tangentCoords x x v) a • chartVec x x (realVec a)) = v := by
      rw [← L12Aux.chartVec_real_sum, L12Aux.sum_realCoord_realVec,
        L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x)]
    change (∑ a, ∑ b, 2 * ((h (chartInv x (chartPt x x))).toFun
      (chartVec x (chartInv x (chartPt x x)) (realVec a))
      (chartVec x (chartInv x (chartPt x x)) (realVec b))).im *
      realCoord (tangentCoords x x u) a * realCoord (tangentCoords x x v) b) = _
    rw [hx]
    let J : TangentVector M x →ₗ[ℝ] TangentVector M x :=
      (Complex.I • LinearMap.id (R := ℂ) (M := TangentVector M x)).restrictScalars ℝ
    let B := (L12Aux.hermitianRealBilin (h x)).comp J
    have hB (u v : TangentVector M x) : B u v = 2 * ((h x).toFun u v).im := by
      change 2 * ((h x).toFun (Complex.I • u) v).re = _
      rw [(h x).map_smul_left]
      simp [Complex.mul_re]
    rw [← hB]
    conv_rhs => rw [← hu, ← hv]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, hB]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring

theorem volumeGiven (h : HermitianField M) : PaperVolumeMeasureNormalization h := by
  intro μ hμ x s hs hsource
  rw [hμ x s hs (by simpa only [extChartAt_source] using hsource)]
  let e := chartAt (ComplexVector n) x
  have hs' : s ⊆ e.source := by simpa only [e, extChartAt_source] using hsource
  have hm : MeasurableSet (chartPt x '' s) := by
    have hpre : MeasurableSet ((fun z : e.target => e.symm z) ⁻¹' s) :=
      hs.preimage e.continuousOn_symm.domRestrict.measurable
    have himage := e.open_target.measurableSet.subtype_image hpre
    convert himage using 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨e y, e.map_source (hs' hy)⟩,
        by change e.symm (e y) ∈ s; rwa [e.left_inv (hs' hy)], rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.symm z, hz, e.right_inv z.property⟩
  apply setLIntegral_congr_fun hm
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hy' := hsource hy
  exact congrArg ENNReal.ofReal (L12Aux.paperVolumeNormalization h x (chartPt x y)
    ((extChartAt (ComplexModel n) x).map_source hy'))

theorem gradient (h : HermitianField M) : PaperGradientNormalization h := by
  intro f hf x
  have he := L18Aux.scalarGradientPair_eq_twice_gradNormSq h hf x
  change L18Aux.chartGradientPair h x (inChart x f) (inChart x f) (chartPt x x) = _ at he
  simpa only [realGradientNormSq, L18Aux.chartGradientPair_eq_sum] using he

theorem pullbackKahlerDensity_eq (h : HermitianField M)
    (f : ℂ → M.Carrier) (ζ : ℂ) :
    pullbackKahlerDensity h f ζ =
      2 * hermitianNormSq (h (f ζ)) (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) f ζ
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1)) := by
  let df := mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) f ζ
  let one := (tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1
  have hi : (tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm Complex.I = Complex.I • one := by
    simpa only [smul_eq_mul, mul_one] using
      ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm.map_smul Complex.I (1 : ℂ))
  change (∑ a, ∑ b, kahlerFormFn h (f ζ) (chartPt (f ζ) (f ζ)) a b *
    realCoord (tangentCoords (f ζ) (f ζ) (df one)) a *
    realCoord (tangentCoords (f ζ) (f ζ)
      (df ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm Complex.I))) b) = _
  rw [(metricTensor h).2.2, hi, map_smul, (h (f ζ)).map_smul_right]
  simp only [hermitianNormSq, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero]
  rfl

theorem disc (h : HermitianField M) : PaperDiscAreaNormalization h := by
  intro hs f hf
  refine ⟨fun ζ _ => pullbackKahlerDensity_eq h f ζ, ?_⟩
  unfold discArea
  simp_rw [pullbackKahlerDensity_eq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [ENNReal.ofReal_ofNat] using
    (lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).symm

theorem metricNormalization : PaperMetricNormalizationTarget := by
  intro n M h hs
  exact ⟨metricTensor h, L12Aux.paperLengthNormalization h,
    L12Aux.paperVolumeNormalization h, volumeGiven h,
    L18Aux.paperDualNormNormalization h, gradient h, disc h⟩

end Yau.NodeProofs.G04Aux
