import Yau.LeafProofs.L18Moser
import Yau.LeafProofs.L18Sobolev
import Yau.LeafProofs.L18SegmentPoincare

/-! Scalar fundamental theorem estimates and the actual ball Poincaré
conclusion from the internally constructed minimizing segments. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal NNReal ContDiff ComplexOrder InnerProductSpace

namespace Yau.LeafProofs.L18Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The scalar fundamental theorem along the genuine complete radial
geodesic, with its actual constant speed. -/
theorem scalar_realExponential_oscillation_le (g : SmoothMetric M)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (a : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) a) :
    letI := underlyingRealTangentNormedAddCommGroup g.form a
    |u (realExponentialMap g a v) - u a| ≤
      ‖v‖ * ∫ t in Icc (0 : ℝ) 1,
        Real.sqrt (scalarGradientPair g.form u u (realExponentialMap g a (t • v))) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  let f : ℝ → M.Carrier := fun t => realExponentialMap g a (t • v)
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f :=
    (realExponentialMap_radial_contMDiff g a v).of_le (by simp)
  let γ := integrableCurve_of_contMDiff g hf
  have hFTC := scalar_curve_FTC g hu γ
  have hbad : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({0, 1} : Finset ℝ) :=
    ({0, 1} : Finset ℝ).finite_toSet.countable.ae_notMem volume
  have hspeed : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Icc (0 : ℝ) 1),
      curveSpeed g.form γ.1 t = ‖v‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hbad] with t ht hn
    have hn' : t ≠ 0 ∧ t ≠ 1 := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
    have ht' : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 hn'.1.symm, lt_of_le_of_ne ht.2 hn'.2⟩
    have hnorm := realCurveVelocity_norm g.form γ.1 ht'
      (by simp [γ, integrableCurve_of_contMDiff, piecewiseC1Curve_of_contMDiff])
    rw [← hnorm]
    exact realExponentialMap_radial_speed g a v t
  have hInt : (∫ t in Icc (0 : ℝ) 1,
      Real.sqrt (scalarGradientPair g.form u u (γ.1 t)) * curveSpeed g.form γ.1 t) =
      ‖v‖ * ∫ t in Icc (0 : ℝ) 1,
        Real.sqrt (scalarGradientPair g.form u u (f t)) := by
    calc
      _ = ∫ t in Icc (0 : ℝ) 1,
          Real.sqrt (scalarGradientPair g.form u u (f t)) * ‖v‖ := by
        apply integral_congr_ae
        filter_upwards [hspeed] with t ht
        rw [ht]
        rfl
      _ = _ := by rw [integral_mul_const]; ring
  rw [hInt] at hFTC
  change |u (f 1) - u (f 0)| ≤ _ at hFTC
  simpa only [f, one_smul, zero_smul, realExponentialMap_zero] using hFTC

/-- The nonnegative integral version of the scalar estimate on an actual
minimizing radial vector. All time-integrability is obtained from smoothness. -/
theorem scalar_minimizing_realExponential_lintegral_le (g : SmoothMetric M)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (a : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) a)
    (hv : v ∈ realMinimizingVectors g a) :
    ENNReal.ofReal |u (realExponentialMap g a v) - u a| ≤
      ENNReal.ofReal (inducedDistance g.form a (realExponentialMap g a v)) *
        ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
          (Real.sqrt (scalarGradientPair g.form u u (realExponentialMap g a (t • v)))) := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form a
  have hc : Continuous (fun t : ℝ =>
      Real.sqrt (scalarGradientPair g.form u u (realExponentialMap g a (t • v)))) :=
    (Real.continuous_sqrt.comp (continuous_of_smoothFn
      (smoothFn_scalarGradientPair g hu hu))).comp
        (realExponentialMap_radial_contMDiff g a v).continuous
  have hi : IntegrableOn (fun t : ℝ =>
      Real.sqrt (scalarGradientPair g.form u u (realExponentialMap g a (t • v))))
      (Icc (0 : ℝ) 1) (volume : Measure ℝ) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  have h := ENNReal.ofReal_le_ofReal (scalar_realExponential_oscillation_le g hu a v)
  rw [ENNReal.ofReal_mul (norm_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun t => Real.sqrt_nonneg _))] at h
  change inducedDistance g.form a (realExponentialMap g a v) = ‖v‖ at hv
  rwa [hv]

/-- The measurable genuine selected segment controls the scalar
oscillation at every strict endpoint pair. -/
theorem scalar_oscillation_le_realSegmentIntegral (g : SmoothMetric M)
    (o : M.Carrier) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    {z : M.Carrier × M.Carrier} (hz : z ∈ realStrictEndpointPairs g) :
    ENNReal.ofReal |u z.1 - u z.2| ≤ realSegmentIntegral g o
      (fun y => ENNReal.ofReal (Real.sqrt (scalarGradientPair g.form u u y))) z := by
  obtain ⟨p, rfl⟩ := hz
  rcases p with ⟨⟨a, v⟩, hv⟩
  have h := scalar_minimizing_realExponential_lintegral_le g hu a v
    (realStrictMinimizingVectors_subset g a hv)
  change ENNReal.ofReal |u a - u (realExponentialMap g a v)| ≤ _
  change ENNReal.ofReal |u (realExponentialMap g a v) - u a| ≤ _ at h
  rw [abs_sub_comm]
  convert h using 1
  unfold realSegmentIntegral
  congr 1
  apply lintegral_congr
  intro t
  change ENNReal.ofReal (Real.sqrt (scalarGradientPair g.form u u
    (realSelectedSegment g o (a, realExponentialMap g a v) t))) = _
  rw [realSelectedSegment_exp g o a v hv t]

/-- The actual finite positive ball volume turns a nonnegative pairwise
oscillation bound into the scalar Poincaré conclusion. -/
theorem scalar_ball_poincare_of_pair_lintegral_bound (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (o : M.Carrier) {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hPair : (∫⁻ z, ENNReal.ofReal |u z.1 - u z.2|
        ∂(μ.restrict (distBall g.form o r)).prod (μ.restrict (distBall g.form o r))) ≤
      ENNReal.ofReal (C * r) * μ (distBall g.form o r) *
        ∫⁻ y in distBall g.form o (3 * r),
          ENNReal.ofReal (Real.sqrt (scalarGradientPair g.form u u y)) ∂μ) :
    (∫ y in distBall g.form o r,
      |u y - (μ.real (distBall g.form o r))⁻¹ * ∫ z in distBall g.form o r, u z ∂μ| ∂μ) ≤
      C * r * ∫ y in distBall g.form o (3 * r),
        Real.sqrt (scalarGradientPair g.form u u y) ∂μ := by
  let B := distBall g.form o r
  let ν := μ.restrict B
  let V := μ.real B
  have hBfin : μ B < ⊤ := riemannianVolume_distBall_lt_top g μ hμ o hr
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ o hr).ne' hBfin.ne
  letI : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hBfin⟩
  have hiu : Integrable u ν := smoothFn_integrableOn_distBall g μ hμ hu o hr
  have hiPair : Integrable (fun z : M.Carrier × M.Carrier => |u z.1 - u z.2|) (ν.prod ν) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hiu.comp_fst ν).sub (hiu.comp_snd ν)).norm
  have hiG : IntegrableOn (fun y => Real.sqrt (scalarGradientPair g.form u u y))
      (distBall g.form o (3 * r)) μ := continuous_integrableOn_distBall g μ hμ
    (Real.continuous_sqrt.comp (continuous_of_smoothFn (smoothFn_scalarGradientPair g hu hu)))
      o (by positivity)
  have hPairReal : (∫ z : M.Carrier × M.Carrier, |u z.1 - u z.2| ∂ν.prod ν) ≤
      C * r * V * ∫ y in distBall g.form o (3 * r),
        Real.sqrt (scalarGradientPair g.form u u y) ∂μ := by
    have h := hPair
    rw [← ofReal_integral_eq_lintegral_ofReal hiPair (ae_of_all _ (fun _ => abs_nonneg _)),
      ← ofReal_integral_eq_lintegral_ofReal hiG (ae_of_all _ (fun _ => Real.sqrt_nonneg _))] at h
    have hvolume : μ B = ENNReal.ofReal V := (ENNReal.ofReal_toReal hBfin.ne).symm
    change ENNReal.ofReal _ ≤ ENNReal.ofReal (C * r) * μ B * ENNReal.ofReal _ at h
    rw [hvolume, ← ENNReal.ofReal_mul (mul_nonneg hC hr.le),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC hr.le) hV.le)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
      (mul_nonneg (mul_nonneg hC hr.le) hV.le)
      (integral_nonneg (fun y => Real.sqrt_nonneg _)))).mp h
  have hAvg := integral_distBall_abs_sub_average_le_pairwise g μ hμ hu o hr
  have hDouble : (∫ y in B, ∫ z in B, |u y - u z| ∂μ ∂μ) =
      ∫ z : M.Carrier × M.Carrier, |u z.1 - u z.2| ∂ν.prod ν :=
    (integral_prod _ hiPair).symm
  rw [hDouble] at hAvg
  calc
    _ ≤ V⁻¹ * ∫ z : M.Carrier × M.Carrier, |u z.1 - u z.2| ∂ν.prod ν := hAvg
    _ ≤ V⁻¹ * (C * r * V * ∫ y in distBall g.form o (3 * r),
        Real.sqrt (scalarGradientPair g.form u u y) ∂μ) :=
      mul_le_mul_of_nonneg_left hPairReal (inv_nonneg.mpr hV.le)
    _ = _ := by field_simp

/-- The uniform Poincaré estimate is proved from actual minimizing
segments, their internally proved radial volume comparison, and scalar FTC. -/
theorem ballScalarPoincareEstimate (n : ℕ) :
    BallScalarPoincareEstimate n ((2 : ℝ) ^ (2 * n + 1)) := by
  intro M g _hc hK hRic μ hμ u hu o r hr
  apply scalar_ball_poincare_of_pair_lintegral_bound g μ hμ hu o hr (by positivity)
  let ν := μ.restrict (distBall g.form o r)
  letI : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using
    riemannianVolume_distBall_lt_top g μ hμ o hr⟩
  have hFull := lintegral_realSegmentIntegral_originalBall_le g hK hRic μ hμ o hr
    (fun y => ENNReal.ofReal (Real.sqrt (scalarGradientPair g.form u u y)))
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_of_smoothFn (smoothFn_scalarGradientPair g hu hu))).measurable)
  apply le_trans _ hFull
  apply lintegral_mono_ae
  filter_upwards [ae_realStrictEndpointPairs_both g μ hμ (distBall g.form o r)] with z hz
  exact scalar_oscillation_le_realSegmentIntegral g o hu hz.1

end Yau.LeafProofs.L18Aux
