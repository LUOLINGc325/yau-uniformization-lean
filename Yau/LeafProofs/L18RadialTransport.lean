import Yau.LeafProofs.L12BishopAssembly

/-! Weighted transport through the genuine exponential on the strict
minimizing radial domain. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff InnerProductSpace ComplexOrder

namespace Yau.LeafProofs.L18Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-- The actual exponential Gram density is continuous, including at
singular vectors. -/
theorem continuous_realExponentialVolumeDensity (g : SmoothMetric M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    Continuous (realExponentialVolumeDensity g x) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  letI := realRiemannianBundle_continuous g
  have hD (w : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
      Continuous (fun v =>
        (⟨realExponentialMap g x v, realExponentialDifferential g x v w⟩ :
          TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) := by
    have hconst : Continuous (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) x =>
        (⟨v, (NormedSpace.fromTangentSpace (𝕜 := ℝ) v).symm w⟩ :
          TangentBundle 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x)
            (TangentSpace 𝓘(ℝ, ComplexVector n) x))) := by
      exact (tangentBundleModelSpaceHomeomorph
        𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x)).symm.continuous.comp
          (continuous_id.prodMk continuous_const)
    exact ((realExponentialMap_contMDiff g x).continuous_tangentMap (by simp)).comp hconst
  have hGram : Continuous (realExponentialGramMatrix g x) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (hD (realInitialOrthonormalFrame g x i)).inner_bundle
      (hD (realInitialOrthonormalFrame g x j))
  exact hGram.matrix_det.sqrt

/-- The Riemannian measure on a distance ball is the pushforward of its
genuine exponential Gram density on the strict radial domain. -/
theorem distBall_restrict_eq_map_strictRadial (g : SmoothMetric M) (x : M.Carrier)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) {r : ℝ} (hr : 0 < r) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
    μ.restrict (distBall g.form x r) =
      Measure.map (realExponentialMap g x)
        (((realTangentVolume g x).restrict (realStrictRadialBall g x r)).withDensity
          (fun v => ENNReal.ofReal (realExponentialVolumeDensity g x v))) := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  have hExp : Measurable (realExponentialMap g x) :=
    (realExponentialMap_contMDiff g x).continuous.measurable
  have hs := measurableSet_realStrictRadialBall g x r
  have hsub : realExponentialMap g x '' realStrictRadialBall g x r ⊆
      distBall g.form x r := by
    rw [distBall_eq_realExponential_image_ball g x hr]
    exact image_mono inter_subset_right
  have hcover : distBall g.form x r ⊆
      (realExponentialMap g x '' realStrictRadialBall g x r) ∪
        (realExponentialMap g x '' realCutEndpointVectors g x) := by
    intro y hy
    have hd : inducedDistance g.form x y < r :=
      (ENNReal.ofReal_lt_ofReal_iff hr).mp hy
    obtain ⟨v, hv, hnorm⟩ := exists_minimizing_realExponential g x y
    have hvmin : v ∈ realMinimizingVectors g x := by
      change inducedDistance g.form x (realExponentialMap g x v) = ‖v‖
      rw [hv, hnorm]
    by_cases hvstrict : v ∈ realStrictMinimizingVectors g x
    · exact Or.inl ⟨v, ⟨hvstrict, by simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hd⟩, hv⟩
    · exact Or.inr ⟨v, ⟨hvmin, hvstrict⟩, hv⟩
  ext t ht
  calc
    μ.restrict (distBall g.form x r) t = μ (t ∩ distBall g.form x r) := restrict_apply ht
    _ = μ (realExponentialMap g x ''
        (realStrictRadialBall g x r ∩ realExponentialMap g x ⁻¹' t)) := by
      apply le_antisymm
      · calc
          μ (t ∩ distBall g.form x r) ≤
              μ ((realExponentialMap g x ''
                (realStrictRadialBall g x r ∩ realExponentialMap g x ⁻¹' t)) ∪
                  (realExponentialMap g x '' realCutEndpointVectors g x)) := by
            apply measure_mono
            intro y hy
            rcases hcover hy.2 with ⟨v, hv, rfl⟩ | hc
            · exact Or.inl ⟨v, ⟨hv, hy.1⟩, rfl⟩
            · exact Or.inr hc
          _ ≤ μ (realExponentialMap g x ''
                (realStrictRadialBall g x r ∩ realExponentialMap g x ⁻¹' t)) +
                  μ (realExponentialMap g x '' realCutEndpointVectors g x) := measure_union_le _ _
          _ = _ := by
            rw [realExponentialMap_cutEndpointVectors_image_measure_zero g x μ hμ, add_zero]
      · apply measure_mono
        rintro y ⟨v, hv, rfl⟩
        exact ⟨hv.2, hsub ⟨v, hv.1, rfl⟩⟩
    _ = ∫⁻ v in realStrictRadialBall g x r ∩ realExponentialMap g x ⁻¹' t,
        ENNReal.ofReal (realExponentialVolumeDensity g x v) ∂realTangentVolume g x :=
      realExponentialMap_image_volume g x μ hμ _ (hs.inter (hExp ht))
        ((realExponentialMap_injOn_strictMinimizingVectors g x).mono
          (inter_subset_left.trans inter_subset_left))
    _ = (Measure.map (realExponentialMap g x)
        (((realTangentVolume g x).restrict (realStrictRadialBall g x r)).withDensity
          (fun v => ENNReal.ofReal (realExponentialVolumeDensity g x v)))) t := by
      rw [Measure.map_apply hExp ht, withDensity_apply _ (hExp ht),
        restrict_restrict (hExp ht), inter_comm]

/-- Exact nonnegative weighted radial transport for the actual metric,
volume, exponential map, and physical tangent volume. -/
theorem distBall_lintegral_eq_strictRadial_integral (g : SmoothMetric M) (x : M.Carrier)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) {r : ℝ} (hr : 0 < r)
    (f : M.Carrier → ℝ≥0∞) (hf : Measurable f) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
    ∫⁻ y in distBall g.form x r, f y ∂μ =
      ∫⁻ v in realStrictRadialBall g x r,
        f (realExponentialMap g x v) *
          ENNReal.ofReal (realExponentialVolumeDensity g x v) ∂realTangentVolume g x := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  have hExp : Measurable (realExponentialMap g x) :=
    (realExponentialMap_contMDiff g x).continuous.measurable
  rw [distBall_restrict_eq_map_strictRadial g x μ hμ hr, lintegral_map hf hExp]
  simpa only [Pi.mul_apply, mul_comm] using
    (lintegral_withDensity_eq_lintegral_mul
      ((realTangentVolume g x).restrict (realStrictRadialBall g x r))
      (continuous_realExponentialVolumeDensity g x).measurable.ennreal_ofReal
      (show Measurable (fun v => f (realExponentialMap g x v)) from hf.comp hExp))

end Yau.LeafProofs.L18Aux
