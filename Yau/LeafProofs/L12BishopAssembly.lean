import Yau.LeafProofs.L12ExponentialChangeVariables
import Yau.LeafProofs.L12NullImage
import Yau.LeafProofs.L12ExponentialInjective

/-! Bishop--Gromov assembly from positivity of the actual minimizing Jacobi
matrix. The remaining geometric dependency is an ordinary theorem parameter. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff InnerProductSpace ComplexOrder

namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-- Positivity of the genuine Jacobi determinant strictly before the endpoint
of an actually minimizing geodesic. -/
def MinimizingJacobiPositiveTarget (g : SmoothMetric M) : Prop :=
  ∀ p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier, ∀ T : ℝ, 0 < T →
    (letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
     inducedDistance g.form p.proj (realGeodesicFlow g p T).proj = T * ‖p.2‖) →
    ∀ t ∈ Set.Ioo 0 T, 0 < (realGeodesicJacobiMatrix g p t).det

/-- Physical radial vectors strictly before their minimizing endpoint and
inside the radius under consideration. -/
def realStrictRadialBall (g : SmoothMetric M) (x : M.Carrier) (r : ℝ) :
    Set (TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  exact realStrictMinimizingVectors g x ∩ Metric.ball 0 r

theorem measurableSet_realStrictRadialBall (g : SmoothMetric M) (x : M.Carrier) (r : ℝ) :
    @MeasurableSet (TangentSpace 𝓘(ℝ, ComplexVector n) x) (borel _)
      (realStrictRadialBall g x r) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  exact (measurableSet_realStrictMinimizingVectors g x).inter measurableSet_ball

/-- The omitted endpoint vectors have null image, so the strict radial
domain has exactly the volume of the genuine distance ball. -/
theorem distBall_volume_eq_strictRadial_integral (g : SmoothMetric M) (x : M.Carrier)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) {r : ℝ} (hr : 0 < r) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
    μ (distBall g.form x r) = ∫⁻ v in realStrictRadialBall g x r,
      ENNReal.ofReal (realExponentialVolumeDensity g x v) ∂realTangentVolume g x := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  have hsub : realExponentialMap g x '' realStrictRadialBall g x r ⊆ distBall g.form x r := by
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
  have heq : μ (distBall g.form x r) =
      μ (realExponentialMap g x '' realStrictRadialBall g x r) := by
    apply le_antisymm _ (measure_mono hsub)
    calc
      μ (distBall g.form x r) ≤ μ ((realExponentialMap g x '' realStrictRadialBall g x r) ∪
          (realExponentialMap g x '' realCutEndpointVectors g x)) := measure_mono hcover
      _ ≤ μ (realExponentialMap g x '' realStrictRadialBall g x r) +
          μ (realExponentialMap g x '' realCutEndpointVectors g x) := measure_union_le _ _
      _ = _ := by rw [realExponentialMap_cutEndpointVectors_image_measure_zero g x μ hμ, add_zero]
  rw [heq]
  exact realExponentialMap_image_volume g x μ hμ _
    (measurableSet_realStrictRadialBall g x r)
    ((realExponentialMap_injOn_strictMinimizingVectors g x).mono inter_subset_left)

/-- Genuine radial density comparison on the strict minimizing domain. -/
theorem realExponentialVolumeDensity_inv_smul_le (g : SmoothMetric M)
    (hK : IsKahler g) (hR : ∀ x, (ricci g.form x).PosSemidef)
    (hpositive : MinimizingJacobiPositiveTarget g) (x : M.Carrier)
    {v : TangentSpace 𝓘(ℝ, ComplexVector n) x}
    (hv : v ∈ realStrictMinimizingVectors g x) {c : ℝ} (hc : 1 ≤ c) :
    realExponentialVolumeDensity g x v ≤ realExponentialVolumeDensity g x (c⁻¹ • v) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  obtain ⟨q, hq⟩ := hv
  have hq1 : 1 < (q.val : ℝ) := by exact_mod_cast q.property
  have hqpos : 0 < (q.val : ℝ) := zero_lt_one.trans hq1
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, v⟩
  have hmin : inducedDistance g.form p.proj (realGeodesicFlow g p q.val).proj =
      (q.val : ℝ) * ‖p.2‖ := by
    change inducedDistance g.form x (realGeodesicFlow g ⟨x, v⟩ q.val).proj = _
    rw [← realExponentialMap_smul]
    change inducedDistance g.form x (realExponentialMap g x ((q.val : ℝ) • v)) = _ at hq ⊢
    rw [hq, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos]
  have hdet := hpositive p q.val hqpos hmin
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hi1 : c⁻¹ ≤ 1 := (inv_le_one₀ hcpos).mpr hc
  have h := realExponentialVolumeDensity_radial_antitone g hK hR p q.val hdet
    ⟨inv_pos.mpr hcpos, hi1.trans_lt hq1⟩ ⟨zero_lt_one, hq1⟩ hi1
  simpa only [p, one_smul] using h

private theorem setLIntegral_dilate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsAddHaarMeasure ν] {c : ℝ} (hc : 0 < c)
    (s : Set E) (f : E → ℝ≥0∞) :
    ∫⁻ v in s, f v ∂ν = ENNReal.ofReal (c ^ Module.finrank ℝ E) *
      ∫⁻ v in (fun w : E => c • w) ⁻¹' s, f (c • v) ∂ν := by
  have he : MeasurableEmbedding (fun v : E => c⁻¹ • v) :=
    (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc.ne')).measurableEmbedding
  have hpre : (fun v : E => c⁻¹ • v) ⁻¹' ((fun w : E => c • w) ⁻¹' s) = s := by
    ext v
    simp only [mem_preimage, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have h : (∫⁻ v in (fun w : E => c • w) ⁻¹' s, f (c • v)
      ∂ν.map (fun v : E => c⁻¹ • v)) = ∫⁻ v in s, f v ∂ν := by
    rw [he.restrict_map, he.lintegral_map, hpre]
    simp only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [map_addHaar_smul ν (inv_ne_zero hc.ne'), Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul, inv_pow, inv_inv,
    abs_of_pos (pow_pos hc _)] at h
  exact h.symm

/-- The exact Bishop--Gromov inequality, conditional only on the ordinary
minimizing-Jacobi positivity theorem for this metric. -/
theorem distBall_volume_comparison_of_minimizingJacobiPositive
    (g : SmoothMetric M) (hK : IsKahler g) (hR : ∀ x, (ricci g.form x).PosSemidef)
    (hpositive : MinimizingJacobiPositiveTarget g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    μ (distBall g.form x R) ≤
      ENNReal.ofReal ((R / r) ^ (2 * n)) * μ (distBall g.form x r) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  let ν := realTangentVolume g x
  letI : IsAddHaarMeasure ν := realTangentVolume_isAddHaarMeasure g x
  let c := R / r
  have hc1 : 1 ≤ c := (one_le_div hr).mpr hrR
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hcR : c * r = R := div_mul_cancel₀ _ hr.ne'
  let s := realStrictRadialBall g x R
  let a := (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) x => c • v) ⁻¹' s
  have ha : MeasurableSet a :=
    (measurableSet_realStrictRadialBall g x R).preimage (measurable_const_smul c)
  have hasub : a ⊆ realStrictRadialBall g x r := by
    intro v hv
    change c • v ∈ realStrictRadialBall g x R at hv
    change v ∈ realStrictMinimizingVectors g x ∧ v ∈ Metric.ball 0 r
    have hvs := realStrictMinimizingVectors_smul g x hv.1 (inv_nonneg.mpr hc.le)
      ((inv_le_one₀ hc).mpr hc1)
    refine ⟨?_, ?_⟩
    · simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hvs
    · have hn : ‖c • v‖ < R := by
        simpa only [Metric.mem_ball, dist_zero_right] using hv.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← hcR] at hn
      simpa only [Metric.mem_ball, dist_zero_right] using (mul_lt_mul_iff_right₀ hc).mp hn
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) = 2 * n := by
    simpa only [Fintype.card_fin] using
      Module.finrank_eq_card_basis (realInitialOrthonormalFrame g x).toBasis
  rw [distBall_volume_eq_strictRadial_integral g x μ hμ (hr.trans_le hrR),
    distBall_volume_eq_strictRadial_integral g x μ hμ hr]
  calc
    _ = ENNReal.ofReal (c ^ (2 * n)) *
        ∫⁻ v in a, ENNReal.ofReal (realExponentialVolumeDensity g x (c • v)) ∂ν := by
      simpa only [hdim] using setLIntegral_dilate ν hc s
        (fun v => ENNReal.ofReal (realExponentialVolumeDensity g x v))
    _ ≤ ENNReal.ofReal (c ^ (2 * n)) *
        ∫⁻ v in a, ENNReal.ofReal (realExponentialVolumeDensity g x v) ∂ν := by
      apply mul_le_mul_right
      apply setLIntegral_mono' ha
      intro v hv
      have h := realExponentialVolumeDensity_inv_smul_le g hK hR hpositive x hv.1 hc1
      simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using ENNReal.ofReal_le_ofReal h
    _ ≤ _ := mul_le_mul_right (lintegral_mono_set hasub) _

/-- The frozen L12 obligation follows once actual minimizing-Jacobi positivity
has been proved for every metric. No new axiom or geometric field is added. -/
theorem bishopGromov_of_minimizingJacobiPositive
    (hpositive : ∀ (n : ℕ) (M : ComplexManifold n) (g : SmoothMetric M),
      MinimizingJacobiPositiveTarget g) : Yau.LeafObligations.L12 := by
  intro n M g _hComplete hK hR μ hμ x r R hr hrR
  exact distBall_volume_comparison_of_minimizingJacobiPositive g hK hR
    (hpositive n M g) μ hμ x hr hrR

end Yau.LeafProofs.L12Aux
