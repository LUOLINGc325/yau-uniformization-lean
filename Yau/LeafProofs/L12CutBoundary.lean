import Yau.LeafProofs.L12MinimizingDomain

/-! Haar nullity of the actual radial endpoint vectors. The proof uses
finite bounded sets and infinitesimal dilation; no polar decomposition
or cut-locus measure hypothesis is assumed. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace Pointwise
namespace Yau.LeafProofs.L12Aux
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

/-- A finite-measure star-shaped set has a null radial endpoint set,
proved directly by Haar dilation rather than by a supplied polar formula. -/
theorem measure_radial_endpoint_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [IsAddHaarMeasure μ] (D C : Set E) (hD : MeasurableSet D) (hfin : μ D ≠ ⊤)
    (hstar : ∀ c : ℝ, 1 ≤ c → D ⊆ (fun v : E => c • v) '' D)
    (hend : ∀ c : ℝ, 1 < c → C ⊆ ((fun v : E => c • v) '' D) \ D) : μ C = 0 := by
  have hbound (c : ℝ) (hc : 1 < c) : μ C ≤ ENNReal.ofReal (c ^ Module.finrank ℝ E) * μ D - μ D := by
    have hmono : μ C ≤ μ (((fun v : E => c • v) '' D) \ D) := measure_mono (hend c hc)
    rw [measure_sdiff (hstar c hc.le) hD.nullMeasurableSet hfin] at hmono
    have hscale : μ ((fun v : E => c • v) '' D) =
        ENNReal.ofReal (c ^ Module.finrank ℝ E) * μ D := by
      change μ (c • D) = _
      exact μ.addHaar_smul_of_nonneg (zero_lt_one.trans hc).le D
    rwa [hscale] at hmono
  have hpow : Tendsto (fun c : ℝ => ENNReal.ofReal (c ^ Module.finrank ℝ E)) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun c : ℝ => ENNReal.ofReal (c ^ Module.finrank ℝ E)) := by
      simpa only [Function.comp_def] using ENNReal.continuous_ofReal.comp (continuous_pow (Module.finrank ℝ E))
    have h : Tendsto (fun c : ℝ => ENNReal.ofReal (c ^ Module.finrank ℝ E)) (𝓝 (1 : ℝ)) (𝓝 1) := by
      simpa only [one_pow, ENNReal.ofReal_one] using hc.tendsto (1 : ℝ)
    exact h.mono_left nhdsWithin_le_nhds
  have hmul := ENNReal.Tendsto.mul_const (b := μ D) hpow (Or.inr hfin)
  have hlim : Tendsto (fun c : ℝ => ENNReal.ofReal (c ^ Module.finrank ℝ E) * μ D - μ D)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa only [one_mul, tsub_self] using ENNReal.Tendsto.sub hmul tendsto_const_nhds (Or.inr hfin)
  apply le_antisymm ?_ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact hbound c hc

variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine radial cut-endpoint vectors have zero physical tangent
Haar measure in every bounded ball. -/
theorem realCutEndpointVectors_inter_closedBall_measure_zero (g : SmoothMetric M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
    ∀ μ : Measure (TangentSpace 𝓘(ℝ, ComplexVector n) x), IsAddHaarMeasure μ → ∀ R : ℝ,
      μ (realCutEndpointVectors g x ∩ Metric.closedBall 0 R) = 0 := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  intro μ hμ R
  letI : IsAddHaarMeasure μ := hμ
  let D := realStrictMinimizingVectors g x ∩ Metric.closedBall 0 R
  let C := realCutEndpointVectors g x ∩ Metric.closedBall 0 R
  have hD : MeasurableSet D := (measurableSet_realStrictMinimizingVectors g x).inter measurableSet_closedBall
  have hfin : μ D ≠ ⊤ := ((measure_mono inter_subset_right).trans_lt (isCompact_closedBall (0 : TangentSpace 𝓘(ℝ, ComplexVector n) x) R).measure_lt_top).ne
  have hnorm {c : ℝ} (hc : 1 ≤ c) {v : TangentSpace 𝓘(ℝ, ComplexVector n) x}
      (hv : v ∈ Metric.closedBall (0 : TangentSpace 𝓘(ℝ, ComplexVector n) x) R) :
      c⁻¹ • v ∈ Metric.closedBall (0 : TangentSpace 𝓘(ℝ, ComplexVector n) x) R := by
    have hcpos : 0 < c := zero_lt_one.trans_le hc
    have hi : c⁻¹ ≤ 1 := (inv_le_one₀ hcpos).mpr hc
    have hvnorm : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hcpos.le)]
    exact (mul_le_mul_of_nonneg_right hi (norm_nonneg v)).trans (by simpa using hvnorm)
  apply measure_radial_endpoint_eq_zero μ D C hD hfin
  · intro c hc v hv
    have hw := realStrictMinimizingVectors_smul g x hv.1 (inv_nonneg.mpr (zero_lt_one.trans_le hc).le)
      ((inv_le_one₀ (zero_lt_one.trans_le hc)).mpr hc)
    refine ⟨c⁻¹ • v, ⟨hw, hnorm hc hv.2⟩, ?_⟩
    dsimp only
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans_le hc)), one_smul]
  · intro c hc v hv
    refine ⟨⟨c⁻¹ • v, ⟨realMinimizingVectors_inv_smul_mem_strict g x hv.1.1 hc,
      hnorm hc.le hv.2⟩, ?_⟩, ?_⟩
    · dsimp only
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans hc)), one_smul]
    · intro hmem
      exact hv.1.2 hmem.1

/-- The entire genuine radial cut-endpoint set is tangent-Haar null. -/
theorem realCutEndpointVectors_measure_zero (g : SmoothMetric M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
    ∀ μ : Measure (TangentSpace 𝓘(ℝ, ComplexVector n) x), IsAddHaarMeasure μ →
      μ (realCutEndpointVectors g x) = 0 := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  intro μ hμ
  have hcover : realCutEndpointVectors g x ⊆ ⋃ k : ℕ,
      realCutEndpointVectors g x ∩ Metric.closedBall (0 : TangentSpace 𝓘(ℝ, ComplexVector n) x) (k : ℝ) := by
    intro v hv
    obtain ⟨k, hk⟩ := exists_nat_ge ‖v‖
    refine mem_iUnion.mpr ⟨k, hv, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hk
  apply measure_mono_null hcover
  apply measure_iUnion_null
  intro k
  exact realCutEndpointVectors_inter_closedBall_measure_zero g x μ hμ (k : ℝ)

end Yau.LeafProofs.L12Aux
