import Yau.LeafProofs.L12HopfRinow

/-! Genuine minimizing radial vectors, their strict extension domain,
and its Borel/star-shaped properties for the original length distance. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

/-- Actual initial vectors whose complete radial geodesics minimize up
to time one, for the original length distance. -/
def realMinimizingVectors (g : SmoothMetric M) (x : M.Carrier) :
    Set (TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  exact {v | inducedDistance g.form x (realExponentialMap g x v) = ‖v‖}

/-- Vectors minimizing strictly beyond their endpoints; the rational
extension parameter makes the actual domain visibly Borel. -/
def realStrictMinimizingVectors (g : SmoothMetric M) (x : M.Carrier) :
    Set (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
  {v | ∃ q : {q : ℚ // 1 < q}, (q.val : ℝ) • v ∈ realMinimizingVectors g x}

theorem isClosed_realMinimizingVectors (g : SmoothMetric M) (x : M.Carrier) :
    IsClosed (realMinimizingVectors g x) := by
  letI := manifold_realSmooth M
  letI := inducedMetricSpace g
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  have hExp : Continuous (realExponentialMap g x) := (realExponentialMap_contMDiff g x).continuous
  exact isClosed_eq (continuous_const.dist hExp) continuous_norm

theorem realMinimizingVectors_zero (g : SmoothMetric M) (x : M.Carrier) :
    (0 : TangentSpace 𝓘(ℝ, ComplexVector n) x) ∈ realMinimizingVectors g x := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  change inducedDistance g.form x (realExponentialMap g x 0) = ‖(0 : TangentSpace 𝓘(ℝ, ComplexVector n) x)‖
  rw [realExponentialMap_zero, norm_zero]
  exact g.induced_distance_eq_zero.mpr rfl

/-- Every earlier point of an actually minimizing radial geodesic is
actually minimizing, by the genuine geodesic length estimate. -/
theorem realMinimizingVectors_smul (g : SmoothMetric M) (x : M.Carrier)
    {v : TangentSpace 𝓘(ℝ, ComplexVector n) x} (hv : v ∈ realMinimizingVectors g x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : a • v ∈ realMinimizingVectors g x := by
  letI := inducedMetricSpace g
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  change dist x (realExponentialMap g x v) = ‖v‖ at hv
  change dist x (realExponentialMap g x (a • v)) = ‖a • v‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have hupper := inducedDistance_realExponentialMap_le g x (a • v)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at hupper
  change dist x (realExponentialMap g x (a • v)) ≤ a * ‖v‖ at hupper
  have htail := realExponentialMap_base_dist_le g x v a 1
  rw [one_smul, abs_of_nonneg (sub_nonneg.mpr ha1)] at htail
  change dist (realExponentialMap g x (a • v)) (realExponentialMap g x v) ≤ ‖v‖ * (1 - a) at htail
  have htri := dist_triangle x (realExponentialMap g x (a • v)) (realExponentialMap g x v)
  apply le_antisymm hupper
  linarith

theorem realStrictMinimizingVectors_subset (g : SmoothMetric M) (x : M.Carrier) :
    realStrictMinimizingVectors g x ⊆ realMinimizingVectors g x := by
  intro v hv
  obtain ⟨q, hq⟩ := hv
  have hqR : 1 < (q.val : ℝ) := by exact_mod_cast q.property
  have h := realMinimizingVectors_smul g x hq (inv_nonneg.mpr (le_trans zero_le_one hqR.le))
    ((inv_le_one₀ (lt_trans zero_lt_one hqR)).mpr hqR.le)
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hqR)), one_smul] using h

theorem realStrictMinimizingVectors_zero (g : SmoothMetric M) (x : M.Carrier) :
    (0 : TangentSpace 𝓘(ℝ, ComplexVector n) x) ∈ realStrictMinimizingVectors g x := by
  refine ⟨⟨2, by norm_num⟩, ?_⟩
  simpa only [smul_zero] using realMinimizingVectors_zero g x

theorem realStrictMinimizingVectors_smul (g : SmoothMetric M) (x : M.Carrier)
    {v : TangentSpace 𝓘(ℝ, ComplexVector n) x} (hv : v ∈ realStrictMinimizingVectors g x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : a • v ∈ realStrictMinimizingVectors g x := by
  obtain ⟨q, hq⟩ := hv
  refine ⟨q, ?_⟩
  have h := realMinimizingVectors_smul g x hq ha ha1
  simpa only [smul_smul, mul_comm a] using h

theorem measurableSet_realStrictMinimizingVectors (g : SmoothMetric M) (x : M.Carrier) :
    @MeasurableSet (TangentSpace 𝓘(ℝ, ComplexVector n) x)
      (borel (TangentSpace 𝓘(ℝ, ComplexVector n) x)) (realStrictMinimizingVectors g x) := by
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  have heq : realStrictMinimizingVectors g x = ⋃ q : {q : ℚ // 1 < q},
      (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) x => (q.val : ℝ) • v) ⁻¹' realMinimizingVectors g x := by
    ext v
    simp only [realStrictMinimizingVectors, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  have hc : Continuous (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) x => (q.val : ℝ) • v) :=
    continuous_const_smul (q.val : ℝ)
  exact (isClosed_realMinimizingVectors g x).measurableSet.preimage hc.measurable

/-- Shrinking any genuinely minimizing vector by a factor greater than
one places it strictly before its endpoint. -/
theorem realMinimizingVectors_inv_smul_mem_strict (g : SmoothMetric M) (x : M.Carrier)
    {v : TangentSpace 𝓘(ℝ, ComplexVector n) x} (hv : v ∈ realMinimizingVectors g x)
    {c : ℝ} (hc : 1 < c) : c⁻¹ • v ∈ realStrictMinimizingVectors g x := by
  obtain ⟨q, hq1, hqc⟩ := exists_rat_btwn hc
  have hq1' : (1 : ℚ) < q := by exact_mod_cast hq1
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hqpos : 0 ≤ (q : ℝ) := (zero_lt_one.trans hq1).le
  refine ⟨⟨q, hq1'⟩, ?_⟩
  have h := realMinimizingVectors_smul g x hv (div_nonneg hqpos hcpos.le)
    ((div_le_one hcpos).mpr hqc.le)
  simpa only [div_eq_mul_inv, smul_smul] using h

/-- The genuine radial endpoint vectors, defined by failure of a strictly
minimizing extension rather than by a separately supplied cut-time function. -/
def realCutEndpointVectors (g : SmoothMetric M) (x : M.Carrier) :
    Set (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
  realMinimizingVectors g x \ realStrictMinimizingVectors g x

theorem realCutEndpointVectors_zero_notMem (g : SmoothMetric M) (x : M.Carrier) :
    (0 : TangentSpace 𝓘(ℝ, ComplexVector n) x) ∉ realCutEndpointVectors g x := by
  intro h
  exact h.2 (realStrictMinimizingVectors_zero g x)

theorem realStrictMinimizingVectors_subset_expanded (g : SmoothMetric M) (x : M.Carrier)
    {c : ℝ} (hc : 1 ≤ c) :
    realStrictMinimizingVectors g x ⊆
      (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) x => c • v) '' realStrictMinimizingVectors g x := by
  intro v hv
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hw := realStrictMinimizingVectors_smul g x hv (inv_nonneg.mpr hcpos.le)
    ((inv_le_one₀ hcpos).mpr hc)
  refine ⟨c⁻¹ • v, hw, ?_⟩
  dsimp only
  rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]

theorem realCutEndpointVectors_subset_expanded_strict (g : SmoothMetric M) (x : M.Carrier)
    {c : ℝ} (hc : 1 < c) :
    realCutEndpointVectors g x ⊆
      ((fun v : TangentSpace 𝓘(ℝ, ComplexVector n) x => c • v) '' realStrictMinimizingVectors g x) \
        realStrictMinimizingVectors g x := by
  intro v hv
  refine ⟨⟨c⁻¹ • v, realMinimizingVectors_inv_smul_mem_strict g x hv.1 hc, ?_⟩, hv.2⟩
  dsimp only
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans hc)), one_smul]

end Yau.LeafProofs.L12Aux
