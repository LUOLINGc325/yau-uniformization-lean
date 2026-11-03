import Yau.LeafProofs.L18
import Yau.LeafProofs.L18RadialTransport
import Yau.LeafProofs.L12MinimizingJacobi

/-! Actual measurable minimizing segments and their nonnegative integral inequality. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff InnerProductSpace ComplexOrder
namespace Yau.LeafProofs.L18Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
local instance : IsManifold 𝓘(ℝ, ComplexVector n) ∞ M.Carrier := manifold_realSmooth M

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-- The strict minimizing domain in the actual tangent bundle. -/
def realStrictPhase (g : SmoothMetric M) :
    Set (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :=
  {p | p.2 ∈ realStrictMinimizingVectors g p.proj}

/-- A closed rational extension test in the genuine phase space. -/
def realMinimizingPhaseTest (g : SmoothMetric M) (q : {q : ℚ // 1 < q}) :
    Set (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :=
  {p | inducedDistance g.form p.proj (realGeodesicFlow g p q.val).proj =
    (q.val : ℝ) * Real.sqrt (realTangentEnergy g.form p)}

theorem realStrictPhase_eq_iUnion (g : SmoothMetric M) :
    realStrictPhase g = ⋃ q : {q : ℚ // 1 < q}, realMinimizingPhaseTest g q := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  ext p
  simp only [realStrictPhase, realStrictMinimizingVectors, mem_setOf_eq, mem_iUnion]
  apply exists_congr
  intro q
  have hq : 0 < (q.val : ℝ) := by exact_mod_cast (lt_trans zero_lt_one q.property)
  change (inducedDistance g.form p.proj (realExponentialMap g p.proj ((q.val : ℝ) • p.2)) =
      ‖(q.val : ℝ) • p.2‖) ↔ _
  rw [realExponentialMap_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
  simp only [realMinimizingPhaseTest, mem_setOf_eq, realTangentEnergy_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg p.2)]

theorem isClosed_realMinimizingPhaseTest (g : SmoothMetric M)
    (q : {q : ℚ // 1 < q}) :
    IsClosed (realMinimizingPhaseTest g q) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := inducedMetricSpace g
  have hproj : Continuous (fun p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => p.proj) :=
    FiberBundle.continuous_proj _ _
  have hflow := (realGeodesicFlow_joint_contMDiff g).continuous.comp
    (continuous_id.prodMk (continuous_const (y := (q.val : ℝ))))
  exact isClosed_eq (hproj.dist (hproj.comp hflow))
    (continuous_const.mul (realTangentEnergy_contMDiff g).continuous.sqrt)

theorem measurableSet_realStrictPhase (g : SmoothMetric M) :
    @MeasurableSet (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
      (borel _) (realStrictPhase g) := by
  letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
  letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
  rw [realStrictPhase_eq_iUnion]
  exact MeasurableSet.iUnion (fun q => (isClosed_realMinimizingPhaseTest g q).measurableSet)

/-- The strict phase domain is a countable union of genuine compact energy layers. -/
theorem isSigmaCompact_realStrictPhase (g : SmoothMetric M) :
    IsSigmaCompact (realStrictPhase g) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhase_t2Space M
  letI := manifold_locallyCompact M
  let K (q : {q : ℚ // 1 < q}) (k l : ℕ) :=
    realMinimizingPhaseTest g q ∩
      {p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier |
        p.proj ∈ compactCovering M.Carrier k ∧ realTangentEnergy g.form p ≤ l}
  have hK (q : {q : ℚ // 1 < q}) (k l : ℕ) : IsCompact (K q k l) :=
    (isCompact_realTangentEnergy_sublevel g (isCompact_compactCovering _ k) l).inter_left
      (isClosed_realMinimizingPhaseTest g q)
  have heq : realStrictPhase g = ⋃ q, ⋃ k, ⋃ l, K q k l := by
    ext p
    rw [realStrictPhase_eq_iUnion]
    simp only [mem_iUnion]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨k, hk⟩ := exists_mem_compactCovering p.proj
      obtain ⟨l, hl⟩ := exists_nat_ge (realTangentEnergy g.form p)
      exact ⟨q, k, l, hq, hk, hl⟩
    · rintro ⟨q, k, l, hq, _⟩
      exact ⟨q, hq⟩
  rw [heq]
  exact isSigmaCompact_iUnion _ (fun q => isSigmaCompact_iUnion _
    (fun k => isSigmaCompact_iUnion_of_isCompact _ (hK q k)))

private theorem measurableEmbedding_of_continuous_injective_sigmaCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [SigmaCompactSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) : MeasurableEmbedding f := by
  refine ⟨hinj, hf.measurable, ?_⟩
  intro s hs
  have hpiece (i : ℕ) : MeasurableSet (f '' (s ∩ compactCovering X i)) := by
    letI := isCompact_iff_compactSpace.mp (isCompact_compactCovering X i)
    have he : MeasurableEmbedding (fun x : compactCovering X i => f x) :=
      ((hf.comp continuous_subtype_val).isClosedEmbedding
        (hinj.comp Subtype.val_injective)).measurableEmbedding
    convert he.measurableSet_image' (hs.preimage measurable_subtype_coe) using 1
    ext y
    simp only [mem_image, mem_inter_iff, mem_preimage, Subtype.exists]
    aesop
  have heq : s = ⋃ i, s ∩ compactCovering X i := by
    rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
  have himage : f '' s = ⋃ i, f '' (s ∩ compactCovering X i) := by
    conv_lhs => rw [heq, image_iUnion]
  rw [himage]
  exact MeasurableSet.iUnion hpiece

/-- Genuine strict endpoint phases are uniquely determined by their endpoint pair. -/
theorem realGeodesicEndpointMap_injOn_realStrictPhase (g : SmoothMetric M) :
    InjOn (realGeodesicEndpointMap g 1) (realStrictPhase g) := by
  rintro ⟨x, v⟩ hv ⟨y, w⟩ hw he
  have hxy : x = y := congrArg Prod.fst he
  subst y
  have hexp : realExponentialMap g x v = realExponentialMap g x w := congrArg Prod.snd he
  have hvw := realExponentialMap_eq_imp_eq_of_mem_strictMinimizingVectors g x hv
    (realStrictMinimizingVectors_subset g x hw) hexp
  change v = w at hvw
  cases hvw
  rfl

/-- The actual endpoint map on strict minimizing phases is a measurable embedding. -/
theorem measurableEmbedding_realStrictEndpoint (g : SmoothMetric M) :
    letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
    letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
    MeasurableEmbedding (fun p : realStrictPhase g => realGeodesicEndpointMap g 1 p.val) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
  letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
  letI : SigmaCompactSpace (realStrictPhase g) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (isSigmaCompact_realStrictPhase g)
  exact measurableEmbedding_of_continuous_injective_sigmaCompact
    ((realGeodesicEndpointMap_contMDiff g 1).continuous.comp continuous_subtype_val)
    (injOn_iff_injective.mp (realGeodesicEndpointMap_injOn_realStrictPhase g))

/-- Endpoint pairs admitting a geodesic that minimizes strictly beyond its endpoint. -/
def realStrictEndpointPairs (g : SmoothMetric M) : Set (M.Carrier × M.Carrier) :=
  Set.range (fun p : realStrictPhase g => realGeodesicEndpointMap g 1 p.val)

theorem measurableSet_realStrictEndpointPairs (g : SmoothMetric M) :
    MeasurableSet (realStrictEndpointPairs g) := by
  letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
  letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
  exact (measurableEmbedding_realStrictEndpoint g).measurableSet_range

/-- An actual, jointly measurable strict phase selection; the center fixes its value off the range. -/
def realSelectedStrictPhase (g : SmoothMetric M) (o : M.Carrier) :
    M.Carrier × M.Carrier → realStrictPhase g := by
  letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
  letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
  letI : Nonempty (realStrictPhase g) :=
    ⟨⟨⟨o, 0⟩, realStrictMinimizingVectors_zero g o⟩⟩
  exact (measurableEmbedding_realStrictEndpoint g).invFun

theorem measurable_realSelectedStrictPhase (g : SmoothMetric M) (o : M.Carrier) :
    letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
    letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
    Measurable (realSelectedStrictPhase g o) := by
  letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
  letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
  letI : Nonempty (realStrictPhase g) :=
    ⟨⟨⟨o, 0⟩, realStrictMinimizingVectors_zero g o⟩⟩
  exact (measurableEmbedding_realStrictEndpoint g).measurable_invFun

theorem realSelectedStrictPhase_leftInverse (g : SmoothMetric M) (o : M.Carrier)
    (p : realStrictPhase g) :
    realSelectedStrictPhase g o (realGeodesicEndpointMap g 1 p.val) = p := by
  letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
  letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
  letI : Nonempty (realStrictPhase g) :=
    ⟨⟨⟨o, 0⟩, realStrictMinimizingVectors_zero g o⟩⟩
  exact (measurableEmbedding_realStrictEndpoint g).leftInverse_invFun p

theorem realSelectedStrictPhase_endpoint (g : SmoothMetric M) (o : M.Carrier)
    {z : M.Carrier × M.Carrier} (hz : z ∈ realStrictEndpointPairs g) :
    realGeodesicEndpointMap g 1 (realSelectedStrictPhase g o z).val = z := by
  obtain ⟨p, rfl⟩ := hz
  rw [realSelectedStrictPhase_leftInverse]

/-- The genuine geodesic segment associated to the measurable phase selection. -/
def realSelectedSegment (g : SmoothMetric M) (o : M.Carrier)
    (z : M.Carrier × M.Carrier) (t : ℝ) : M.Carrier :=
  (realGeodesicFlow g (realSelectedStrictPhase g o z).val t).proj

theorem measurable_realSelectedSegment (g : SmoothMetric M) (o : M.Carrier) :
    Measurable (fun z : (M.Carrier × M.Carrier) × ℝ => realSelectedSegment g o z.1 z.2) := by
  letI := manifold_realPhase M
  letI : MeasurableSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := borel _
  letI : BorelSpace (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := ⟨rfl⟩
  have hflow : Measurable (fun p :
      (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        (realGeodesicFlow g p.1 p.2).proj) :=
    ((FiberBundle.continuous_proj _ _).comp (realGeodesicFlow_joint_contMDiff g).continuous).measurable
  exact hflow.comp
    ((measurable_subtype_coe.comp ((measurable_realSelectedStrictPhase g o).comp measurable_fst)).prodMk
      measurable_snd)

theorem realSelectedSegment_exp (g : SmoothMetric M) (o a : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) a)
    (hv : v ∈ realStrictMinimizingVectors g a) (t : ℝ) :
    realSelectedSegment g o (a, realExponentialMap g a v) t =
      realExponentialMap g a (t • v) := by
  have he := realSelectedStrictPhase_leftInverse g o
    (⟨⟨a, v⟩, hv⟩ : realStrictPhase g)
  change realSelectedStrictPhase g o (a, realExponentialMap g a v) = _ at he
  rw [realSelectedSegment, he, realExponentialMap_smul]

/-- Away from a null cut image, every fixed-base endpoint has the selected strict phase. -/
theorem ae_realStrictEndpointPairs (g : SmoothMetric M) (a : M.Carrier)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    ∀ᵐ b ∂μ, (a, b) ∈ realStrictEndpointPairs g := by
  letI := underlyingRealTangentNormedAddCommGroup g.form a
  letI := underlyingRealTangentInnerProductSpace g.form a
  have hnull := realExponentialMap_cutEndpointVectors_image_measure_zero g a μ hμ
  have hae : ∀ᵐ b ∂μ, b ∉ realExponentialMap g a '' realCutEndpointVectors g a :=
    ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using hnull)
  filter_upwards [hae] with b hb
  obtain ⟨v, hv, hnorm⟩ := exists_minimizing_realExponential g a b
  have hvmin : v ∈ realMinimizingVectors g a := by
    change inducedDistance g.form a (realExponentialMap g a v) = ‖v‖
    rw [hv, hnorm]
  have hvstrict : v ∈ realStrictMinimizingVectors g a := by
    by_contra h
    exact hb ⟨v, ⟨hvmin, h⟩, hv⟩
  exact ⟨⟨⟨a, v⟩, hvstrict⟩, by exact Prod.ext rfl hv⟩

/-- The actual reverse flow traverses the same geometric curve in reverse time. -/
theorem realSegmentReverse_flow_proj (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    (realGeodesicFlow g (realSegmentReverse g 1 p) t).proj =
      (realGeodesicFlow g p (1 - t)).proj := by
  rw [realSegmentReverse, realGeodesicFlow_rescale]
  change (realGeodesicFlow g (realGeodesicFlow g p 1) (t * (-1))).proj = _
  rw [← realGeodesicFlow_add]
  congr 2
  ring

/-- Endpoint uniqueness needs strict minimality only on one side. -/
theorem realGeodesicEndpointMap_eq_imp_eq_of_strict (g : SmoothMetric M)
    (p q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hp : p ∈ realStrictPhase g) (hq : q.2 ∈ realMinimizingVectors g q.proj)
    (he : realGeodesicEndpointMap g 1 p = realGeodesicEndpointMap g 1 q) : p = q := by
  rcases p with ⟨x, v⟩
  rcases q with ⟨y, w⟩
  have hxy : x = y := congrArg Prod.fst he
  subst y
  have hvw := realExponentialMap_eq_imp_eq_of_mem_strictMinimizingVectors g x hp hq
    (show realExponentialMap g x v = realExponentialMap g x w from congrArg Prod.snd he)
  change v = w at hvw
  cases hvw
  rfl

/-- Reversing a minimizing phase remains genuinely minimizing. -/
theorem realSegmentReverse_mem_minimizing (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hp : p.2 ∈ realMinimizingVectors g p.proj) :
    (realSegmentReverse g 1 p).2 ∈
      realMinimizingVectors g (realSegmentReverse g 1 p).proj := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hend := congrArg Prod.snd (realSegmentReverse_endpointMap g 1 p)
  have hnorm : ‖(realSegmentReverse g 1 p).2‖ = ‖p.2‖ := by
    change ‖(-1 : ℝ) • (realGeodesicFlow g p 1).2‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_one, one_mul,
      realGeodesicFlow_velocity_norm]
  change inducedDistance g.form (realGeodesicFlow g p 1).proj
    (realExponentialMap g (realSegmentReverse g 1 p).proj (realSegmentReverse g 1 p).2) = _
  change (realGeodesicFlow g (realSegmentReverse g 1 p) 1).proj = p.proj at hend
  rw [show realExponentialMap g (realSegmentReverse g 1 p).proj
    (realSegmentReverse g 1 p).2 = p.proj from hend, g.induced_distance_symm, hnorm]
  exact hp

/-- Actual selected segments agree under endpoint reversal wherever both orientations are strict. -/
theorem realSelectedSegment_swap (g : SmoothMetric M) (o : M.Carrier)
    {z : M.Carrier × M.Carrier} (hz : z ∈ realStrictEndpointPairs g)
    (hswap : z.swap ∈ realStrictEndpointPairs g) (t : ℝ) :
    realSelectedSegment g o z.swap t = realSelectedSegment g o z (1 - t) := by
  have hp := (realSelectedStrictPhase g o z).property
  have hq := (realSelectedStrictPhase g o z.swap).property
  have he := realSelectedStrictPhase_endpoint g o hz
  have heq := realSelectedStrictPhase_endpoint g o hswap
  have hrev : realGeodesicEndpointMap g 1
      (realSegmentReverse g 1 (realSelectedStrictPhase g o z).val) = z.swap := by
    rw [realSegmentReverse_endpointMap]
    exact congrArg Prod.swap he
  have hphase := realGeodesicEndpointMap_eq_imp_eq_of_strict g
    (realSelectedStrictPhase g o z.swap).val
    (realSegmentReverse g 1 (realSelectedStrictPhase g o z).val) hq
    (realSegmentReverse_mem_minimizing g _ (realStrictMinimizingVectors_subset g _ hp))
    (heq.trans hrev.symm)
  change (realGeodesicFlow g (realSelectedStrictPhase g o z.swap).val t).proj = _
  rw [hphase, realSegmentReverse_flow_proj]
  rfl


/-- Both orientations are strict for almost every pair on any finite restricted measure. -/
theorem ae_realStrictEndpointPairs_both (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (s : Set M.Carrier) [IsFiniteMeasure (μ.restrict s)] :
    ∀ᵐ z ∂(μ.restrict s).prod (μ.restrict s),
      z ∈ realStrictEndpointPairs g ∧ z.swap ∈ realStrictEndpointPairs g := by
  have hp : ∀ᵐ z ∂(μ.restrict s).prod (μ.restrict s), z ∈ realStrictEndpointPairs g := by
    apply (ae_prod_iff_ae_ae (measurableSet_realStrictEndpointPairs g)).mpr
    exact ae_of_all _ (fun a => ae_restrict_of_ae (ae_realStrictEndpointPairs g a μ hμ))
  have hswap : ∀ᵐ z ∂(μ.restrict s).prod (μ.restrict s),
      z.swap ∈ realStrictEndpointPairs g :=
    measurePreserving_swap.quasiMeasurePreserving.ae hp
  exact hp.and hswap

private theorem segment_setLIntegral_dilate {E : Type*} [NormedAddCommGroup E]
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

/-- The radial half-time integral is controlled by the actual density comparison. -/
theorem strictRadial_lintegral_smul_le (g : SmoothMetric M)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : M.Carrier) {R t : ℝ} (hR : 0 < R) (ht : t ∈ Icc (1 / 2 : ℝ) 1)
    (F : M.Carrier → ℝ≥0∞) (hF : Measurable F) :
    letI := underlyingRealTangentNormedAddCommGroup g.form a
    letI := underlyingRealTangentInnerProductSpace g.form a
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) a) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) a) := ⟨rfl⟩
    ∫⁻ v in realStrictRadialBall g a R,
      F (realExponentialMap g a (t • v)) *
        ENNReal.ofReal (realExponentialVolumeDensity g a v) ∂realTangentVolume g a ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * ∫⁻ b in distBall g.form a R, F b ∂μ := by
  letI := underlyingRealTangentNormedAddCommGroup g.form a
  letI := underlyingRealTangentInnerProductSpace g.form a
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) a) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) a) := ⟨rfl⟩
  let ν := realTangentVolume g a
  letI : IsAddHaarMeasure ν := realTangentVolume_isAddHaarMeasure g a
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  let c := t⁻¹
  have hc : 0 < c := inv_pos.mpr ht0
  have hc1 : 1 ≤ c := (one_le_inv₀ ht0).mpr ht.2
  have hc2 : c ≤ 2 := by
    dsimp only [c]
    rw [← one_div, div_le_iff₀ ht0]
    linarith [ht.1]
  let D := realStrictRadialBall g a R
  let A := (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) a => c • v) ⁻¹' D
  have hA : MeasurableSet A :=
    (measurableSet_realStrictRadialBall g a R).preimage (measurable_const_smul c)
  have hsub : A ⊆ D := by
    intro v hv
    change c • v ∈ realStrictMinimizingVectors g a ∩ Metric.ball 0 R at hv
    have hstrict := realStrictMinimizingVectors_smul g a hv.1
      (inv_nonneg.mpr hc.le) ((inv_le_one₀ hc).mpr hc1)
    have he : c⁻¹ • (c • v) = v := by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    refine ⟨by rwa [he] at hstrict, ?_⟩
    have hn : c * ‖v‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc] using hv.2
    have hvn : ‖v‖ < R := (le_mul_of_one_le_left (norm_nonneg _) hc1).trans_lt hn
    simpa only [Metric.mem_ball, dist_zero_right] using hvn
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) a) = 2 * n := by
    simpa only [Fintype.card_fin] using
      Module.finrank_eq_card_basis (realInitialOrthonormalFrame g a).toBasis
  calc
    _ = ENNReal.ofReal (c ^ (2 * n)) * ∫⁻ v in A,
        F (realExponentialMap g a v) *
          ENNReal.ofReal (realExponentialVolumeDensity g a (c • v)) ∂ν := by
      have he : t * c = 1 := mul_inv_cancel₀ ht0.ne'
      simpa only [hdim, smul_smul, he, one_smul] using
        segment_setLIntegral_dilate ν hc D (fun v =>
          F (realExponentialMap g a (t • v)) *
            ENNReal.ofReal (realExponentialVolumeDensity g a v))
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * ∫⁻ v in A,
        F (realExponentialMap g a v) *
          ENNReal.ofReal (realExponentialVolumeDensity g a v) ∂ν := by
      apply mul_le_mul'
      · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le hc2 _)
      · apply setLIntegral_mono' hA
        intro v hv
        have hJ := realExponentialVolumeDensity_inv_smul_le g hK hRic
          (realMinimizingJacobiPositive g) a hv.1 hc1
        have he : c⁻¹ • (c • v) = v := by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
        rw [he] at hJ
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hJ)
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * ∫⁻ v in D,
        F (realExponentialMap g a v) *
          ENNReal.ofReal (realExponentialVolumeDensity g a v) ∂ν :=
      mul_le_mul_right (lintegral_mono_set hsub) _
    _ = _ := by rw [distBall_lintegral_eq_strictRadial_integral g a μ hμ hR F hF]

/-- Half-time integration along the actual measurable minimizing segments. -/
theorem lintegral_realSelectedSegment_lastHalf_le (g : SmoothMetric M)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o a : M.Carrier) {R : ℝ} (hR : 0 < R)
    (F : M.Carrier → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ b in distBall g.form a R, ∫⁻ t in Icc (1 / 2 : ℝ) 1,
      F (realSelectedSegment g o (a, b) t) ∂volume ∂μ ≤
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) *
        ∫⁻ b in distBall g.form a R, F b ∂μ := by
  letI : IsFiniteMeasure (μ.restrict (distBall g.form a R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using riemannianVolume_distBall_lt_top g μ hμ a hR⟩
  have hmeas : Measurable (fun z : M.Carrier × ℝ =>
      F (realSelectedSegment g o (a, z.1) z.2)) :=
    hF.comp ((measurable_realSelectedSegment g o).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
  have hpoint (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
      ∫⁻ b in distBall g.form a R, F (realSelectedSegment g o (a, b) t) ∂μ ≤
        ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * ∫⁻ b in distBall g.form a R, F b ∂μ := by
    letI := underlyingRealTangentNormedAddCommGroup g.form a
    letI := underlyingRealTangentInnerProductSpace g.form a
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) a) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) a) := ⟨rfl⟩
    have hFt : Measurable (fun b => F (realSelectedSegment g o (a, b) t)) := by
      simpa only [Function.comp_def, id_eq] using
        hmeas.comp (measurable_id.prodMk (measurable_const (a := t)))
    rw [distBall_lintegral_eq_strictRadial_integral g a μ hμ hR _ hFt]
    have heq : (∫⁻ v in realStrictRadialBall g a R,
        F (realSelectedSegment g o (a, realExponentialMap g a v) t) *
          ENNReal.ofReal (realExponentialVolumeDensity g a v) ∂realTangentVolume g a) =
        ∫⁻ v in realStrictRadialBall g a R,
          F (realExponentialMap g a (t • v)) *
            ENNReal.ofReal (realExponentialVolumeDensity g a v) ∂realTangentVolume g a := by
      apply setLIntegral_congr_fun (measurableSet_realStrictRadialBall g a R)
      intro v hv
      change F (realSelectedSegment g o (a, realExponentialMap g a v) t) *
        ENNReal.ofReal (realExponentialVolumeDensity g a v) = _
      rw [realSelectedSegment_exp g o a v hv.1]
    rw [heq]
    exact strictRadial_lintegral_smul_le g hK hRic μ hμ a hR ht F hF
  calc
    _ = ∫⁻ t in Icc (1 / 2 : ℝ) 1, ∫⁻ b in distBall g.form a R,
        F (realSelectedSegment g o (a, b) t) ∂μ :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ t in Icc (1 / 2 : ℝ) 1,
        ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * ∫⁻ b in distBall g.form a R, F b ∂μ :=
      setLIntegral_mono' measurableSet_Icc hpoint
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      norm_num
      ac_rfl

/-- The late-half segment functional, retaining the physical endpoint distance. -/
def realSegmentLastHalf (g : SmoothMetric M) (o : M.Carrier)
    (F : M.Carrier → ℝ≥0∞) (z : M.Carrier × M.Carrier) : ℝ≥0∞ :=
  ENNReal.ofReal (inducedDistance g.form z.1 z.2) *
    ∫⁻ t in Icc (1 / 2 : ℝ) 1, F (realSelectedSegment g o z t)

theorem measurable_realSegmentLastHalf (g : SmoothMetric M) (o : M.Carrier)
    (F : M.Carrier → ℝ≥0∞) (hF : Measurable F) :
    Measurable (realSegmentLastHalf g o F) := by
  exact (continuous_inducedDistance g).measurable.ennreal_ofReal.mul
    (hF.comp (measurable_realSelectedSegment g o)).lintegral_prod_right'

/-- The actual last half-segment estimate on a fixed radial ball. -/
theorem lintegral_realSegmentLastHalf_le (g : SmoothMetric M)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o a : M.Carrier) {R : ℝ} (hR : 0 < R)
    (F : M.Carrier → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ b in distBall g.form a R, realSegmentLastHalf g o F (a, b) ∂μ ≤
      ENNReal.ofReal R * ENNReal.ofReal (1 / 2 : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * ∫⁻ b in distBall g.form a R, F b ∂μ := by
  calc
    _ ≤ ∫⁻ b in distBall g.form a R, ENNReal.ofReal R *
        ∫⁻ t in Icc (1 / 2 : ℝ) 1, F (realSelectedSegment g o (a, b) t) ∂volume ∂μ := by
      apply setLIntegral_mono' (measurableSet_distBall g a R)
      intro b hb
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal ((mem_distBall_iff g a b hR).mp hb).le) le_rfl
    _ = ENNReal.ofReal R * ∫⁻ b in distBall g.form a R,
        ∫⁻ t in Icc (1 / 2 : ℝ) 1, F (realSelectedSegment g o (a, b) t) ∂volume ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal R * (ENNReal.ofReal (1 / 2 : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * ∫⁻ b in distBall g.form a R, F b ∂μ) :=
      mul_le_mul' le_rfl (lintegral_realSelectedSegment_lastHalf_le g hK hRic μ hμ o a hR F hF)
    _ = _ := by ac_rfl

/-- The last-half estimate localized to the original ball and its triple dilation. -/
theorem lintegral_realSegmentLastHalf_originalBall_le (g : SmoothMetric M)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o a : M.Carrier) {r : ℝ} (hr : 0 < r) (ha : a ∈ distBall g.form o r)
    (F : M.Carrier → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ b in distBall g.form o r, realSegmentLastHalf g o F (a, b) ∂μ ≤
      ENNReal.ofReal (((2 : ℝ) ^ (2 * n)) * r) *
        ∫⁻ b in distBall g.form o (3 * r), F b ∂μ := by
  letI := inducedMetricSpace g
  have hao : dist o a < r := (mem_distBall_iff g o a hr).mp ha
  have hsub : distBall g.form o r ⊆ distBall g.form a (2 * r) := by
    intro b hb
    apply (mem_distBall_iff g a b (by linarith)).mpr
    have hb' : dist o b < r := (mem_distBall_iff g o b hr).mp hb
    change dist a b < 2 * r
    have htri := dist_triangle a o b
    rw [dist_comm a o] at htri
    linarith
  have hsub3 : distBall g.form a (2 * r) ⊆ distBall g.form o (3 * r) := by
    intro b hb
    apply (mem_distBall_iff g o b (by linarith)).mpr
    have hb' : dist a b < 2 * r := (mem_distBall_iff g a b (by linarith)).mp hb
    change dist o b < 3 * r
    have htri := dist_triangle o a b
    linarith
  have hc : ENNReal.ofReal (2 * r) * ENNReal.ofReal (1 / 2 : ℝ) *
      ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) = ENNReal.ofReal (((2 : ℝ) ^ (2 * n)) * r) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * r),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * r) * (1 / 2 : ℝ))]
    congr 1
    ring
  calc
    _ ≤ ∫⁻ b in distBall g.form a (2 * r), realSegmentLastHalf g o F (a, b) ∂μ :=
      lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal (2 * r) * ENNReal.ofReal (1 / 2 : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * ∫⁻ b in distBall g.form a (2 * r), F b ∂μ :=
      lintegral_realSegmentLastHalf_le g hK hRic μ hμ o a (by linarith) F hF
    _ ≤ _ := by
      rw [hc]
      exact mul_le_mul' le_rfl (lintegral_mono_set hsub3)

/-- The full segment functional. -/
def realSegmentIntegral (g : SmoothMetric M) (o : M.Carrier)
    (F : M.Carrier → ℝ≥0∞) (z : M.Carrier × M.Carrier) : ℝ≥0∞ :=
  ENNReal.ofReal (inducedDistance g.form z.1 z.2) *
    ∫⁻ t in Icc (0 : ℝ) 1, F (realSelectedSegment g o z t)

theorem measurable_realSegmentIntegral (g : SmoothMetric M) (o : M.Carrier)
    (F : M.Carrier → ℝ≥0∞) (hF : Measurable F) :
    Measurable (realSegmentIntegral g o F) := by
  exact (continuous_inducedDistance g).measurable.ennreal_ofReal.mul
    (hF.comp (measurable_realSelectedSegment g o)).lintegral_prod_right'

/-- Reflection identifies the two half segments, with all endpoint pairs and curves actual. -/
theorem realSegmentIntegral_le_lastHalf_add_swap (g : SmoothMetric M) (o : M.Carrier)
    (F : M.Carrier → ℝ≥0∞) (hF : Measurable F)
    {z : M.Carrier × M.Carrier} (hz : z ∈ realStrictEndpointPairs g)
    (hswap : z.swap ∈ realStrictEndpointPairs g) :
    realSegmentIntegral g o F z ≤
      realSegmentLastHalf g o F z + realSegmentLastHalf g o F z.swap := by
  have hmeas : Measurable (fun t : ℝ => F (realSelectedSegment g o z t)) :=
    hF.comp ((measurable_realSelectedSegment g o).comp (measurable_const.prodMk measurable_id))
  have hpre : (fun t : ℝ => 1 - t) ⁻¹' Icc (0 : ℝ) (1 / 2) = Icc (1 / 2 : ℝ) 1 := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hreflect : (∫⁻ t in Icc (0 : ℝ) (1 / 2), F (realSelectedSegment g o z t)) =
      ∫⁻ t in Icc (1 / 2 : ℝ) 1, F (realSelectedSegment g o z.swap t) := by
    have h := (volume.measurePreserving_sub_left (1 : ℝ)).setLIntegral_comp_preimage
      (s := Icc (0 : ℝ) (1 / 2)) measurableSet_Icc hmeas
    rw [hpre] at h
    rw [← h]
    apply lintegral_congr
    intro t
    rw [realSelectedSegment_swap g o hz hswap]
  have hunion : Icc (0 : ℝ) 1 = Icc (0 : ℝ) (1 / 2) ∪ Icc (1 / 2 : ℝ) 1 := by
    ext t
    simp only [mem_Icc, mem_union]
    constructor
    · intro h
      rcases le_total t (1 / 2 : ℝ) with ht | ht
      · exact Or.inl ⟨h.1, ht⟩
      · exact Or.inr ⟨ht, h.2⟩
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
  have hsplit : (∫⁻ t in Icc (0 : ℝ) 1, F (realSelectedSegment g o z t)) ≤
      (∫⁻ t in Icc (1 / 2 : ℝ) 1, F (realSelectedSegment g o z t)) +
        ∫⁻ t in Icc (1 / 2 : ℝ) 1, F (realSelectedSegment g o z.swap t) := by
    rw [hunion]
    have h := lintegral_union_le (μ := (volume : Measure ℝ)) (fun t => F (realSelectedSegment g o z t))
      (Icc (0 : ℝ) (1 / 2)) (Icc (1 / 2 : ℝ) 1)
    rw [hreflect, add_comm] at h
    exact h
  unfold realSegmentIntegral realSegmentLastHalf
  rw [show inducedDistance g.form z.swap.1 z.swap.2 = inducedDistance g.form z.1 z.2 from
    g.induced_distance_symm _ _, ← mul_add]
  exact mul_le_mul' le_rfl hsplit

/-- The genuine nonnegative segment inequality on an original metric ball. -/
theorem lintegral_realSegmentIntegral_originalBall_le (g : SmoothMetric M)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) {r : ℝ} (hr : 0 < r)
    (F : M.Carrier → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, realSegmentIntegral g o F z
        ∂(μ.restrict (distBall g.form o r)).prod (μ.restrict (distBall g.form o r)) ≤
      ENNReal.ofReal (((2 : ℝ) ^ (2 * n + 1)) * r) * μ (distBall g.form o r) *
        ∫⁻ b in distBall g.form o (3 * r), F b ∂μ := by
  let B := distBall g.form o r
  let ν := μ.restrict B
  letI : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using riemannianVolume_distBall_lt_top g μ hμ o hr⟩
  let A := ENNReal.ofReal (((2 : ℝ) ^ (2 * n)) * r) * μ B *
    ∫⁻ b in distBall g.form o (3 * r), F b ∂μ
  have hH := measurable_realSegmentLastHalf g o F hF
  have hbound : ∫⁻ z, realSegmentLastHalf g o F z ∂ν.prod ν ≤ A := by
    rw [lintegral_prod _ hH.aemeasurable]
    calc
      _ ≤ ∫⁻ a, ENNReal.ofReal (((2 : ℝ) ^ (2 * n)) * r) *
          ∫⁻ b in distBall g.form o (3 * r), F b ∂μ ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_distBall g o r)] with a ha
        exact lintegral_realSegmentLastHalf_originalBall_le g hK hRic μ hμ o a hr ha F hF
      _ = A := by
        rw [lintegral_const, show ν univ = μ B from Measure.restrict_apply_univ B]
        dsimp only [A]
        ac_rfl
  have hswap : ∫⁻ z, realSegmentLastHalf g o F z.swap ∂ν.prod ν =
      ∫⁻ z, realSegmentLastHalf g o F z ∂ν.prod ν :=
    measurePreserving_swap.lintegral_comp hH
  have hboth := ae_realStrictEndpointPairs_both g μ hμ B
  calc
    _ ≤ ∫⁻ z, (realSegmentLastHalf g o F z + realSegmentLastHalf g o F z.swap) ∂ν.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [hboth] with z hz
      exact realSegmentIntegral_le_lastHalf_add_swap g o F hF hz.1 hz.2
    _ = (∫⁻ z, realSegmentLastHalf g o F z ∂ν.prod ν) +
        ∫⁻ z, realSegmentLastHalf g o F z.swap ∂ν.prod ν :=
      lintegral_add_left hH _
    _ ≤ A + A := by rw [hswap]; exact add_le_add hbound hbound
    _ = _ := by
      dsimp only [A]
      rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2
      congr 1
      rw [pow_succ]
      ring

end Yau.LeafProofs.L18Aux
