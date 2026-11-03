import spec.CHAIN.LeafObligations
import Yau.LeafProofs.SharedCalculus

/-!
Infrastructure for the exact Bishop--Gromov obligation L12.  The metric below
uses the existing length infimum and preserves the manifold topology.  It does
not replace that distance by a separately chosen Riemannian distance.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff

namespace Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine metric structure of the existing project length distance. -/
def inducedMetricSpace (g : SmoothMetric M) : MetricSpace M.Carrier :=
  MetricSpace.ofDistTopology (inducedDistance g.form)
    (fun x => g.induced_distance_eq_zero.mpr rfl)
    g.induced_distance_symm g.induced_distance_triangle
    (by
      intro s
      rw [isOpen_iff_mem_nhds]
      constructor
      · intro hs x hx
        rcases (g.induced_distance_topology x s).mp (hs x hx) with ⟨ε, hε, hsub⟩
        exact ⟨ε, hε, fun y hy => hsub hy⟩
      · intro hs x hx
        rcases hs x hx with ⟨ε, hε, hsub⟩
        exact (g.induced_distance_topology x s).mpr ⟨ε, hε, hsub⟩)
    (fun _ _ h => g.induced_distance_eq_zero.mp h)

theorem inducedMetricSpace_dist (g : SmoothMetric M) (x y : M.Carrier) :
    @dist M.Carrier (inducedMetricSpace g).toDist x y = inducedDistance g.form x y :=
  rfl

/-- The project's sequence completeness gives ordinary uniform completeness. -/
theorem inducedMetricSpace_complete (g : SmoothMetric M) :
    @CompleteSpace M.Carrier (inducedMetricSpace g).toUniformSpace := by
  letI := inducedMetricSpace g
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc : IsCauchy (inducedDistance g.form) u := by
    intro ε hε
    rcases Metric.cauchySeq_iff.mp hu ε hε with ⟨N, hN⟩
    exact ⟨N, fun m k hm hk => hN m hm k hk⟩
  rcases g.complete_distance u hc with ⟨x, hx⟩
  exact ⟨x, Metric.tendsto_atTop.mpr hx⟩

theorem mem_distBall_iff (g : SmoothMetric M) (x y : M.Carrier)
    {r : ℝ} (hr : 0 < r) :
    y ∈ distBall g.form x r ↔ inducedDistance g.form x y < r := by
  exact ENNReal.ofReal_lt_ofReal_iff hr

/-- Project balls are precisely ordinary open balls in the constructed metric. -/
theorem distBall_eq_metric_ball (g : SmoothMetric M) (x : M.Carrier)
    {r : ℝ} (hr : 0 < r) :
    distBall g.form x r = @Metric.ball M.Carrier (inducedMetricSpace g).toPseudoMetricSpace x r := by
  ext y
  rw [mem_distBall_iff g x y hr]
  change inducedDistance g.form x y < r ↔ inducedDistance g.form y x < r
  rw [g.induced_distance_symm x y]

theorem distBall_eq_empty_of_nonpos (h : HermitianField M) (x : M.Carrier)
    {r : ℝ} (hr : r ≤ 0) : distBall h x r = ∅ := by
  ext y
  simp [distBall, ENNReal.ofReal_of_nonpos hr]

theorem isOpen_distBall (g : SmoothMetric M) (x : M.Carrier) (r : ℝ) :
    IsOpen (distBall g.form x r) := by
  by_cases hr : 0 < r
  · letI := inducedMetricSpace g
    rw [distBall_eq_metric_ball g x hr]
    exact Metric.isOpen_ball
  · rw [distBall_eq_empty_of_nonpos g.form x (le_of_not_gt hr)]
    exact isOpen_empty

theorem measurableSet_distBall (g : SmoothMetric M) (x : M.Carrier) (r : ℝ) :
    MeasurableSet (distBall g.form x r) :=
  (isOpen_distBall g x r).measurableSet

theorem continuous_inducedDistance (g : SmoothMetric M) :
    Continuous (fun p : M.Carrier × M.Carrier => inducedDistance g.form p.1 p.2) := by
  letI := inducedMetricSpace g
  exact continuous_dist

theorem continuous_distFrom (g : SmoothMetric M) (x : M.Carrier) :
    Continuous (distFrom g.form x) := by
  letI := inducedMetricSpace g
  exact continuous_const.dist continuous_id

/-- Local compactness follows from the actual finite-dimensional charts. -/
theorem manifold_locallyCompact (M : ComplexManifold n) :
    LocallyCompactSpace M.Carrier :=
  ChartedSpace.locallyCompactSpace (ComplexVector n) M.Carrier

/-- The chart law fixes the volume globally, even before existence is proved. -/
theorem riemannianVolume_unique (h : HermitianField M) {μ ν : Measure M.Carrier}
    (hμ : IsRiemannianVolume h μ) (hν : IsRiemannianVolume h ν) : μ = ν := by
  obtain ⟨S, hS, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun x : M.Carrier => (chartAt (ComplexVector n) x).source)
    (fun x => (chartAt (ComplexVector n) x).open_source)
    (by rw [iUnion_source_chartAt])
  apply Measure.ext_of_biUnion_eq_univ hS (Set.eq_univ_of_univ_subset hcover)
  intro x _
  apply Measure.ext
  intro t ht
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  have hi := ht.inter (chartAt (ComplexVector n) x).open_source.measurableSet
  exact (hμ x _ hi Set.inter_subset_right).trans (hν x _ hi Set.inter_subset_right).symm

theorem abs_distFrom_sub_le (g : SmoothMetric M) (o x y : M.Carrier) :
    |distFrom g.form o x - distFrom g.form o y| ≤ inducedDistance g.form x y := by
  letI := inducedMetricSpace g
  change |dist o x - dist o y| ≤ dist x y
  simpa only [dist_comm] using abs_dist_sub_le x y o

/-- The integrating factor in the scalar Riccati comparison.  This is the
analytic step applied to the trace of the radial Jacobi shape operator. -/
theorem riccati_integratingFactor_antitone {k T : ℝ} (hk : 0 < k)
    {h h' : ℝ → ℝ}
    (hh : ∀ t ∈ Set.Ioo 0 T, HasDerivAt h (h' t) t)
    (hRic : ∀ t ∈ Set.Ioo 0 T, k * h' t + h t ^ 2 ≤ 0) :
    AntitoneOn (fun t => t ^ 2 * h t - k * t) (Set.Ioo 0 T) := by
  have hd : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (fun s => s ^ 2 * h s - k * s)
        (2 * t * h t + t ^ 2 * h' t - k) t := by
    intro t ht
    convert (((hasDerivAt_id t).pow 2).mul (hh t ht)).sub
      ((hasDerivAt_id t).const_mul k) using 1
    · funext s
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    · simp only [Pi.pow_apply, id_eq]
      ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 T)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (by simpa only [interior_Ioo] using ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' : t ∈ Set.Ioo 0 T := by simpa only [interior_Ioo] using ht
  rw [(hd t ht').deriv]
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (hRic t ht')
  have hs := sq_nonneg (t * h t - k)
  have hbound : k * (2 * t * h t + t ^ 2 * h' t - k) ≤ 0 := by
    nlinarith
  nlinarith

/-- The Euclidean radial upper bound from the Riccati differential inequality
and its genuine initial asymptotic, without a comparison theorem as input. -/
theorem riccati_le_euclidean {k T : ℝ} (hk : 0 < k)
    {h h' : ℝ → ℝ}
    (hh : ∀ t ∈ Set.Ioo 0 T, HasDerivAt h (h' t) t)
    (hRic : ∀ t ∈ Set.Ioo 0 T, k * h' t + h t ^ 2 ≤ 0)
    (hzero : Tendsto (fun t => t ^ 2 * h t - k * t) (𝓝[>] 0) (𝓝 0)) :
    ∀ t ∈ Set.Ioo 0 T, h t ≤ k / t := by
  have hanti := riccati_integratingFactor_antitone hk hh hRic
  intro t ht
  have hbound : t ^ 2 * h t - k * t ≤ 0 := by
    apply ge_of_tendsto hzero
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.1)] with s hs hst
    exact hanti ⟨hs, lt_trans hst ht.2⟩ ht (le_of_lt hst)
  apply (le_div_iff₀ ht.1).mpr
  by_contra hfail
  have hpos := mul_pos ht.1 (sub_pos.mpr (lt_of_not_ge hfail))
  nlinarith

/-- A radial density satisfying `t J' ≤ k J` has decreasing Euclidean ratio. -/
theorem normalizedDensity_antitone {k : ℕ} {T : ℝ} {J J' : ℝ → ℝ}
    (hJ : ∀ t ∈ Set.Ioo 0 T, HasDerivAt J (J' t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, t * J' t ≤ (k + 1 : ℕ) * J t) :
    AntitoneOn (fun t => J t / t ^ (k + 1)) (Set.Ioo 0 T) := by
  have hd : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (fun s => J s / s ^ (k + 1))
        ((J' t * t ^ (k + 1) - J t * ((k + 1 : ℕ) * t ^ k)) /
          (t ^ (k + 1)) ^ 2) t := by
    intro t ht
    convert!
      (hJ t ht).div (hasDerivAt_pow (k + 1) t) (pow_ne_zero _ (ne_of_gt ht.1))
      using 1 <;> simp only [Nat.add_one_sub_one]
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 T)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (by simpa only [interior_Ioo] using ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' : t ∈ Set.Ioo 0 T := by simpa only [interior_Ioo] using ht
  rw [(hd t ht').deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hmul := mul_nonpos_of_nonneg_of_nonpos
    (pow_nonneg (le_of_lt ht'.1) k) (sub_nonpos.mpr (hbound t ht'))
  rw [pow_succ]
  nlinarith [hmul]

/-- The analytic Jacobi-density comparison, from its first-order density ODE,
trace Riccati inequality, positivity, and the initial radial asymptotic. -/
theorem jacobiDensity_ratio_antitone {k : ℕ} {T : ℝ} {J h h' : ℝ → ℝ}
    (hJ : ∀ t ∈ Set.Ioo 0 T, HasDerivAt J (h t * J t) t)
    (hJpos : ∀ t ∈ Set.Ioo 0 T, 0 ≤ J t)
    (hh : ∀ t ∈ Set.Ioo 0 T, HasDerivAt h (h' t) t)
    (hRic : ∀ t ∈ Set.Ioo 0 T, (k + 1 : ℕ) * h' t + h t ^ 2 ≤ 0)
    (hzero : Tendsto (fun t => t ^ 2 * h t - (k + 1 : ℕ) * t)
      (𝓝[>] 0) (𝓝 0)) :
    AntitoneOn (fun t => J t / t ^ (k + 1)) (Set.Ioo 0 T) := by
  apply normalizedDensity_antitone hJ
  intro t ht
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hu := riccati_le_euclidean hk hh hRic hzero t ht
  have hut := (le_div_iff₀ ht.1).mp hu
  have hm := mul_le_mul_of_nonneg_right hut (hJpos t ht)
  nlinarith

/-- Cauchy--Schwarz for the shape operator, including all off-diagonal terms. -/
theorem trace_sq_le_card_trace_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.IsSymm) :
    S.trace ^ 2 ≤ Fintype.card ι * (S * S).trace := by
  have hdiag : (∑ i, S i i ^ 2) ≤ (S * S).trace := by
    unfold Matrix.trace
    apply Finset.sum_le_sum
    intro i _
    change S i i ^ 2 ≤ ∑ j, S i j * S j i
    rw [pow_two]
    apply Finset.single_le_sum (s := Finset.univ) (f := fun j => S i j * S j i) (a := i)
    · intro j _
      rw [hS.apply i j]
      exact mul_self_nonneg _
    · exact Finset.mem_univ i
  calc
    S.trace ^ 2 ≤ Fintype.card ι * ∑ i, S i i ^ 2 := by
      simpa only [Matrix.trace, Matrix.diag_apply, Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => S i i))
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _)

/-- Taking the trace of the matrix Riccati equation and using nonnegative
radial Ricci gives the scalar differential inequality used above. -/
theorem matrixRiccati_trace_inequality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S S' R : Matrix ι ι ℝ) (hS : S.IsSymm)
    (hRic : S' + S * S + R = 0) (hR : 0 ≤ R.trace) :
    Fintype.card ι * S'.trace + S.trace ^ 2 ≤ 0 := by
  have htrace := congrArg Matrix.trace hRic
  simp only [Matrix.trace_add, Matrix.trace_zero] at htrace
  have hcs := trace_sq_le_card_trace_mul_self S hS
  have hRmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)) hR
  nlinarith

/-- Positive radial dilation in the nonnegative integral, without finiteness
or measurability assumptions on the density. -/
theorem lintegral_dilate_Ioo (f : ℝ → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Set.Ioo 0 r, f t) =
      ENNReal.ofReal r * ∫⁻ t in Set.Ioo 0 1, f (r * t) := by
  have he : MeasurableEmbedding (fun t : ℝ => r * t) :=
    (Homeomorph.mulLeft₀ r (ne_of_gt hr)).isClosedEmbedding.measurableEmbedding
  have hvol : ENNReal.ofReal r •
      Measure.map (fun t : ℝ => r * t) volume = (volume : Measure ℝ) := by
    simpa only [abs_of_pos hr] using Real.smul_map_volume_mul_left (ne_of_gt hr)
  have hpre : (fun t : ℝ => r * t) ⁻¹' Set.Ioo 0 r = Set.Ioo 0 1 := by
    ext t
    change (0 < r * t ∧ r * t < r) ↔ (0 < t ∧ t < 1)
    constructor
    · intro ht
      constructor <;> nlinarith [ht.1, ht.2]
    · intro ht
      exact ⟨mul_pos hr ht.1, by nlinarith [ht.2]⟩
  calc
    (∫⁻ t in Set.Ioo 0 r, f t) =
        ∫⁻ t, f t ∂((ENNReal.ofReal r •
          Measure.map (fun t : ℝ => r * t) volume).restrict (Set.Ioo 0 r)) := by
      rw [hvol]
    _ = _ := by
      rw [Measure.restrict_smul, lintegral_smul_measure, he.restrict_map,
        he.lintegral_map, hpre, smul_eq_mul]

theorem density_scale_le {k : ℕ} {J : ℝ → ℝ}
    (hanti : AntitoneOn (fun t => J t / t ^ k) (Set.Ioi 0))
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    J R ≤ (R / r) ^ k * J r := by
  have hR := lt_of_lt_of_le hr hrR
  have ha := hanti hr hR hrR
  calc
    J R = (J R / R ^ k) * R ^ k := by
      rw [div_mul_cancel₀ _ (pow_ne_zero _ (ne_of_gt hR))]
    _ ≤ (J r / r ^ k) * R ^ k := mul_le_mul_of_nonneg_right ha
      (pow_nonneg (le_of_lt hR) k)
    _ = (R / r) ^ k * J r := by
      rw [div_pow]
      ring

/-- The radial integration step in Bishop--Gromov.  The nonnegative integral
allows cut-time densities without imposing artificial integrability inputs. -/
theorem radialIntegral_comparison {k : ℕ} {J : ℝ → ℝ}
    (hanti : AntitoneOn (fun t => J t / t ^ k) (Set.Ioi 0))
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (∫⁻ t in Set.Ioo 0 R, ENNReal.ofReal (J t)) ≤
      ENNReal.ofReal ((R / r) ^ (k + 1)) *
        ∫⁻ t in Set.Ioo 0 r, ENNReal.ofReal (J t) := by
  have hR := lt_of_lt_of_le hr hrR
  have hc : 0 ≤ R / r := div_nonneg (le_of_lt hR) (le_of_lt hr)
  have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (J (R * s)) ≤
        ENNReal.ofReal ((R / r) ^ k) * ENNReal.ofReal (J (r * s)) := by
    intro s hs
    have hd := density_scale_le hanti (mul_pos hr hs.1)
      (mul_le_mul_of_nonneg_right hrR (le_of_lt hs.1))
    have hratio : R * s / (r * s) = R / r := by
      field_simp [ne_of_gt hs.1]
    rw [hratio] at hd
    simpa only [ENNReal.ofReal_mul (pow_nonneg hc k)] using ENNReal.ofReal_le_ofReal hd
  have hcoeff : R * (R / r) ^ k = (R / r) ^ (k + 1) * r := by
    rw [pow_succ, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hr), mul_comm]
  calc
    (∫⁻ t in Set.Ioo 0 R, ENNReal.ofReal (J t)) =
        ENNReal.ofReal R * ∫⁻ s in Set.Ioo 0 1, ENNReal.ofReal (J (R * s)) :=
      lintegral_dilate_Ioo _ hR
    _ ≤ ENNReal.ofReal R * ∫⁻ s in Set.Ioo 0 1,
        ENNReal.ofReal ((R / r) ^ k) * ENNReal.ofReal (J (r * s)) :=
      mul_le_mul_right (setLIntegral_mono' measurableSet_Ioo hpoint) _
    _ = ENNReal.ofReal R * (ENNReal.ofReal ((R / r) ^ k) *
        ∫⁻ s in Set.Ioo 0 1, ENNReal.ofReal (J (r * s))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((R / r) ^ (k + 1)) *
        (ENNReal.ofReal r * ∫⁻ s in Set.Ioo 0 1, ENNReal.ofReal (J (r * s))) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hR), hcoeff,
        ENNReal.ofReal_mul (pow_nonneg hc (k + 1)), mul_assoc]
    _ = _ := by rw [lintegral_dilate_Ioo (fun t => ENNReal.ofReal (J t)) hr]

/-- Extending the polar Jacobian by zero beyond its cut time preserves the
normalized density monotonicity. -/
theorem cutDensity_ratio_antitone {k : ℕ} {c : ℝ} {J : ℝ → ℝ}
    (hanti : AntitoneOn (fun t => J t / t ^ k) (Set.Ioo 0 c))
    (hJ : ∀ t ∈ Set.Ioo 0 c, 0 ≤ J t) :
    AntitoneOn (fun t => (Set.Iio c).indicator J t / t ^ k) (Set.Ioi 0) := by
  intro s hs t ht hst
  by_cases htc : t < c
  · have hsc := lt_of_le_of_lt hst htc
    simpa only [Set.indicator, Set.mem_Iio, if_pos htc, if_pos hsc] using
      hanti ⟨hs, hsc⟩ ⟨ht, htc⟩ hst
  · simp only [Set.indicator, Set.mem_Iio, if_neg htc, zero_div]
    by_cases hsc : s < c
    · rw [if_pos hsc]
      exact div_nonneg (hJ s ⟨hs, hsc⟩) (pow_nonneg (le_of_lt hs) k)
    · rw [if_neg hsc, zero_div]

/-- Integrating the radial comparison over all directions preserves the same
dimension constant.  No interchange of two integrals is assumed. -/
theorem angularRadialIntegral_comparison {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) {k : ℕ} (J : Ω → ℝ → ℝ)
    (hanti : ∀ θ, AntitoneOn (fun t => J θ t / t ^ k) (Set.Ioi 0))
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (∫⁻ θ, ∫⁻ t in Set.Ioo 0 R, ENNReal.ofReal (J θ t) ∂volume ∂σ) ≤
      ENNReal.ofReal ((R / r) ^ (k + 1)) *
        ∫⁻ θ, ∫⁻ t in Set.Ioo 0 r, ENNReal.ofReal (J θ t) ∂volume ∂σ := by
  calc
    _ ≤ ∫⁻ θ, ENNReal.ofReal ((R / r) ^ (k + 1)) *
        ∫⁻ t in Set.Ioo 0 r, ENNReal.ofReal (J θ t) ∂volume ∂σ :=
      lintegral_mono fun θ => radialIntegral_comparison (hanti θ) hr hrR
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem curveLength_nonneg (h : HermitianField M) {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) : 0 ≤ curveLength h γ :=
  integral_nonneg fun _ => Real.sqrt_nonneg _

/-- Every actual admissible curve bounds the defined length distance above. -/
theorem inducedDistance_le_curveLength (h : HermitianField M) {x y : M.Carrier}
    (γ : IntegrableCurve h x y) : inducedDistance h x y ≤ curveLength h γ.1 := by
  apply csInf_le _ (Set.mem_range_self γ)
  refine ⟨0, ?_⟩
  rintro _ ⟨η, rfl⟩
  exact curveLength_nonneg h η.1

/-- The actual infimum supplies arbitrarily close-to-minimal admissible curves. -/
theorem exists_nearMinimizingCurve (g : SmoothMetric M) (x y : M.Carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : IntegrableCurve g.form x y,
      curveLength g.form γ.1 < inducedDistance g.form x y + ε := by
  obtain ⟨γ⟩ := g.integrable_curve_nonempty x y
  have hne : (Set.range (fun η : IntegrableCurve g.form x y =>
      curveLength g.form η.1)).Nonempty := ⟨_, Set.mem_range_self γ⟩
  have hlt : sInf (Set.range (fun η : IntegrableCurve g.form x y =>
      curveLength g.form η.1)) < inducedDistance g.form x y + ε := by
    exact lt_add_of_pos_right _ hε
  obtain ⟨_, ⟨η, rfl⟩, hη⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨η, hη⟩

/-- Connected noncompact complex manifolds have positive complex dimension. -/
theorem manifold_dimension_pos (M : ComplexManifold n) : 0 < n := by
  by_contra hn
  have hn0 := Nat.eq_zero_of_not_pos hn
  subst n
  letI : DiscreteTopology M.Carrier :=
    ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  letI : Subsingleton M.Carrier := subsingleton_of_preconnected_totallyDisconnected
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace M.Carrier))
    (inferInstance : CompactSpace M.Carrier)

/-- Actual inverse-chart differentiation, in both directions on chart source. -/
theorem tangentCoords_chartVec (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : ComplexVector n) :
    tangentCoords x y (chartVec x y v) = v := by
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
    (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  exact congrArg (fun L => L v) hcomp

theorem chartVec_tangentCoords (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : TangentVector M y) :
    chartVec x y (tangentCoords x y v) = v := by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  exact congrArg (fun L => L v) hcomp

/-- The real metric `G = 2 Re h` as an actual real bilinear map on the fibre. -/
def hermitianRealBilin {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (h : HermitianInnerProduct V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => 2 * (h.toFun v w).re)
    (by
      intro u v w
      rw [h.map_add_left, Complex.add_re, mul_add])
    (by
      intro r v w
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), h.map_smul_left]
      simp [Complex.mul_re, smul_eq_mul]
      ring)
    (by
      intro u v w
      rw [h.map_add_right, Complex.add_re, mul_add])
    (by
      intro r v w
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), h.map_smul_right]
      simp [Complex.mul_re, smul_eq_mul]
      ring)

theorem hermitianRealBilin_apply {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (h : HermitianInnerProduct V) (v w : V) :
    hermitianRealBilin h v w = 2 * (h.toFun v w).re := rfl

theorem hermitianRealBilin_symm {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (h : HermitianInnerProduct V) (v w : V) :
    hermitianRealBilin h v w = hermitianRealBilin h w v := by
  have hr := congrArg Complex.re (h.conjugate_symmetric v w)
  simp only [Complex.star_def, Complex.conj_re] at hr
  exact congrArg (2 * ·) hr

theorem hermitianRealBilin_pos {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (h : HermitianInnerProduct V) {v : V} (hv : v ≠ 0) :
    0 < hermitianRealBilin h v v :=
  mul_pos (by norm_num) (hermitianNormSq_pos h hv)

/-- Finite-dimensional continuity uses the fibre's existing topology. -/
def hermitianRealContinuousBilin {V : Type*} [AddCommGroup V]
    [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] (h : HermitianInnerProduct V) : V →L[ℝ] V →L[ℝ] ℝ :=
  (hermitianRealBilin h).toContinuousBilinearMap

theorem hermitianRealContinuousBilin_apply {V : Type*} [AddCommGroup V]
    [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] (h : HermitianInnerProduct V) (v w : V) :
    hermitianRealContinuousBilin h v w = 2 * (h.toFun v w).re := rfl

/-- A positive definite bilinear form on an actual finite-dimensional normed
space controls that space's existing norm. -/
theorem positiveBilin_coercive {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ B v v := by
  rcases subsingleton_or_nontrivial V with hsub | hnontrivial
  · letI := hsub
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · letI := hnontrivial
    have hcont : Continuous (fun v : V => B v v) := by fun_prop
    obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    have hwn : ‖w‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    have hwne : w ≠ 0 := by
      intro hzero
      simp [hzero] at hwn
    refine ⟨B w w, hpos w hwne, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hu : (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : V) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      convert! norm_smul_inv_norm (𝕜 := ℝ) hv
    have hminv := hmin hu
    change B w w ≤ B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at hminv
    simp only [map_smul, smul_apply, smul_eq_mul] at hminv
    calc
      B w w * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ * (‖v‖⁻¹ * B v v)) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hminv (sq_nonneg _)
      _ = B v v := by field_simp

theorem positiveBilin_unitSublevel_bounded {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : V | B v v < 1} := by
  obtain ⟨c, hc, hbound⟩ := positiveBilin_coercive B hpos
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  refine ⟨Real.sqrt (1 / c), ?_⟩
  intro v hv
  change B v v < 1 at hv
  have hs : ‖v‖ ^ 2 ≤ 1 / c := (le_div_iff₀ hc).mpr (by nlinarith [hbound v])
  calc
    ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hs

theorem positiveBilin_unitSublevel_bounded_topological {V : Type*}
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : V | B v v < 1} := by
  letI : IsNormableSpace ℝ V := isNormableSpace_of_finiteDimensional
  let e := (Module.finBasis ℝ V).equivFunL
  let B0 := B.bilinearComp e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap
  have hB0 : ∀ v, v ≠ 0 → 0 < B0 v v := by
    intro v hv
    change 0 < B (e.symm v) (e.symm v)
    apply hpos
    intro hz
    change e.symm v = 0 at hz
    apply hv
    apply e.symm.injective
    simpa only [map_zero] using hz
  have hb := positiveBilin_unitSublevel_bounded B0 hB0
  apply (hb.image e.symm.toContinuousLinearMap).subset
  intro v hv
  refine ⟨e v, ?_, e.symm_apply_apply v⟩
  change B (e.symm (e v)) (e.symm (e v)) < 1
  change B v v < 1 at hv
  simpa only [e.symm_apply_apply] using hv

theorem finiteBilin_diagonal_continuous {V : Type*}
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) : Continuous (fun v => B v v) := by
  letI : IsNormableSpace ℝ V := isNormableSpace_of_finiteDimensional
  let e := (Module.finBasis ℝ V).equivFunL
  let B0 := B.bilinearComp e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap
  have hc : Continuous (fun v => B0 v v) :=
    B0.continuous.clm_apply continuous_id
  convert! hc.comp e.continuous using 1
  funext v
  change B v v = B (e.symm (e v)) (e.symm (e v))
  rw [e.symm_apply_apply]

/-- The project's intrinsic Hermitian field gives a genuine Mathlib real
Riemannian fibre metric with exactly `G(v,w) = 2 Re h(v,w)`. -/
def hermitianRiemannianMetric (h : HermitianField M) :
    Bundle.RiemannianMetric (fun x : M.Carrier => TangentVector M x) := by
  letI : ∀ x : M.Carrier, ContinuousSMul ℝ (TangentVector M x) :=
    fun _ => IsScalarTower.continuousSMul ℂ
  letI : ∀ x : M.Carrier, IsNormableSpace ℝ (TangentVector M x) :=
    fun _ => isNormableSpace_of_finiteDimensional
  exact
    { inner x := hermitianRealContinuousBilin (h x)
      symm x v w := hermitianRealBilin_symm (h x) v w
      pos x v hv := hermitianRealBilin_pos (h x) hv
      continuousAt x := (finiteBilin_diagonal_continuous
        (hermitianRealContinuousBilin (h x))).continuousAt
      isVonNBounded x := by
        apply positiveBilin_unitSublevel_bounded_topological
        intro v hv
        rw [hermitianRealContinuousBilin_apply]
        exact mul_pos (by norm_num) (hermitianNormSq_pos (h x) hv) }

theorem hermitianRiemannianMetric_inner (h : HermitianField M) (x : M.Carrier)
    (v w : TangentVector M x) :
    (hermitianRiemannianMetric h).inner x v w = 2 * ((h x).toFun v w).re := rfl

theorem realCoord_sum_realVec (r : RIdx n → ℝ) (a : RIdx n) :
    realCoord (∑ b, r b • realVec b) a = r a := by
  rcases a with ⟨i, j⟩
  fin_cases j <;>
    simp [realCoord, realVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.single_apply]
  all_goals
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [Ne.symm hbi]
    · simp

theorem realVec_linearIndependent (n : ℕ) : LinearIndependent ℝ (realVec (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro r hr a
  have ha := congrArg (fun v => realCoord v a) hr
  rw [realCoord_sum_realVec] at ha
  simpa only [realCoord, PiLp.zero_apply, Complex.zero_re, Complex.zero_im, ite_self] using ha

def hermitianTangentNormedAddCommGroup (h : HermitianField M) (x : M.Carrier) :
    NormedAddCommGroup (TangentVector M x) := by
  letI : ContinuousSMul ℝ (TangentVector M x) := IsScalarTower.continuousSMul ℂ
  exact ((hermitianRiemannianMetric h).toCore x).toNormedAddCommGroupOfTopology
    ((hermitianRiemannianMetric h).continuousAt x)
    ((hermitianRiemannianMetric h).isVonNBounded x)

def hermitianTangentInnerProductSpace (h : HermitianField M) (x : M.Carrier) :
    letI := hermitianTangentNormedAddCommGroup h x
    InnerProductSpace ℝ (TangentVector M x) := by
  letI : ContinuousSMul ℝ (TangentVector M x) := IsScalarTower.continuousSMul ℂ
  exact InnerProductSpace.ofCoreOfTopology ((hermitianRiemannianMetric h).toCore x)
    ((hermitianRiemannianMetric h).continuousAt x)
    ((hermitianRiemannianMetric h).isVonNBounded x)

theorem hermitianRiemannianMetric_norm (h : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) :
    letI := hermitianTangentNormedAddCommGroup h x
    ‖v‖ = Real.sqrt (2 * hermitianNormSq (h x) v) := by
  letI : NormedAddCommGroup (TangentVector M x) := hermitianTangentNormedAddCommGroup h x
  rfl

theorem chartVec_real_sum (x y : M.Carrier) (r : RIdx n → ℝ) :
    chartVec x y (∑ a, r a • realVec a) = ∑ a, r a • chartVec x y (realVec a) := by
  let L := ((mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x).symm (chartPt x y)).comp
      (tangentSpaceCastModel (ComplexModel n) (chartPt x y)).symm.toContinuousLinearMap).restrictScalars ℝ
  change L (∑ a, r a • realVec a) = ∑ a, r a • L (realVec a)
  simp only [map_sum, map_smul]

theorem realMetricFn_quadratic (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (r : RIdx n → ℝ) :
    star r ⬝ᵥ ((realMetricFn h x z) *ᵥ r) =
      hermitianRealBilin (h (chartInv x z))
        (chartVec x (chartInv x z) (∑ a, r a • realVec a))
        (chartVec x (chartInv x z) (∑ a, r a • realVec a)) := by
  simp only [chartVec_real_sum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Pi.star_apply,
    star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hermitianRealBilin_apply]
  unfold realMetricFn
  have hs := congrArg Complex.re ((h (chartInv x z)).conjugate_symmetric
    (chartVec x (chartInv x z) (realVec a)) (chartVec x (chartInv x z) (realVec b)))
  simp only [Complex.star_def, Complex.conj_re] at hs
  rw [hs]
  ring

theorem realMetricFn_posDef (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) :
    (realMetricFn h x z).PosDef := by
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hz
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext a b
    exact hermitianRealBilin_symm (h (chartInv x z)) _ _
  · intro r hr
    rw [realMetricFn_quadratic]
    apply hermitianRealBilin_pos
    intro hzero
    have hcoords := congrArg (tangentCoords x (chartInv x z)) hzero
    rw [tangentCoords_chartVec x (chartInv x z) hy] at hcoords
    have hsum : (∑ a, r a • realVec a) = 0 := by
      convert! hcoords using 1
      simp only [tangentCoords, map_zero]
      rfl
    apply hr
    funext a
    have ha := congrArg (fun v => realCoord v a) hsum
    rw [realCoord_sum_realVec] at ha
    simpa only [realCoord, PiLp.zero_apply, Pi.zero_apply, Complex.zero_re,
      Complex.zero_im, ite_self] using ha

theorem volumeDensity_pos (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) :
    0 < Real.sqrt (realMetricFn h x z).det :=
  Real.sqrt_pos.mpr (realMetricFn_posDef h x z hz).det_pos

/- The following short coordinate calculations are repeated from L18Aux to
keep the dependency direction L18 -> L12 and avoid a module cycle. -/

theorem chartVec_complex_smul (x y : M.Carrier) (c : ℂ) (v : ComplexVector n) :
    chartVec x y (c • v) = c • chartVec x y v := by
  exact (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x).symm (chartPt x y)).map_smul c v

theorem realMetricFn_entries (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a b : RIdx n) :
    realMetricFn h x z a b = 2 *
      (if a.2 = b.2 then (hMat h x z a.1 b.1).re
        else if a.2 = 0 then -(hMat h x z a.1 b.1).im
        else (hMat h x z a.1 b.1).im) := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realMetricFn, realVec, hMat, stdVec, chartVec_complex_smul,
      HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right]

theorem hMat_eq_chartCoefficientFunction (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (i j : Fin n) :
    hMat h x z i j = chartCoefficientFunction h x i j z := rfl

theorem hMat_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => hMat g.form x z i j) (chartTarget x) := by
  simpa only [hMat_eq_chartCoefficientFunction, chartTarget] using
    g.coordinate_smooth x i j

theorem metricSmooth_of_smoothMetric (g : SmoothMetric M) : MetricSmooth g.form := by
  intro x a b
  simp_rw [realMetricFn_entries]
  split_ifs
  · exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn
      (hMat_contDiffOn g x a.1 b.1))
  · exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn
      (hMat_contDiffOn g x a.1 b.1)).neg
  · exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn
      (hMat_contDiffOn g x a.1 b.1))

/-- The same holomorphic charts give the underlying smooth real manifold. -/
theorem manifold_realSmooth (M : ComplexManifold n) :
    IsManifold 𝓘(ℝ, ComplexVector n) ∞ M.Carrier := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ComplexVector n) ∞ M.Carrier
  intro e e' he he'
  have hc := (ComplexModel n).contDiffOn_extendCoordChange (n := ∞)
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  convert! hc.restrict_scalars ℝ using 1
  simp [ModelWithCorners.extendCoordChange_source, ComplexModel, mfld_simps]

/-- Canonical real-linear identification of the real and complex tangent
fibres, before endowing either fibre with a metric norm. -/
def realTangentEquiv (x : M.Carrier) :
    TangentSpace 𝓘(ℝ, ComplexVector n) x ≃L[ℝ] TangentVector M x :=
  (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x).trans
    ((tangentSpaceCastModel (ComplexModel n) x).restrictScalars ℝ).symm

/-- The actual real tangent bundle receives the same metric `2 Re h`. -/
def underlyingRealRiemannianMetric (h : HermitianField M) :
    Bundle.RiemannianMetric (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI : ∀ x : M.Carrier, IsNormableSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun _ => isNormableSpace_of_finiteDimensional
  letI : ∀ x : M.Carrier, ContinuousSMul ℝ (TangentVector M x) :=
    fun _ => IsScalarTower.continuousSMul ℂ
  letI : ∀ x : M.Carrier, IsNormableSpace ℝ (TangentVector M x) :=
    fun _ => isNormableSpace_of_finiteDimensional
  let B := fun x => ((hermitianRiemannianMetric h).inner x).bilinearComp
    (realTangentEquiv x).toContinuousLinearMap (realTangentEquiv x).toContinuousLinearMap
  have hpos : ∀ x v, v ≠ 0 → 0 < B x v v := by
    intro x v hv
    change 0 < (hermitianRiemannianMetric h).inner x
      (realTangentEquiv x v) (realTangentEquiv x v)
    apply (hermitianRiemannianMetric h).pos
    intro hz
    apply hv
    apply (realTangentEquiv x).injective
    simpa only [map_zero] using hz
  exact
    { inner := B
      symm x v w := (hermitianRiemannianMetric h).symm x _ _
      pos := hpos
      continuousAt x := (finiteBilin_diagonal_continuous (B x)).continuousAt
      isVonNBounded x := positiveBilin_unitSublevel_bounded_topological (B x) (hpos x) }

theorem underlyingRealRiemannianMetric_inner (h : HermitianField M) (x : M.Carrier)
    (v w : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    (underlyingRealRiemannianMetric h).inner x v w =
      2 * ((h x).toFun (realTangentEquiv x v) (realTangentEquiv x w)).re := rfl

theorem real_extChartAt_eq (x : M.Carrier) :
    extChartAt 𝓘(ℝ, ComplexVector n) x = extChartAt (ComplexModel n) x := rfl

theorem real_writtenInExtChartAt_eq {m : ℕ} {N : ComplexManifold m}
    (f : M.Carrier → N.Carrier) (x : M.Carrier) :
    writtenInExtChartAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector m) x f =
      writtenInExtChartAt (ComplexModel n) (ComplexModel m) x f := rfl

theorem hasMFDerivAt_real {m : ℕ} {N : ComplexManifold m}
    {f : M.Carrier → N.Carrier} {x : M.Carrier}
    {F : TangentVector M x →L[ℂ] TangentVector N (f x)}
    (hf : HasMFDerivAt (ComplexModel n) (ComplexModel m) f x F) :
    HasMFDerivAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector m) f x
      ((realTangentEquiv (M := N) (f x)).symm.toContinuousLinearMap ∘L
        F.restrictScalars ℝ ∘L (realTangentEquiv x).toContinuousLinearMap) := by
  refine ⟨hf.1, ?_⟩
  have hd := hf.2.restrictScalars ℝ
  convert! hd using 1 <;> simp only [ModelWithCorners.range_eq_univ]

theorem mdifferentiableAt_real {m : ℕ} {N : ComplexManifold m}
    {f : M.Carrier → N.Carrier} {x : M.Carrier}
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel m) f x) :
    MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector m) f x :=
  (hasMFDerivAt_real hf.hasMFDerivAt).mdifferentiableAt

theorem mfderiv_real {m : ℕ} {N : ComplexManifold m}
    {f : M.Carrier → N.Carrier} {x : M.Carrier}
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel m) f x) :
    mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector m) f x =
      (realTangentEquiv (M := N) (f x)).symm.toContinuousLinearMap ∘L
        (mfderiv (ComplexModel n) (ComplexModel m) f x).restrictScalars ℝ ∘L
          (realTangentEquiv x).toContinuousLinearMap :=
  (hasMFDerivAt_real hf.hasMFDerivAt).mfderiv

def realChartVec (x : M.Carrier) (z v : ComplexVector n) :
    TangentSpace 𝓘(ℝ, ComplexVector n) (chartInv x z) :=
  mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (chartInv x) z
    ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)

/-- Differentiating the same inverse chart over `ℝ` and over `ℂ` gives the
same actual tangent vector under the canonical real tangent identification. -/
theorem realTangentEquiv_realChartVec (x : M.Carrier) (z v : ComplexVector n)
    (hz : z ∈ chartTarget x) :
    realTangentEquiv (chartInv x z) (realChartVec x z v) =
      chartVec x (chartInv x z) v := by
  let S := ComplexEuclideanManifold n (Nat.succ_le_iff.mpr (manifold_dimension_pos M))
  have hf : MDifferentiableAt (ComplexModel n) (ComplexModel n)
      (fun u : S.Carrier => chartInv x u) z := by
    have hc := mdifferentiableWithinAt_extChartAt_symm (I := ComplexModel n) hz
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at hc
  have hd := mfderiv_real (M := S) (N := M) hf
  have hv := congrArg (fun A => realTangentEquiv (chartInv x z)
    (A ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v))) hd
  have hsource : realTangentEquiv (M := S) z
      ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v) =
        (tangentSpaceCastModel (ComplexModel n) z).symm v := rfl
  change realTangentEquiv (chartInv x z) (realChartVec x z v) =
    realTangentEquiv (chartInv x z) ((realTangentEquiv (chartInv x z)).symm
      (((mfderiv (ComplexModel n) (ComplexModel n) (chartInv x) z).restrictScalars ℝ)
        (realTangentEquiv (M := S) z
          ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)))) at hv
  rw [ContinuousLinearEquiv.apply_symm_apply, hsource] at hv
  have hpt : chartPt x (chartInv x z) = z :=
    (extChartAt (ComplexModel n) x).right_inv hz
  unfold chartVec
  rw [hpt]
  exact hv

/-- The independently constructed real Riemannian metric has exactly the
project's coordinate coefficients in its genuine real inverse-chart frame. -/
theorem underlyingRealRiemannianMetric_frame (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    (underlyingRealRiemannianMetric h).inner (chartInv x z)
      (realChartVec x z (realVec a)) (realChartVec x z (realVec b)) =
        realMetricFn h x z a b := by
  rw [underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec x z (realVec a) hz,
    realTangentEquiv_realChartVec x z (realVec b) hz]
  rfl

theorem underlyingRealRiemannianMetric_frame_smooth (g : SmoothMetric M)
    (x : M.Carrier) (a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => (underlyingRealRiemannianMetric g.form).inner (chartInv x z)
      (realChartVec x z (realVec a)) (realChartVec x z (realVec b))) (chartTarget x) := by
  apply (metricSmooth_of_smoothMetric g x a b).congr
  intro z hz
  exact underlyingRealRiemannianMetric_frame g.form x z hz a b

theorem realCoord_injective (n : ℕ) : Function.Injective (realCoord (n := n)) := by
  intro u v huv
  apply PiLp.ext
  intro i
  apply Complex.ext
  · simpa only [realCoord, ite_eq_left_iff, ite_true] using congrFun huv (i, 0)
  · simpa [realCoord] using congrFun huv (i, 1)

theorem sum_realCoord_realVec (v : ComplexVector n) :
    (∑ a, realCoord v a • realVec a) = v := by
  apply realCoord_injective n
  funext a
  exact realCoord_sum_realVec (realCoord v) a

theorem realBilin_eq_sum (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (u v : ComplexVector n) :
    B u v = ∑ a, ∑ b, realCoord u a * realCoord v b * B (realVec a) (realVec b) := by
  conv_lhs => rw [← sum_realCoord_realVec u, ← sum_realCoord_realVec v]
  rw [map_sum B, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul B, smul_apply, map_sum (B (realVec a)), smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul (B (realVec a)), smul_eq_mul]
  ring

/-- For the genuine finite real chart basis, smoothness of every scalar
coefficient gives smoothness of the entire continuous bilinear map. -/
theorem contDiffOn_realBilin_of_basis {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : Set D} {B : D → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ}
    (hB : ∀ a b : RIdx n, ContDiffOn ℝ ∞ (fun z => B z (realVec a) (realVec b)) s) :
    ContDiffOn ℝ ∞ B s := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  have hc : ContDiffOn ℝ ∞
      (fun z => ∑ a, ∑ b, realCoord u a * realCoord v b * B z (realVec a) (realVec b)) s := by
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ => contDiffOn_const.mul (hB a b)
  apply hc.congr
  intro z _
  exact realBilin_eq_sum (B z) u v

def realMetricInChart (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ := by
  letI : IsNormableSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) (chartInv x z)) :=
    isNormableSpace_of_finiteDimensional
  let L := (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (chartInv x) z).comp
    (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm.toContinuousLinearMap
  exact ((underlyingRealRiemannianMetric h).inner (chartInv x z)).bilinearComp L L

theorem realMetricInChart_apply (h : HermitianField M) (x : M.Carrier)
    (z u v : ComplexVector n) :
    realMetricInChart h x z u v = (underlyingRealRiemannianMetric h).inner (chartInv x z)
      (realChartVec x z u) (realChartVec x z v) := rfl

theorem realMetricInChart_smooth (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (realMetricInChart g.form x) (chartTarget x) := by
  apply contDiffOn_realBilin_of_basis
  intro a b
  simpa only [realMetricInChart_apply] using
    underlyingRealRiemannianMetric_frame_smooth g x a b

open Bundle in
set_option maxHeartbeats 400000 in
def smoothUnderlyingRealRiemannianMetric (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    ContMDiffRiemannianMetric 𝓘(ℝ, ComplexVector n) ∞ (ComplexVector n)
      (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := manifold_realSmooth M
  let G := underlyingRealRiemannianMetric g.form
  refine
    { inner := G.inner
      symm := G.symm
      pos := G.pos
      isVonNBounded := G.isVonNBounded
      contMDiff := ?_ }
  intro x
  rw [contMDiffAt_section]
  rw [contMDiffAt_iff_source]
  simp only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ,
    contMDiffAt_iff_contDiffAt]
  have hn : chartTarget x ∈ 𝓝 (chartPt x x) :=
    extChartAt_target_mem_nhds (I := ComplexModel n) x
  have hc := (realMetricInChart_smooth g x).contDiffAt hn
  have heq : ∀ z ∈ chartTarget x,
      (trivializationAt (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
        (fun y : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) y →L[ℝ]
          TangentSpace 𝓘(ℝ, ComplexVector n) y →L[ℝ] ℝ) x
        ⟨chartInv x z, G.inner (chartInv x z)⟩).2 = realMetricInChart g.form x z := by
    intro z hz
    have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
      simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
    have hbase : chartInv x z ∈ (trivializationAt (ComplexVector n)
        (fun y : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) y) x).baseSet := hy
    have hframe : ∀ u : ComplexVector n,
        (trivializationAt (ComplexVector n)
          (fun y : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) y) x).symm
            (chartInv x z) u = realChartVec x z u := by
      intro u
      rw [← (trivializationAt (ComplexVector n)
        (fun y : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) y) x).symmL_apply (R := ℝ) hbase u]
      rw [TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, ComplexVector n)) hy]
      simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ]
      change mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (chartInv x)
        (chartPt x (chartInv x z))
        ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) (chartPt x (chartInv x z))).symm u) = _
      have hpt : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
      rw [hpt]
      rfl
    ext u v
    simp only [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂ hbase hbase (Set.mem_univ _)]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
    rw [realMetricInChart_apply, hframe, hframe]
  apply hc.congr_of_eventuallyEq
  filter_upwards [hn] with z hz
  exact heq z hz


theorem smoothUnderlyingRealRiemannianMetric_toRiemannianMetric (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    (smoothUnderlyingRealRiemannianMetric g).toRiemannianMetric =
      underlyingRealRiemannianMetric g.form := by
  rfl

theorem realTangent_finrank (x : M.Carrier) :
    Module.finrank ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) = 2 * n := by
  calc
    Module.finrank ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) =
        Module.finrank ℝ (ComplexVector n) :=
      (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x).toLinearEquiv.finrank_eq
    _ = 2 * n := by
      rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex]
      simp [ComplexVector]

theorem chartVec_self (x : M.Carrier) (v : ComplexVector n) :
    chartVec x x v = (tangentSpaceCastModel (ComplexModel n) x).symm v := by
  have hi := mfderivWithin_range_extChartAt_symm (I := ComplexModel n) (x := x)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
  have hv := congrArg (fun L => L ((tangentSpaceCastModel (ComplexModel n) (chartPt x x)).symm v)) hi
  exact hv

def realCurveVelocity (f : ℝ → M.Carrier) (t : ℝ) :
    TangentSpace 𝓘(ℝ, ComplexVector n) (f t) :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) f t
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)

theorem realCurveVelocity_chart {f : ℝ → M.Carrier} {t : ℝ}
    (hcont : ContinuousAt f t)
    (hdiff : DifferentiableAt ℝ (fun s => extChartAt (ComplexModel n) (f t) (f s)) t) :
    realTangentEquiv (f t) (realCurveVelocity f t) =
      (tangentSpaceCastModel (ComplexModel n) (f t)).symm
        ((fderiv ℝ (fun s => extChartAt (ComplexModel n) (f t) (f s)) t) 1) := by
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) f t := by
    rw [mdifferentiableAt_iff]
    refine ⟨hcont, ?_⟩
    convert! hdiff.differentiableWithinAt using 1 <;>
      simp [writtenInExtChartAt, real_extChartAt_eq, mfld_simps]
  rw [realCurveVelocity, hf.mfderiv]
  simp [writtenInExtChartAt, real_extChartAt_eq, realTangentEquiv, mfld_simps]
  rfl


theorem realTangentDerivative_eq_chart {x y : M.Carrier} (γ : PiecewiseC1Curve x y) (t : ℝ) :
    realTangentDerivative γ t =
      (tangentSpaceCastModel (ComplexModel n) (γ t)).symm
        ((fderiv ℝ (fun s => extChartAt (ComplexModel n) (γ t) (γ s)) t) 1) := by
  change chartVec (γ t) (γ t)
    ((fderiv ℝ (fun s => extChartAt (ComplexModel n) (γ t) (γ s)) t) 1) = _
  exact chartVec_self _ _

theorem realCurveVelocity_eq_derivative {x y : M.Carrier} (γ : PiecewiseC1Curve x y)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) (hbreak : t ∉ γ.breakpoints) :
    realTangentEquiv (γ t) (realCurveVelocity γ t) = realTangentDerivative γ t := by
  have hc : ContinuousAt γ.toFun t :=
    γ.continuous_on.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hd := (γ.piecewise_c1 t hbreak).differentiableAt (by norm_num)
  exact (realCurveVelocity_chart hc hd).trans (realTangentDerivative_eq_chart γ t).symm

@[instance_reducible]
def underlyingRealTangentNormedAddCommGroup (h : HermitianField M) (x : M.Carrier) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
  ((underlyingRealRiemannianMetric h).toCore x).toNormedAddCommGroupOfTopology
    ((underlyingRealRiemannianMetric h).continuousAt x)
    ((underlyingRealRiemannianMetric h).isVonNBounded x)

theorem underlyingRealTangent_norm (h : HermitianField M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    letI := underlyingRealTangentNormedAddCommGroup h x
    ‖v‖ = Real.sqrt (2 * hermitianNormSq (h x) (realTangentEquiv x v)) := by
  rfl

theorem realCurveVelocity_norm (h : HermitianField M) {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) {t : ℝ} (ht : t ∈ Set.Ioo 0 1)
    (hbreak : t ∉ γ.breakpoints) :
    letI := underlyingRealTangentNormedAddCommGroup h (γ t)
    ‖realCurveVelocity γ t‖ = curveSpeed h γ t := by
  letI := underlyingRealTangentNormedAddCommGroup h (γ t)
  rw [underlyingRealTangent_norm, realCurveVelocity_eq_derivative γ ht hbreak]
  rfl

/-- The project length integral is exactly Mathlib's path length for the same
real Riemannian metric.  The endpoints and finite breakpoints contribute zero. -/
theorem curveLength_eq_pathELength (h : HermitianField M) {x y : M.Carrier}
    (γ : IntegrableCurve h x y) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup h z
    ENNReal.ofReal (curveLength h γ.1) =
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ.1 0 1 := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo, curveLength,
    ofReal_integral_eq_lintegral_ofReal γ.2
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _)]
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply lintegral_congr_ae
  have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ γ.1.breakpoints :=
    γ.1.breakpoints.finite_toSet.countable.ae_notMem volume
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hb] with t ht hbreak
  change ENNReal.ofReal (curveSpeed h γ.1 t) = ‖realCurveVelocity γ.1 t‖ₑ
  rw [← ofReal_norm, realCurveVelocity_norm h γ.1 ht hbreak]

set_option backward.isDefEq.respectTransparency false in
theorem realMetricTensor_quadratic (h : HermitianField M) (p : M.Carrier) (w : TangentVector M p) :
    (∑ a, ∑ b, realMetricFn h p (chartPt p p) a b *
      realCoord (tangentCoords p p w) a * realCoord (tangentCoords p p w) b) =
        2 * hermitianNormSq (h p) w := by
  have hq := realMetricFn_quadratic h p (chartPt p p) (realCoord (tangentCoords p p w))
  have hp : chartInv p (chartPt p p) = p :=
    (extChartAt (ComplexModel n) p).left_inv (mem_extChartAt_source p)
  rw [hp, sum_realCoord_realVec,
    chartVec_tangentCoords p p (mem_extChartAt_source p)] at hq
  rw [hermitianRealBilin_apply] at hq
  change _ = 2 * hermitianNormSq (h p) w at hq
  rw [← hq]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem paperLengthNormalization (h : HermitianField M) : PaperLengthNormalization h := by
  intro _ x y γ
  unfold curveLength curveSpeed
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun t =>
    (congrArg Real.sqrt (realMetricTensor_quadratic h (γ t) (realTangentDerivative γ t))).symm

open Bundle

@[instance_reducible]
def underlyingRealTangentInnerProductSpace (h : HermitianField M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup h x
    InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
  InnerProductSpace.ofCoreOfTopology ((underlyingRealRiemannianMetric h).toCore x)
    ((underlyingRealRiemannianMetric h).continuousAt x)
    ((underlyingRealRiemannianMetric h).isVonNBounded x)

theorem realRiemannianBundle_continuous (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentNormedAddCommGroup g.form x
    letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentInnerProductSpace g.form x
    IsContinuousRiemannianBundle (ComplexVector n)
      (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := manifold_realSmooth M
  letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup g.form x
  letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentInnerProductSpace g.form x
  refine ⟨(underlyingRealRiemannianMetric g.form).inner, ?_, ?_⟩
  · exact (smoothUnderlyingRealRiemannianMetric g).contMDiff.continuous
  · intro x v w
    rfl

theorem realRiemannianBundle_contMDiff (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentNormedAddCommGroup g.form x
    letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentInnerProductSpace g.form x
    IsContMDiffRiemannianBundle 𝓘(ℝ, ComplexVector n) ∞ (ComplexVector n)
      (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := manifold_realSmooth M
  letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup g.form x
  letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentInnerProductSpace g.form x
  refine ⟨(underlyingRealRiemannianMetric g.form).inner, ?_, ?_⟩
  · exact (smoothUnderlyingRealRiemannianMetric g).contMDiff
  · intro x v w
    rfl

theorem continuous_realLineUnitSection :
    Continuous (fun t : ℝ =>
      (⟨t, (tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  simp only [trivializationAt_model_space_apply]
  convert! (continuousAt_const (y := (1 : ℝ))) using 1

theorem continuous_realCurveVelocity {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) :
    letI := manifold_realSmooth M
    Continuous (fun t =>
      (⟨f t, realCurveVelocity f t⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) := by
  letI := manifold_realSmooth M
  convert! (hf.continuous_tangentMap (by norm_num)).comp continuous_realLineUnitSection using 1

theorem continuous_norm_realCurveVelocity (g : SmoothMetric M) {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) :
    letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentNormedAddCommGroup g.form x
    Continuous (fun t => ‖realCurveVelocity f t‖) := by
  letI := manifold_realSmooth M
  letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup g.form x
  letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentInnerProductSpace g.form x
  letI := realRiemannianBundle_continuous g
  have hv := continuous_realCurveVelocity hf
  have hi := hv.inner_bundle hv
  have hs := Real.continuous_sqrt.comp hi
  convert! hs using 1


theorem contDiffAt_chart_of_contMDiff {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) (t : ℝ) :
    ContDiffAt ℝ 1 (fun s : ℝ => extChartAt (ComplexModel n) (f t) (f s)) t := by
  have hd := (contMDiffAt_iff.mp (hf t)).2
  simp only [real_extChartAt_eq, mfld_simps, contDiffWithinAt_univ] at hd
  convert! hd using 1

def piecewiseC1Curve_of_contMDiff {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) : PiecewiseC1Curve (f 0) (f 1) where
  toFun := f
  start_eq := rfl
  finish_eq := rfl
  breakpoints := ∅
  breakpoints_mem := by simp
  continuous_on := hf.continuous.continuousOn
  piecewise_c1 := fun t _ => contDiffAt_chart_of_contMDiff hf t

theorem integrable_curveSpeed_of_contMDiff (g : SmoothMetric M) {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) :
    IntegrableOn (curveSpeed g.form (piecewiseC1Curve_of_contMDiff hf)) (Set.Icc (0 : ℝ) 1) := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  have hc : Continuous (curveSpeed g.form (piecewiseC1Curve_of_contMDiff hf)) := by
    convert! continuous_norm_realCurveVelocity g hf using 1
    ext t
    rw [underlyingRealTangent_norm,
      realCurveVelocity_chart hf.continuous.continuousAt
        ((contDiffAt_chart_of_contMDiff hf t).differentiableAt (by norm_num))]
    unfold curveSpeed
    rw [realTangentDerivative_eq_chart]
    rfl
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

def integrableCurve_of_contMDiff (g : SmoothMetric M) {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) :
    IntegrableCurve g.form (f 0) (f 1) :=
  ⟨piecewiseC1Curve_of_contMDiff hf, integrable_curveSpeed_of_contMDiff g hf⟩

theorem inducedDistance_le_riemannianEDist (g : SmoothMetric M) (x y : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    ENNReal.ofReal (inducedDistance g.form x y) ≤
      Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  by_contra! hr
  obtain ⟨f, hx, hy, hf, hlen, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  let γ := integrableCurve_of_contMDiff g hf
  have hD := inducedDistance_le_curveLength g.form γ
  have hD' : inducedDistance g.form x y ≤ curveLength g.form γ.1 :=
    (congrArg₂ (inducedDistance g.form) hx hy).ge.trans hD
  have hLen := curveLength_eq_pathELength g.form γ
  change ENNReal.ofReal (curveLength g.form γ.1) =
    Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 1 at hLen
  have hcontra : ENNReal.ofReal (inducedDistance g.form x y) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 1 := by
    rw [← hLen]
    exact ENNReal.ofReal_le_ofReal hD'
  exact (not_lt_of_ge hcontra) hlen


@[instance_reducible]
def realRiemannianBundle (h : HermitianField M) :
    RiemannianBundle (fun z : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
  ⟨underlyingRealRiemannianMetric h⟩

@[instance_reducible]
def realEMetricSpace (g : SmoothMetric M) : EMetricSpace M.Carrier := by
  letI := manifold_realSmooth M
  letI := manifold_locallyCompact M
  letI := realRiemannianBundle g.form
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  letI := realRiemannianBundle_continuous g
  exact EMetricSpace.ofRiemannianMetric 𝓘(ℝ, ComplexVector n) M.Carrier

set_option backward.isDefEq.respectTransparency false in
theorem realEMetricSpace_edist (g : SmoothMetric M) (x y : M.Carrier) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    @edist M.Carrier (realEMetricSpace g).toEDist x y =
      Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y := by
  rfl

theorem realEMetricSpace_topology (g : SmoothMetric M) :
    (realEMetricSpace g).toUniformSpace.toTopologicalSpace = M.topology := rfl

theorem realEMetricSpace_complete (g : SmoothMetric M) :
    @CompleteSpace M.Carrier (realEMetricSpace g).toUniformSpace := by
  letI := realEMetricSpace g
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m k : ℕ, N ≤ m → N ≤ k → inducedDistance g.form (u m) (u k) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hu (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.mpr hε)
    refine ⟨N, fun m k hm hk => ?_⟩
    have hcomp := inducedDistance_le_riemannianEDist g (u m) (u k)
    have hlt : ENNReal.ofReal (inducedDistance g.form (u m) (u k)) < ENNReal.ofReal ε :=
      hcomp.trans_lt (by simpa only [realEMetricSpace_edist g] using hN m hm k hk)
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hlt
  obtain ⟨x, hx⟩ := g.complete_distance u hsmall
  refine ⟨x, ?_⟩
  change Tendsto u atTop (@nhds M.Carrier M.topology x)
  letI := inducedMetricSpace g
  apply Metric.tendsto_atTop.mpr
  change ∀ ε > 0, ∃ N, ∀ k ≥ N, inducedDistance g.form (u k) x < ε
  exact hx


theorem riemannianEDist_le_pathELength_of_contMDiffAt_Ioo (g : SmoothMetric M)
    {f : ℝ → M.Carrier} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f t) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) (f a) (f b) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  letI := realEMetricSpace g
  rcases hab.eq_or_lt with rfl | hab
  · simp [Manifold.riemannianEDist_self]
  have hordered : ∀ u ∈ Set.Ioo a b, ∀ v ∈ Set.Ioo a b, u ≤ v →
      edist (f u) (f v) ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
    intro u hu v hv huv
    rw [realEMetricSpace_edist g]
    apply (Manifold.riemannianEDist_le_pathELength (γ := f)
      (a := u) (b := v) (x := f u) (y := f v) ?_ rfl rfl huv).trans
        (Manifold.pathELength_mono hu.1.le hv.2.le)
    intro t ht
    exact (hd t ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩).contMDiffWithinAt
  have hbound : ∀ p ∈ Set.Ioo a b ×ˢ Set.Ioo a b,
      edist (f p.1) (f p.2) ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
    intro p hp
    rcases le_total p.1 p.2 with h | h
    · exact hordered _ hp.1 _ hp.2 h
    · rw [edist_comm]
      exact hordered _ hp.2 _ hp.1 h
  have hcl : closure (Set.Ioo a b ×ˢ Set.Ioo a b) = Set.Icc a b ×ˢ Set.Icc a b := by
    rw [closure_prod_eq, closure_Ioo hab.ne]
  have hfst : ContinuousOn (fun p : ℝ × ℝ => f p.1) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hc.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hsnd : ContinuousOn (fun p : ℝ × ℝ => f p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hc.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hdist := continuous_edist.comp_continuousOn (hfst.prodMk hsnd)
  have hend := le_on_closure hbound (by rw [hcl]; convert! hdist using 1) continuousOn_const
    (x := (a, b)) (by rw [hcl]; exact ⟨⟨le_rfl, hab.le⟩, ⟨hab.le, le_rfl⟩⟩)
  rw [realEMetricSpace_edist g] at hend
  exact hend

theorem riemannianEDist_le_pathELength_of_finite_exceptions (g : SmoothMetric M)
    {f : ℝ → M.Carrier} (s : Finset ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ s →
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f t) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) (f a) (f b) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
  classical
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  induction s using Finset.induction_on generalizing a b with
  | empty =>
    apply riemannianEDist_le_pathELength_of_contMDiffAt_Ioo g hab hc
    intro t ht
    exact hd t ht (by simp)
  | @insert c s hcs ih =>
    by_cases hac : a < c
    · by_cases hcb : c < b
      · have hleft := ih hac.le
          (hc.mono (Set.Icc_subset_Icc le_rfl hcb.le))
          (fun t ht hnot => hd t ⟨ht.1, ht.2.trans hcb⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt ht.2, hnot⟩))
        have hright := ih hcb.le
          (hc.mono (Set.Icc_subset_Icc hac.le le_rfl))
          (fun t ht hnot => hd t ⟨hac.trans ht.1, ht.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt ht.1, hnot⟩))
        exact (Manifold.riemannianEDist_triangle (I := 𝓘(ℝ, ComplexVector n))
          (x := f a) (y := f c) (z := f b)).trans
            ((add_le_add hleft hright).trans_eq (Manifold.pathELength_add hac.le hcb.le))
      · apply ih hab hc
        intro t ht hnot
        apply hd t ht
        simp only [Finset.mem_insert, not_or]
        exact ⟨ne_of_lt (ht.2.trans_le (le_of_not_gt hcb)), hnot⟩
    · apply ih hab hc
      intro t ht hnot
      apply hd t ht
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_gt ((le_of_not_gt hac).trans_lt ht.1), hnot⟩

theorem riemannianEDist_le_curveLength (g : SmoothMetric M) {x y : M.Carrier}
    (γ : IntegrableCurve g.form x y) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y ≤
      ENNReal.ofReal (curveLength g.form γ.1) := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  rw [curveLength_eq_pathELength g.form γ]
  have hd := riemannianEDist_le_pathELength_of_finite_exceptions g γ.1.breakpoints
    zero_le_one γ.1.continuous_on (fun t ht hnot => ?_)
  · simpa only [γ.1.start_eq, γ.1.finish_eq] using hd
  · rw [contMDiffAt_iff]
    refine ⟨γ.1.continuous_on.continuousAt (Icc_mem_nhds ht.1 ht.2), ?_⟩
    simp only [real_extChartAt_eq, mfld_simps, contDiffWithinAt_univ]
    convert! γ.1.piecewise_c1 t hnot using 1

theorem inducedDistance_eq_riemannianEDist (g : SmoothMetric M) (x y : M.Carrier) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    ENNReal.ofReal (inducedDistance g.form x y) =
      Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  apply le_antisymm (inducedDistance_le_riemannianEDist g x y)
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  by_cases hrinf : r = ⊤
  · exact hrinf ▸ le_top
  have hpos : 0 < r.toReal :=
    ENNReal.toReal_pos (lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ _) hr).ne' hrinf
  have hreal : inducedDistance g.form x y < r.toReal := by
    rw [← ENNReal.ofReal_toReal hrinf] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mp hr
  obtain ⟨γ, hγ⟩ := exists_nearMinimizingCurve g x y (sub_pos.mpr hreal)
  exact (riemannianEDist_le_curveLength g γ).trans
    ((ENNReal.ofReal_le_ofReal (show curveLength g.form γ.1 ≤ r.toReal by linarith)).trans_eq (ENNReal.ofReal_toReal hrinf))

theorem inducedMetricSpace_isRiemannianManifold (g : SmoothMetric M) :
    letI := inducedMetricSpace g
    letI := realRiemannianBundle g.form
    IsRiemannianManifold 𝓘(ℝ, ComplexVector n) M.Carrier := by
  letI := inducedMetricSpace g
  letI := realRiemannianBundle g.form
  constructor
  intro x y
  rw [edist_dist]
  exact inducedDistance_eq_riemannianEDist g x y

theorem realEMetricSpace_eq_inducedMetricSpace (g : SmoothMetric M) :
    realEMetricSpace g = (inducedMetricSpace g).toEMetricSpace := by
  apply EMetricSpace.ext
  ext x y
  rw [realEMetricSpace_edist g]
  rw [@edist_dist M.Carrier (inducedMetricSpace g).toPseudoMetricSpace]
  exact (inducedDistance_eq_riemannianEDist g x y).symm


theorem exists_radial_approximation (g : SmoothMetric M) (x y : M.Carrier)
    {r ε : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ inducedDistance g.form x y) (hε : 0 < ε) :
    ∃ z : M.Carrier, inducedDistance g.form x z = r ∧
      inducedDistance g.form z y < inducedDistance g.form x y - r + ε := by
  letI := manifold_realSmooth M
  letI := inducedMetricSpace g
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  have hpos : 0 < inducedDistance g.form x y + ε :=
    add_pos_of_nonneg_of_pos (by change 0 ≤ dist x y; exact dist_nonneg) hε
  have he : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y <
      ENNReal.ofReal (inducedDistance g.form x y + ε) := by
    rw [← inducedDistance_eq_riemannianEDist g]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (lt_add_of_pos_right _ hε)
  obtain ⟨f, hx, hy, hf, hlen, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt he zero_lt_one
  have hcont : Continuous (fun t => dist x (f t)) := continuous_const.dist hf.continuous
  have hm : r ∈ Set.Icc (dist x (f 0)) (dist x (f 1)) := by
    simpa only [hx, hy, dist_self, inducedMetricSpace_dist, Set.mem_Icc] using And.intro hr0 hr
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn hm
  change inducedDistance g.form x (f t) = r at htr
  refine ⟨f t, htr, ?_⟩
  have hleft : ENNReal.ofReal r ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 t := by
    rw [← htr, inducedDistance_eq_riemannianEDist g]
    exact Manifold.riemannianEDist_le_pathELength hf.contMDiffOn hx rfl ht.1
  have hright : ENNReal.ofReal (inducedDistance g.form (f t) y) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) f t 1 := by
    rw [inducedDistance_eq_riemannianEDist g]
    exact Manifold.riemannianEDist_le_pathELength hf.contMDiffOn rfl hy ht.2
  have hsum : ENNReal.ofReal (r + inducedDistance g.form (f t) y) <
      ENNReal.ofReal (inducedDistance g.form x y + ε) := by
    rw [ENNReal.ofReal_add hr0 (by change 0 ≤ dist (f t) y; exact dist_nonneg)]
    exact ((add_le_add hleft hright).trans_eq
      (Manifold.pathELength_add ht.1 ht.2)).trans_lt hlen
  have hreal := (ENNReal.ofReal_lt_ofReal_iff hpos).mp hsum
  linarith


open Set Metric

variable {X : Type*} [MetricSpace X]

theorem closedBall_near_smallerBall
    (hrad : ∀ (x y : X) {r ε : ℝ}, 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε)
    (x : X) {r R δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (hR : R < r + δ) :
    ∀ y ∈ closedBall x R, ∃ z ∈ closedBall x r, dist y z < δ := by
  intro y hy
  by_cases hyr : dist x y ≤ r
  · exact ⟨y, by simpa only [mem_closedBall, dist_comm] using hyr, by simpa⟩
  have hε : 0 < (r + δ - R) / 2 := by linarith
  obtain ⟨z, hz, hzy⟩ := hrad x y hr (le_of_not_ge hyr) hε
  refine ⟨z, by rw [mem_closedBall, dist_comm, hz], ?_⟩
  have hyR : dist x y ≤ R := by simpa only [mem_closedBall, dist_comm] using hy
  rw [dist_comm]
  linarith

theorem compactBall_of_compact_smallerBalls [CompleteSpace X]
    (hrad : ∀ (x y : X) {r ε : ℝ}, 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε)
    (x : X) (R : ℝ)
    (happrox : ∀ ε > 0, ∃ r : ℝ, 0 ≤ r ∧ R - ε < r ∧ IsCompact (closedBall x r)) :
    IsCompact (closedBall x R) := by
  apply TotallyBounded.isCompact_of_isClosed ?_ isClosed_closedBall
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨r, hr, hRr, hcompact⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hcompact.totallyBounded
    (ε / 2) (half_pos hε)
  refine ⟨t, ht, ?_⟩
  intro y hy
  obtain ⟨z, hz, hyz⟩ := closedBall_near_smallerBall hrad x hr (half_pos hε)
    (by linarith) y hy
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hcover hz)
  apply mem_iUnion₂.mpr
  refine ⟨w, hw, ?_⟩
  change dist y w < ε
  have hzw' : dist z w < ε / 2 := hzw
  linarith [dist_triangle y z w]

theorem properSpace_of_radial_approximation [CompleteSpace X] [LocallyCompactSpace X]
    (hrad : ∀ (x y : X) {r ε : ℝ}, 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε) : ProperSpace X := by
  constructor
  intro x R
  by_contra hR
  let S : Set ℝ := {r | 0 ≤ r ∧ IsCompact (closedBall x r)}
  have hzero : (0 : ℝ) ∈ S := ⟨le_rfl, by simp⟩
  have hSne : S.Nonempty := ⟨0, hzero⟩
  have hbounded : BddAbove S := by
    refine ⟨R, ?_⟩
    intro r hr
    by_contra hrR
    exact hR (hr.2.of_isClosed_subset isClosed_closedBall
      (closedBall_subset_closedBall (le_of_not_ge hrR)))
  let ρ := sSup S
  have hρ : 0 ≤ ρ := le_csSup hbounded hzero
  have hcompact : IsCompact (closedBall x ρ) := by
    apply compactBall_of_compact_smallerBalls hrad
    intro ε hε
    obtain ⟨r, hr, hlt⟩ := exists_lt_of_lt_csSup hSne
      (show ρ - ε < sSup S by change ρ - ε < ρ; linarith)
    exact ⟨r, hr.1, hlt, hr.2⟩
  obtain ⟨δ, hδ, hK⟩ := hcompact.exists_isCompact_cthickening
  have hlarger : IsCompact (closedBall x (ρ + δ / 2)) := by
    apply hK.of_isClosed_subset isClosed_closedBall
    intro y hy
    obtain ⟨z, hz, hyz⟩ := closedBall_near_smallerBall hrad x hρ hδ
      (show ρ + δ / 2 < ρ + δ by linarith) y hy
    exact mem_cthickening_of_dist_le y z δ (closedBall x ρ) hz hyz.le
  have hmem : ρ + δ / 2 ∈ S := ⟨by linarith, hlarger⟩
  have hle := le_csSup hbounded hmem
  change ρ + δ / 2 ≤ ρ at hle
  linarith

open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem inducedMetricSpace_proper (g : SmoothMetric M) :
    letI := inducedMetricSpace g
    ProperSpace M.Carrier := by
  letI := inducedMetricSpace g
  refine @properSpace_of_radial_approximation M.Carrier (inducedMetricSpace g)
    (inducedMetricSpace_complete g) ?_ ?_
  · change @LocallyCompactSpace M.Carrier M.topology
    exact manifold_locallyCompact M
  · intro x y r ε hr0 hr hε
    exact exists_radial_approximation g x y hr0 hr hε

theorem isCompact_inducedDistance_sublevel (g : SmoothMetric M) (x : M.Carrier) (R : ℝ) :
    IsCompact {y : M.Carrier | inducedDistance g.form x y ≤ R} := by
  letI := inducedMetricSpace g
  letI := inducedMetricSpace_proper g
  convert! isCompact_closedBall x R using 1
  ext y
  simp only [Set.mem_setOf_eq, mem_closedBall, inducedMetricSpace_dist,
    g.induced_distance_symm x y]

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_exact_radial_of_radial_approximation
    (hrad : ∀ (x y : X) {r ε : ℝ}, 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε)
    (x y : X) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ dist x y) :
    ∃ z : X, dist x z = r ∧ dist z y = dist x y - r := by
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall x r).exists_isMinOn
    ⟨x, mem_closedBall_self hr0⟩ (continuous_id.dist continuous_const).continuousOn
  have hzle : dist x z ≤ r := by simpa only [mem_closedBall, dist_comm] using hz
  have hzy : dist z y ≤ dist x y - r := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    obtain ⟨w, hw, hwy⟩ := hrad x y hr0 hr (sub_pos.mpr ha)
    have hwmem : w ∈ closedBall x r := by rw [mem_closedBall, dist_comm, hw]
    have hle := hmin hwmem
    change dist z y ≤ dist w y at hle
    linarith
  have htriangle := dist_triangle x z y
  refine ⟨z, ?_, ?_⟩ <;> linarith

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_exact_radial (g : SmoothMetric M) (x y : M.Carrier)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ inducedDistance g.form x y) :
    ∃ z : M.Carrier, inducedDistance g.form x z = r ∧
      inducedDistance g.form z y = inducedDistance g.form x y - r := by
  letI := inducedMetricSpace g
  letI := inducedMetricSpace_proper g
  refine exists_exact_radial_of_radial_approximation ?_ x y hr0 hr
  intro a b s ε hs0 hs hε
  exact exists_radial_approximation g a b hs0 hs hε

variable {n : ℕ} {M : ComplexManifold n}

def realLeviCivitaConnection (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    CovariantDerivative 𝓘(ℝ, ComplexVector n) (ComplexVector n)
      (TangentSpace 𝓘(ℝ, ComplexVector n) : M.Carrier → Type) := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle g.form
  letI := realRiemannianBundle_contMDiff g
  exact CovariantDerivative.leviCivitaConnection 𝓘(ℝ, ComplexVector n) M.Carrier

theorem realLeviCivitaConnection_isLeviCivita (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := realRiemannianBundle g.form
    letI := realRiemannianBundle_contMDiff g
    CovariantDerivative.IsLeviCivitaConnection 𝓘(ℝ, ComplexVector n)
      (realLeviCivitaConnection g) := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle g.form
  letI := realRiemannianBundle_contMDiff g
  exact CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection 𝓘(ℝ, ComplexVector n)


def realCoordinateField (x : M.Carrier) (v : ComplexVector n) :
    ∀ y : M.Carrier, TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  letI := manifold_realSmooth M
  exact fun y => (trivializationAt (ComplexVector n)
    (TangentSpace 𝓘(ℝ, ComplexVector n) : M.Carrier → Type) x).symm y v

theorem realCoordinateField_contMDiffAt (x y : M.Carrier) (v : ComplexVector n)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) ∞
      (fun z => (⟨z, realCoordinateField x v z⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) y := by
  letI := manifold_realSmooth M
  let e := trivializationAt (ComplexVector n)
    (TangentSpace 𝓘(ℝ, ComplexVector n) : M.Carrier → Type) x
  have hybase : y ∈ e.baseSet := hy
  rw [e.contMDiffAt_section_iff hybase]
  apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hybase] with z hz
  change (e ⟨z, e.symm z v⟩).2 = v
  simp [hz]

theorem realCoordinateField_eq_realChartVec (x : M.Carrier) (z v : ComplexVector n)
    (hz : z ∈ chartTarget x) :
    realCoordinateField x v (chartInv x z) = realChartVec x z v := by
  letI := manifold_realSmooth M
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have hbase : chartInv x z ∈ (trivializationAt (ComplexVector n)
    (TangentSpace 𝓘(ℝ, ComplexVector n) : M.Carrier → Type) x).baseSet := hy
  unfold realCoordinateField
  rw [← (trivializationAt (ComplexVector n)
    (TangentSpace 𝓘(ℝ, ComplexVector n) : M.Carrier → Type) x).symmL_apply (R := ℝ) hbase v]
  rw [TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, ComplexVector n)) hy]
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ]
  change mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (chartInv x)
    (chartPt x (chartInv x z))
    ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) (chartPt x (chartInv x z))).symm v) = _
  have hpt : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  rw [hpt]
  rfl

def realConstantField (v : ComplexVector n) :
    ∀ z : ComplexVector n, TangentSpace 𝓘(ℝ, ComplexVector n) z :=
  fun z => (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v

theorem realConstantField_contMDiff (v : ComplexVector n) :
    ContMDiff 𝓘(ℝ, ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) ∞
      (fun z => (⟨z, realConstantField v z⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) (ComplexVector n))) := by
  intro z
  rw [contMDiffAt_section]
  simp only [trivializationAt_model_space_apply]
  convert! (contMDiffAt_const (c := v)) using 1

theorem realConstantField_mlieBracket (u v : ComplexVector n) :
    VectorField.mlieBracket 𝓘(ℝ, ComplexVector n) (realConstantField u) (realConstantField v) = 0 := by
  rw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin]
  funext z
  change VectorField.lieBracketWithin ℝ (fun _ => u) (fun _ => v) Set.univ z = 0
  simp [VectorField.lieBracketWithin]

theorem realCoordinateField_eq_mpullback (x y : M.Carrier) (v : ComplexVector n)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    realCoordinateField x v y =
      VectorField.mpullback 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
        (extChartAt 𝓘(ℝ, ComplexVector n) x) (realConstantField v) y := by
  letI := manifold_realSmooth M
  have hy' : y ∈ (extChartAt 𝓘(ℝ, ComplexVector n) x).source := by simpa only [extChartAt_source] using hy
  let e := trivializationAt (ComplexVector n)
    (TangentSpace 𝓘(ℝ, ComplexVector n) : M.Carrier → Type) x
  have hbase : y ∈ e.baseSet := hy
  symm
  apply (isInvertible_mfderiv_extChartAt hy').inverse_apply_eq.mpr
  change (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n)
    (extChartAt 𝓘(ℝ, ComplexVector n) x y)).symm v =
      mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
        (extChartAt 𝓘(ℝ, ComplexVector n) x) y (e.symm y v)
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy,
    ← e.symmL_apply (R := ℝ) hbase v]
  convert! (e.continuousLinearMapAt_symmL hbase v).symm using 1

theorem realCoordinateField_mlieBracket (x y : M.Carrier) (u v : ComplexVector n)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    VectorField.mlieBracket 𝓘(ℝ, ComplexVector n)
      (realCoordinateField x u) (realCoordinateField x v) y = 0 := by
  letI := manifold_realSmooth M
  have heq (w : ComplexVector n) : realCoordinateField x w =ᶠ[𝓝 y]
      VectorField.mpullback 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
        (extChartAt 𝓘(ℝ, ComplexVector n) x) (realConstantField w) := by
    filter_upwards [(chartAt (ComplexVector n) x).open_source.mem_nhds hy] with z hz
    exact realCoordinateField_eq_mpullback x z w hz
  have hu := (realConstantField_contMDiff u).mdifferentiable (by simp)
  have hv := (realConstantField_contMDiff v).mdifferentiable (by simp)
  letI : IsManifold 𝓘(ℝ, ComplexVector n) (minSmoothness ℝ 2) M.Carrier :=
    IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  have hb := VectorField.mpullback_mlieBracket
    (n := ∞)
    (f := extChartAt 𝓘(ℝ, ComplexVector n) x) (hu _) (hv _)
    (contMDiffAt_extChartAt' hy) (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) by simp)
  rw [realConstantField_mlieBracket, VectorField.mpullback_zero] at hb
  exact ((heq u).mlieBracket_vectorField_eq (heq v)).trans hb.symm

theorem mvfderiv_realCoordinateField (F : M.Carrier → ℝ) (x : M.Carrier)
    (z v : ComplexVector n) (hz : z ∈ chartTarget x)
    (hF : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) F (chartInv x z)) :
    mvfderiv 𝓘(ℝ, ComplexVector n) F (chartInv x z)
      (realCoordinateField x v (chartInv x z)) =
        fderiv ℝ (fun w => F (chartInv x w)) z v := by
  letI := manifold_realSmooth M
  have hz' : z ∈ (extChartAt 𝓘(ℝ, ComplexVector n) x).target := hz
  have hinv : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
      (chartInv x) z := by
    have hs := contMDiffWithinAt_extChartAt_symm_range
      (I := 𝓘(ℝ, ComplexVector n)) (n := ∞) x hz'
    rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hs
    exact hs.mdifferentiableAt (by simp)
  rw [realCoordinateField_eq_realChartVec x z v hz]
  have hchain := mvfderiv_comp_apply z hF hinv
    ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)
  rw [mvfderiv_eq_fderiv] at hchain
  exact hchain.symm

def realCoordinateMetric (h : HermitianField M) (x : M.Carrier) (u v : ComplexVector n)
    (y : M.Carrier) : ℝ :=
  (underlyingRealRiemannianMetric h).inner y
    (realCoordinateField x u y) (realCoordinateField x v y)

theorem realCoordinateMetric_inChart (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    realCoordinateMetric h x (realVec a) (realVec b) (chartInv x z) =
      realMetricFn h x z a b := by
  unfold realCoordinateMetric
  rw [realCoordinateField_eq_realChartVec x z (realVec a) hz,
    realCoordinateField_eq_realChartVec x z (realVec b) hz]
  exact underlyingRealRiemannianMetric_frame h x z hz a b

theorem realCoordinateMetric_mdifferentiableAt (g : SmoothMetric M) (x y : M.Carrier)
    (u v : ComplexVector n) (hy : y ∈ (chartAt (ComplexVector n) x).source) :
    MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (realCoordinateMetric g.form x u v) y := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle g.form
  letI := realRiemannianBundle_contMDiff g
  have hs := (realCoordinateField_contMDiffAt x y u hy).inner_bundle
    (realCoordinateField_contMDiffAt x y v hy)
  convert! hs.mdifferentiableAt (by simp) using 1

theorem mvfderiv_realCoordinateMetric (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    mvfderiv 𝓘(ℝ, ComplexVector n)
      (realCoordinateMetric g.form x (realVec b) (realVec c)) (chartInv x z)
      (realCoordinateField x (realVec a) (chartInv x z)) =
        rDeriv (fun w => realMetricFn g.form x w b c) z a := by
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  rw [mvfderiv_realCoordinateField _ x z (realVec a) hz
    (realCoordinateMetric_mdifferentiableAt g x (chartInv x z) _ _ hy)]
  have heq : (fun w => realCoordinateMetric g.form x (realVec b) (realVec c) (chartInv x w))
      =ᶠ[𝓝 z] (fun w => realMetricFn g.form x w b c) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact realCoordinateMetric_inChart g.form x w hw b c
  unfold rDeriv
  rw [heq.fderiv_eq]

theorem realLeviCivitaConnection_frame_inner (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    letI := manifold_realSmooth M
    (underlyingRealRiemannianMetric g.form).inner (chartInv x z)
      (realLeviCivitaConnection g (realCoordinateField x (realVec b)) (chartInv x z)
        (realCoordinateField x (realVec a) (chartInv x z)))
      (realCoordinateField x (realVec c) (chartInv x z)) =
        (rDeriv (fun w => realMetricFn g.form x w b c) z a +
          rDeriv (fun w => realMetricFn g.form x w c a) z b -
          rDeriv (fun w => realMetricFn g.form x w a b) z c) / 2 := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle g.form
  letI := realRiemannianBundle_contMDiff g
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have hA := (realCoordinateField_contMDiffAt x (chartInv x z) (realVec a) hy).mdifferentiableAt (by simp)
  have hB := (realCoordinateField_contMDiffAt x (chartInv x z) (realVec b) hy).mdifferentiableAt (by simp)
  have hC := (realCoordinateField_contMDiffAt x (chartInv x z) (realVec c) hy).mdifferentiableAt (by simp)
  have hk := CovariantDerivative.leviCivitaConnection_apply_inner
    𝓘(ℝ, ComplexVector n) hA hB hC
  simp only [realCoordinateField_mlieBracket x (chartInv x z) _ _ hy,
    inner_zero_right, sub_zero, add_zero] at hk
  change (underlyingRealRiemannianMetric g.form).inner (chartInv x z)
      (realLeviCivitaConnection g (realCoordinateField x (realVec b)) (chartInv x z)
        (realCoordinateField x (realVec a) (chartInv x z)))
      (realCoordinateField x (realVec c) (chartInv x z)) =
        (mvfderiv 𝓘(ℝ, ComplexVector n)
          (realCoordinateMetric g.form x (realVec b) (realVec c)) (chartInv x z)
          (realCoordinateField x (realVec a) (chartInv x z)) +
         mvfderiv 𝓘(ℝ, ComplexVector n)
          (realCoordinateMetric g.form x (realVec c) (realVec a)) (chartInv x z)
          (realCoordinateField x (realVec b) (chartInv x z)) -
         mvfderiv 𝓘(ℝ, ComplexVector n)
          (realCoordinateMetric g.form x (realVec a) (realVec b)) (chartInv x z)
          (realCoordinateField x (realVec c) (chartInv x z))) / 2 at hk
  rw [mvfderiv_realCoordinateMetric g x z hz a b c,
    mvfderiv_realCoordinateMetric g x z hz b c a,
    mvfderiv_realCoordinateMetric g x z hz c a b] at hk
  exact hk


theorem realMetricFn_symm (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a b : RIdx n) : realMetricFn h x z a b = realMetricFn h x z b a := by
  have he := congrArg Complex.re ((h (chartInv x z)).conjugate_symmetric
    (chartVec x (chartInv x z) (realVec a)) (chartVec x (chartInv x z) (realVec b)))
  simp only [Complex.star_def, Complex.conj_re] at he
  exact congrArg (fun t : ℝ => 2 * t) he

theorem christoffel_metric_contraction (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    (∑ d, christoffel g.form x z d a b * realMetricFn g.form x z d c) =
      (rDeriv (fun w => realMetricFn g.form x w b c) z a +
        rDeriv (fun w => realMetricFn g.form x w a c) z b -
        rDeriv (fun w => realMetricFn g.form x w a b) z c) / 2 := by
  let G := realMetricFn g.form x z
  let D : RIdx n → ℝ := fun d => rDeriv (fun w => realMetricFn g.form x w b d) z a +
    rDeriv (fun w => realMetricFn g.form x w a d) z b -
    rDeriv (fun w => realMetricFn g.form x w a b) z d
  have hv : G *ᵥ (G⁻¹ *ᵥ D) = D := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr (realMetricFn_posDef g.form x z hz).det_pos.ne'),
      Matrix.one_mulVec]
  calc
    _ = (1 / 2 : ℝ) * (G *ᵥ (G⁻¹ *ᵥ D)) c := by
      unfold christoffel
      change (∑ d, ((1 / 2 : ℝ) * ∑ e, G⁻¹ d e * D e) * G d c) = _
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show G d c = G c d from realMetricFn_symm g.form x z d c]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by rw [hv]; dsimp [D]; ring

theorem realCoordinateField_span (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    ∃ r : RIdx n → ℝ, w = ∑ a, r a • realCoordinateField x (realVec a) y := by
  letI := manifold_realSmooth M
  let e := trivializationAt (ComplexVector n)
    (TangentSpace 𝓘(ℝ, ComplexVector n) : M.Carrier → Type) x
  have hbase : y ∈ e.baseSet := hy
  let u := e.continuousLinearMapAt ℝ y w
  refine ⟨realCoord u, ?_⟩
  have he := e.symmL_continuousLinearMapAt (R := ℝ) hbase w
  change e.symmL ℝ y u = w at he
  rw [← he]
  conv_lhs => rw [← sum_realCoord_realVec u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [e.symmL_apply (R := ℝ) hbase (realVec a)]
  rfl

theorem realLeviCivitaConnection_frame (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (realCoordinateField x (realVec b)) (chartInv x z)
      (realCoordinateField x (realVec a) (chartInv x z)) =
        ∑ d, christoffel g.form x z d a b • realCoordinateField x (realVec d) (chartInv x z) := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle g.form
  letI := realRiemannianBundle_contMDiff g
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have htest (c : RIdx n) :
      (underlyingRealRiemannianMetric g.form).inner (chartInv x z)
        (realLeviCivitaConnection g (realCoordinateField x (realVec b)) (chartInv x z)
          (realCoordinateField x (realVec a) (chartInv x z)))
        (realCoordinateField x (realVec c) (chartInv x z)) =
      (underlyingRealRiemannianMetric g.form).inner (chartInv x z)
        (∑ d, christoffel g.form x z d a b • realCoordinateField x (realVec d) (chartInv x z))
        (realCoordinateField x (realVec c) (chartInv x z)) := by
    rw [realLeviCivitaConnection_frame_inner g x z hz a b c,
      map_sum ((underlyingRealRiemannianMetric g.form).inner (chartInv x z)),
      ContinuousLinearMap.sum_apply]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hinner (d : RIdx n) :
        (underlyingRealRiemannianMetric g.form).inner (chartInv x z)
          (realCoordinateField x (realVec d) (chartInv x z))
          (realCoordinateField x (realVec c) (chartInv x z)) =
        realMetricFn g.form x z d c := realCoordinateMetric_inChart g.form x z hz d c
    simp_rw [hinner]
    rw [christoffel_metric_contraction g x z hz a b c]
    rw [show (fun w => realMetricFn g.form x w c a) =
      (fun w => realMetricFn g.form x w a c) from
        funext fun w => realMetricFn_symm g.form x w c a]
  apply ext_inner_right ℝ
  intro w
  obtain ⟨r, hr⟩ := realCoordinateField_span x (chartInv x z) hy w
  rw [hr, inner_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [inner_smul_right, RCLike.conj_to_real]
  exact congrArg (fun t : ℝ => r c * t) (htest c)


/-- Compatibility name for the shared entrywise determinant calculus. -/
theorem contDiffOn_matrix_det {E ι 𝔸 : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {A : E → Matrix ι ι 𝔸} {s : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) s) :
    ContDiffOn ℝ ∞ (fun z => (A z).det) s :=
  SharedCalculus.contDiffOn_matrix_det hA

theorem contDiffOn_matrix_inv {E ι 𝕜 : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    {A : E → Matrix ι ι 𝕜} {s : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) s)
    (hdet : ∀ z ∈ s, (A z).det ≠ 0) (i j : ι) :
    ContDiffOn ℝ ∞ (fun z => (A z)⁻¹ i j) s :=
  SharedCalculus.contDiffOn_matrix_inv hA hdet i j

theorem realMetricFn_inverse_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => (realMetricFn g.form x z)⁻¹ a b) (chartTarget x) :=
  contDiffOn_matrix_inv (metricSmooth_of_smoothMetric g x)
    (fun z hz => (realMetricFn_posDef g.form x z hz).det_pos.ne') a b

theorem rDeriv_contDiffOn {f : ComplexVector n → ℝ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (a : RIdx n) : ContDiffOn ℝ ∞ (fun z => rDeriv f z a) O :=
  (hf.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

theorem christoffel_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (c a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => christoffel g.form x z c a b) (chartTarget x) := by
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro d _
  apply (realMetricFn_inverse_contDiffOn g x c d).mul
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  exact ((rDeriv_contDiffOn hO (metricSmooth_of_smoothMetric g x b d) a).add
    (rDeriv_contDiffOn hO (metricSmooth_of_smoothMetric g x a d) b)).sub
      (rDeriv_contDiffOn hO (metricSmooth_of_smoothMetric g x a b) d)

theorem contMDiffAt_chartLift_of_contDiffOn (x y : M.Carrier)
    {F : ComplexVector n → ℝ} (hF : ContDiffOn ℝ ∞ F (chartTarget x))
    (hy : y ∈ (chartAt (ComplexVector n) x).source) :
    ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (fun p => F (chartPt x p)) y := by
  letI := manifold_realSmooth M
  have hpoint : chartPt x y ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (by simpa only [extChartAt_source] using hy)
  have hc := hF.contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hpoint)
  exact hc.contMDiffAt.comp y (contMDiffAt_extChartAt' hy)

theorem realLeviCivitaConnection_finset_sum {ι : Type*} (g : SmoothMetric M) (s : Finset ι)
    (W : ι → ∀ y : M.Carrier, TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (p : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) p)
    (hW : letI := manifold_realSmooth M
      ∀ i ∈ s, MDifferentiableAt 𝓘(ℝ, ComplexVector n)
        (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
          (fun y => (⟨y, W i y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) p) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (∑ i ∈ s, W i) p v =
      ∑ i ∈ s, realLeviCivitaConnection g (W i) p v := by
  classical
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection g
  change cov (∑ i ∈ s, W i) p v = ∑ i ∈ s, cov (W i) p v
  induction s using Finset.induction_on with
  | empty => simp [cov.zero]
  | @insert i s hi ih =>
    rw [Finset.forall_mem_insert] at hW
    have hs := MDifferentiableAt.sum_section hW.2
    have hadd : cov (W i + ∑ j ∈ s, W j) p = cov (W i) p + cov (∑ j ∈ s, W j) p := by
      apply cov.isCovariantDerivativeOnUniv.add hW.1
      convert! hs using 1
      simp only [Finset.sum_apply]
    simp only [Finset.sum_insert hi]
    rw [hadd, ContinuousLinearMap.add_apply, ih hW.2]

def realConnectionFrame (g : SmoothMetric M) (x : M.Carrier) (a b : RIdx n) :
    ∀ y : M.Carrier, TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  letI := manifold_realSmooth M
  exact fun y => realLeviCivitaConnection g (realCoordinateField x (realVec b)) y
    (realCoordinateField x (realVec a) y)

theorem realConnectionFrame_eq_sum (g : SmoothMetric M) (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) (a b : RIdx n) :
    realConnectionFrame g x a b y =
      ∑ d, christoffel g.form x (chartPt x y) d a b • realCoordinateField x (realVec d) y := by
  have hz : chartPt x y ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (by simpa only [extChartAt_source] using hy)
  have hi : chartInv x (chartPt x y) = y :=
    (extChartAt (ComplexModel n) x).left_inv (by simpa only [extChartAt_source] using hy)
  have hk := realLeviCivitaConnection_frame g x (chartPt x y) hz a b
  rw [hi] at hk
  exact hk

theorem realConnectionFrame_contMDiffAt (g : SmoothMetric M) (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) (a b : RIdx n) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) ∞
      (fun p => (⟨p, realConnectionFrame g x a b p⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) y := by
  letI := manifold_realSmooth M
  have hs := ContMDiffAt.sum_section (s := Finset.univ) (fun d _ =>
    (contMDiffAt_chartLift_of_contDiffOn x y (christoffel_contDiffOn g x d a b) hy).smul_section
      (realCoordinateField_contMDiffAt x y (realVec d) hy))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt (ComplexVector n) x).open_source.mem_nhds hy] with p hp
  exact congrArg (fun v => (⟨p, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier))
    (realConnectionFrame_eq_sum g x p hp a b)

theorem mvfderiv_chartLift (x : M.Carrier) (z v : ComplexVector n)
    (hz : z ∈ chartTarget x) {F : ComplexVector n → ℝ}
    (hF : ContDiffOn ℝ ∞ F (chartTarget x)) :
    mvfderiv 𝓘(ℝ, ComplexVector n) (fun y => F (chartPt x y)) (chartInv x z)
      (realCoordinateField x v (chartInv x z)) = fderiv ℝ F z v := by
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  rw [mvfderiv_realCoordinateField _ x z v hz
    ((contMDiffAt_chartLift_of_contDiffOn x (chartInv x z) hF hy).mdifferentiableAt (by simp))]
  have heq : (fun w => F (chartPt x (chartInv x w))) =ᶠ[𝓝 z] F := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact congrArg F ((extChartAt (ComplexModel n) x).right_inv hw)
  rw [heq.fderiv_eq]

theorem realLeviCivitaConnection_frame_sum (g : SmoothMetric M) (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) (a : RIdx n)
    (C : RIdx n → M.Carrier → ℝ)
    (hC : ∀ d, MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (C d) y) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (∑ d, fun p => C d p • realCoordinateField x (realVec d) p) y
      (realCoordinateField x (realVec a) y) =
    ∑ d, (C d y • (∑ e, christoffel g.form x (chartPt x y) e a d •
      realCoordinateField x (realVec e) y) +
      mvfderiv 𝓘(ℝ, ComplexVector n) (C d) y (realCoordinateField x (realVec a) y) •
        realCoordinateField x (realVec d) y) := by
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection g
  have hD (d : RIdx n) :=
    (realCoordinateField_contMDiffAt x y (realVec d) hy).mdifferentiableAt (by simp)
  change cov (∑ d, C d • realCoordinateField x (realVec d)) y
    (realCoordinateField x (realVec a) y) = _
  rw [realLeviCivitaConnection_finset_sum g Finset.univ _ y _
    (fun d _ => (hC d).smul_section (hD d))]
  apply Finset.sum_congr rfl
  intro d _
  have hleib := cov.isCovariantDerivativeOnUniv.leibniz (hD d) (hC d)
  change cov ((C d) • realCoordinateField x (realVec d)) y _ = _
  rw [hleib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  have he := realConnectionFrame_eq_sum g x y hy a d
  change cov (realCoordinateField x (realVec d)) y
    (realCoordinateField x (realVec a) y) = _ at he
  rw [he]

theorem realLeviCivitaConnection_frame_iterated (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (realConnectionFrame g x b c) (chartInv x z)
      (realCoordinateField x (realVec a) (chartInv x z)) =
    ∑ d, (christoffel g.form x z d b c •
      (∑ e, christoffel g.form x z e a d • realCoordinateField x (realVec e) (chartInv x z)) +
      rDeriv (fun w => christoffel g.form x w d b c) z a •
        realCoordinateField x (realVec d) (chartInv x z)) := by
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection g
  let p := chartInv x z
  let C : RIdx n → M.Carrier → ℝ := fun d y => christoffel g.form x (chartPt x y) d b c
  let W := ∑ d, C d • realCoordinateField x (realVec d)
  have hy : p ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv, p] using (extChartAt (ComplexModel n) x).map_target hz
  have hpt : chartPt x p = z := (extChartAt (ComplexModel n) x).right_inv hz
  have hC (d : RIdx n) : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (C d) p :=
    (contMDiffAt_chartLift_of_contDiffOn x p (christoffel_contDiffOn g x d b c) hy).mdifferentiableAt (by simp)
  have hD (d : RIdx n) :=
    (realCoordinateField_contMDiffAt x p (realVec d) hy).mdifferentiableAt (by simp)
  have hW : MDifferentiableAt 𝓘(ℝ, ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) p := by
    convert! MDifferentiableAt.sum_section (s := Finset.univ)
      (fun d _ => (hC d).smul_section (hD d)) using 1
    simp only [W, Finset.sum_apply, Pi.smul_apply]
  have heq : realConnectionFrame g x b c =ᶠ[𝓝 p] W := by
    filter_upwards [(chartAt (ComplexVector n) x).open_source.mem_nhds hy] with y hy'
    rw [realConnectionFrame_eq_sum g x y hy']
    simp only [W, C, Finset.sum_apply, Pi.smul_apply]
    rfl
  have hloc := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((realConnectionFrame_contMDiffAt g x p hy b c).mdifferentiableAt (by simp)) hW
    Filter.univ_mem heq
  change cov (realConnectionFrame g x b c) p _ = _
  rw [hloc]
  have hexp := realLeviCivitaConnection_frame_sum g x p hy a C hC
  change cov W p (realCoordinateField x (realVec a) p) = _ at hexp
  rw [hexp]
  apply Finset.sum_congr rfl
  intro d _
  have hd := mvfderiv_chartLift x z (realVec a) hz (christoffel_contDiffOn g x d b c)
  change mvfderiv 𝓘(ℝ, ComplexVector n) (C d) p
    (realCoordinateField x (realVec a) p) =
      rDeriv (fun w => christoffel g.form x w d b c) z a at hd
  rw [hd]
  simp only [C, hpt]
  rfl

def realCurvatureFrame (g : SmoothMetric M) (x : M.Carrier) (a b c : RIdx n) :
    ∀ y : M.Carrier, TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection g
  exact fun y =>
    cov (realConnectionFrame g x b c) y (realCoordinateField x (realVec a) y) -
    cov (realConnectionFrame g x a c) y (realCoordinateField x (realVec b) y) -
    cov (realCoordinateField x (realVec c)) y
      (VectorField.mlieBracket 𝓘(ℝ, ComplexVector n)
        (realCoordinateField x (realVec a)) (realCoordinateField x (realVec b)) y)

theorem realCurvatureFrame_eq_riemannCoeff (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    realCurvatureFrame g x a b c (chartInv x z) =
      ∑ l, riemannCoeff g.form x z a b c l • realCoordinateField x (realVec l) (chartInv x z) := by
  letI := manifold_realSmooth M
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  unfold realCurvatureFrame
  rw [realCoordinateField_mlieBracket x (chartInv x z) _ _ hy, map_zero, sub_zero,
    realLeviCivitaConnection_frame_iterated g x z hz a b c,
    realLeviCivitaConnection_frame_iterated g x z hz b a c]
  have hprod (i j k : RIdx n) :
      (∑ d, christoffel g.form x z d j k •
        (∑ e, christoffel g.form x z e i d • realCoordinateField x (realVec e) (chartInv x z))) =
      ∑ e, (∑ d, christoffel g.form x z d j k * christoffel g.form x z e i d) •
        realCoordinateField x (realVec e) (chartInv x z) := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hprod a b c, hprod b a c]
  simp only [riemannCoeff, add_smul, sub_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_smul]
  abel


/- The following minimal Kähler chart-closure subgraph is transcribed from the
immutable /tmp/yau-l18-44.lean, SHA256
dddb59386cd1d770fd51350b396d5f1c212aeafe91ef78dfdd0d25f1168fc568.
Each declaration records the original L18Aux name and its new L12Aux name.
There is no import of L18.  Its chartVec_smul dependency is discharged by the
already proved chartVec_complex_smul.  The source's L09 orthonormal basis is
replaced by the realVec_basis below, proved from this file's existing linear
independence and vector reconstruction.  No additional hypothesis is introduced.
-/

def realVec_basis (n : ℕ) : Module.Basis (RIdx n) ℝ (ComplexVector n) :=
  Module.Basis.mk (realVec_linearIndependent n) (by
    intro u _
    rw [← sum_realCoord_realVec u]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem realVec_basis_apply (n : ℕ) (a : RIdx n) : realVec_basis n a = realVec a := by
  simp only [realVec_basis, Module.Basis.coe_mk]

-- Source: L18Aux.fderiv_pullback_bilin → L12Aux.fderiv_pullback_bilin
theorem fderiv_pullback_bilin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {B : F → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hB : DifferentiableAt ℝ B (f x)) (u v w : E) :
    fderiv ℝ (fun y => B (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) x w =
      fderiv ℝ B (f x) (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v) +
        B (f x) (fderiv ℝ (fderiv ℝ f) x w u) (fderiv ℝ f x v) +
          B (f x) (fderiv ℝ f x u) (fderiv ℝ (fderiv ℝ f) x w v) :=
  SharedCalculus.fderiv_pullback_bilin hf hB u v w

-- Source: L18Aux.cyclic_derivative_pullback_bilin → L12Aux.cyclic_derivative_pullback_bilin
theorem cyclic_derivative_pullback_bilin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {B : F → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hB : DifferentiableAt ℝ B (f x))
    (hskew : ∀ p q, B (f x) p q = -B (f x) q p) (u v w : E) :
    fderiv ℝ (fun y => B (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) x u +
      fderiv ℝ (fun y => B (f y) (fderiv ℝ f y w) (fderiv ℝ f y u)) x v +
      fderiv ℝ (fun y => B (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) x w =
    fderiv ℝ B (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) (fderiv ℝ f x w) +
      fderiv ℝ B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) (fderiv ℝ f x u) +
      fderiv ℝ B (f x) (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v) :=
  SharedCalculus.cyclic_derivative_pullback_bilin hf hB hskew u v w

-- Source: L18Aux.chartTransition_contDiffAt → L12Aux.chartTransition_contDiffAt
theorem chartTransition_contDiffAt {n : ℕ} {M : ComplexManifold n} (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    ContDiffAt ℂ ∞ (fun w => chartPt b (chartInv a w)) z := by
  have hi : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ (chartInv a) z :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) a).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)
  have ho : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ (chartPt b) (chartInv a z) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hy)
  exact (ho.comp z hi).contDiffAt

-- Source: L18Aux.chartTransition_fderiv → L12Aux.chartTransition_fderiv
theorem chartTransition_fderiv {n : ℕ} {M : ComplexManifold n} (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v : ComplexVector n) :
    fderiv ℂ (fun w => chartPt b (chartInv a w)) z v =
      tangentCoords b (chartInv a z) (chartVec a (chartInv a z) v) := by
  have hi : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) (chartInv a) z := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := ComplexModel n) hz
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have ho : MDifferentiableAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) (chartPt b) (chartInv a z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hy)
  have hcomp := mfderiv_comp_apply z ho hi v
  have hpt : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hz
  rw [mfderiv_eq_fderiv] at hcomp
  change fderiv ℂ (fun w => chartPt b (chartInv a w)) z v =
    mfderiv (ComplexModel n) (ComplexModel n) (chartPt b) (chartInv a z)
      (mfderiv (ComplexModel n) (ComplexModel n) (chartInv a) z v) at hcomp
  unfold tangentCoords chartVec
  rw [hpt]
  exact hcomp

-- Source: L18Aux.complexStructureCLM → L12Aux.complexStructureCLM
def complexStructureCLM (n : ℕ) : ComplexVector n →L[ℝ] ComplexVector n :=
  (Complex.I • ContinuousLinearMap.id ℂ (ComplexVector n)).restrictScalars ℝ

-- Source: L18Aux.chartKahlerBilin → L12Aux.chartKahlerBilin
def chartKahlerBilin {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  (realMetricInChart h x z).comp (complexStructureCLM n)

-- Source: L18Aux.chartKahlerBilin_apply → L12Aux.chartKahlerBilin_apply
theorem chartKahlerBilin_apply {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v w : ComplexVector n) :
    chartKahlerBilin h x z v w =
      2 * ((h (chartInv x z)).toFun (chartVec x (chartInv x z) v)
        (chartVec x (chartInv x z) w)).im := by
  change realMetricInChart h x z (Complex.I • v) w = _
  rw [realMetricInChart_apply, underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec x z (Complex.I • v) hz,
    realTangentEquiv_realChartVec x z w hz,
    chartVec_complex_smul, (h (chartInv x z)).map_smul_left]
  simp [Complex.mul_re]

-- Source: L18Aux.chartKahlerBilin_contDiffOn → L12Aux.chartKahlerBilin_contDiffOn
theorem chartKahlerBilin_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartKahlerBilin g.form x) (chartTarget x) :=
  (realMetricInChart_smooth g x).clm_comp contDiffOn_const

-- Source: L18Aux.chartKahlerBilin_realVec → L12Aux.chartKahlerBilin_realVec
theorem chartKahlerBilin_realVec {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    chartKahlerBilin h x z (realVec a) (realVec b) = kahlerFormFn h x z a b :=
  chartKahlerBilin_apply h x hz (realVec a) (realVec b)

-- Source: L18Aux.chartKahlerBilin_skew → L12Aux.chartKahlerBilin_skew
theorem chartKahlerBilin_skew {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v w : ComplexVector n) :
    chartKahlerBilin h x z v w = -chartKahlerBilin h x z w v := by
  rw [chartKahlerBilin_apply h x hz, chartKahlerBilin_apply h x hz]
  have hs := congrArg Complex.im ((h (chartInv x z)).conjugate_symmetric
    (chartVec x (chartInv x z) v) (chartVec x (chartInv x z) w))
  simp only [Complex.star_def, Complex.conj_im] at hs
  linarith

-- Source: L18Aux.fderiv_bilin_apply_const → L12Aux.fderiv_bilin_apply_const
theorem fderiv_bilin_apply_const {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : E → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (u : E) (v w : F) :
    fderiv ℝ (fun y => B y v w) x u = fderiv ℝ B x u v w :=
  SharedCalculus.fderiv_bilin_apply_const hB u v w

-- Source: L18Aux.cyclic_trilinear_zero_of_basis → L12Aux.cyclic_trilinear_zero_of_basis
theorem cyclic_trilinear_zero_of_basis {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : Module.Basis ι ℝ E)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h : ∀ i j k, D (e i) (e j) (e k) + D (e j) (e k) (e i) +
      D (e k) (e i) (e j) = 0) (u v w : E) :
    D u v w + D v w u + D w u v = 0 :=
  SharedCalculus.cyclic_trilinear_zero_of_basis e D h u v w

-- Source: L18Aux.chartKahlerBilin_pullback → L12Aux.chartKahlerBilin_pullback
theorem chartKahlerBilin_pullback {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v w : ComplexVector n) :
    chartKahlerBilin h a z v w =
      chartKahlerBilin h b (chartPt b (chartInv a z))
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z v)
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z w) := by
  have hd : DifferentiableAt ℂ (fun t => chartPt b (chartInv a t)) z :=
    (chartTransition_contDiffAt a b hz hy).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  change chartKahlerBilin h a z v w =
    chartKahlerBilin h b (chartPt b (chartInv a z))
      (fderiv ℂ (fun t => chartPt b (chartInv a t)) z v)
      (fderiv ℂ (fun t => chartPt b (chartInv a t)) z w)
  have ht : chartPt b (chartInv a z) ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source hy
  have hinv : chartInv b (chartPt b (chartInv a z)) = chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  rw [chartTransition_fderiv a b hz hy v, chartTransition_fderiv a b hz hy w,
    chartKahlerBilin_apply h a hz, chartKahlerBilin_apply h b ht]
  rw [hinv,
    chartVec_tangentCoords b (chartInv a z) hy,
    chartVec_tangentCoords b (chartInv a z) hy]

-- Source: L18Aux.fderiv_chartKahlerBilin_realVec → L12Aux.fderiv_chartKahlerBilin_realVec
theorem fderiv_chartKahlerBilin_realVec {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    fderiv ℝ (chartKahlerBilin g.form x) z (realVec a) (realVec b) (realVec c) =
      rDeriv (fun t => kahlerFormFn g.form x t b c) z a := by
  have hB : DifferentiableAt ℝ (chartKahlerBilin g.form x) z :=
    ((chartKahlerBilin_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun t => chartKahlerBilin g.form x t (realVec b) (realVec c)) =ᶠ[𝓝 z]
      (fun t => kahlerFormFn g.form x t b c) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with t ht
    exact chartKahlerBilin_realVec g.form x ht b c
  rw [← fderiv_bilin_apply_const hB]
  exact congrArg (fun A => A (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))

-- Source: L18Aux.cyclic_chartKahlerBilin_center → L12Aux.cyclic_chartKahlerBilin_center
set_option synthInstance.maxHeartbeats 80000 in
theorem cyclic_chartKahlerBilin_center {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) (u v w : ComplexVector n) :
    fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x) u v w +
      fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x) v w u +
      fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x) w u v = 0 := by
  apply cyclic_trilinear_zero_of_basis (realVec_basis n)
    (fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x)) _ u v w
  intro a b c
  simp only [realVec_basis_apply]
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [fderiv_chartKahlerBilin_realVec g x hz,
    fderiv_chartKahlerBilin_realVec g x hz,
    fderiv_chartKahlerBilin_realVec g x hz]
  exact hK x a b c

-- Source: L18Aux.cyclic_chartKahlerBilin_on → L12Aux.cyclic_chartKahlerBilin_on
theorem cyclic_chartKahlerBilin_on {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (u v w : ComplexVector n) :
    fderiv ℝ (chartKahlerBilin g.form x) z u v w +
      fderiv ℝ (chartKahlerBilin g.form x) z v w u +
      fderiv ℝ (chartKahlerBilin g.form x) z w u v = 0 := by
  let y := chartInv x z
  let T : ComplexVector n → ComplexVector n := fun t => chartPt y (chartInv x t)
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have ht : T z ∈ chartTarget y := mem_extChartAt_target y
  have hT : ContDiffAt ℝ 2 T z :=
    ((chartTransition_contDiffAt x y hz hy).restrict_scalars ℝ).of_le (by simp)
  have hBx : DifferentiableAt ℝ (chartKahlerBilin g.form x) z :=
    ((chartKahlerBilin_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hBy : DifferentiableAt ℝ (chartKahlerBilin g.form y) (T z) :=
    ((chartKahlerBilin_contDiffOn g y).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds ht)).differentiableAt (by simp)
  have hskew (p q : ComplexVector n) :
      chartKahlerBilin g.form y (T z) p q = -chartKahlerBilin g.form y (T z) q p :=
    chartKahlerBilin_skew g.form y ht p q
  have hi : ContinuousAt (chartInv x) z := continuousAt_extChartAt_symm'' hz
  have hs : ∀ᶠ t in 𝓝 z, chartInv x t ∈ (extChartAt (ComplexModel n) y).source :=
    hi.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds hy)
  have hpull (p q : ComplexVector n) :
      (fun t => chartKahlerBilin g.form x t p q) =ᶠ[𝓝 z]
        (fun t => chartKahlerBilin g.form y (T t) (fderiv ℝ T t p) (fderiv ℝ T t q)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz, hs]
      with t htx hty
    exact chartKahlerBilin_pullback g.form x y htx hty p q
  have hderiv (p q r : ComplexVector n) :
      fderiv ℝ (chartKahlerBilin g.form x) z p q r =
        fderiv ℝ (fun t => chartKahlerBilin g.form y (T t)
          (fderiv ℝ T t q) (fderiv ℝ T t r)) z p := by
    rw [← fderiv_bilin_apply_const hBx]
    exact congrArg (fun A => A p) ((hpull q r).fderiv_eq (𝕜 := ℝ))
  rw [hderiv u v w, hderiv v w u, hderiv w u v]
  exact (cyclic_derivative_pullback_bilin hT hBy hskew u v w).trans
    (cyclic_chartKahlerBilin_center g hK y
      (fderiv ℝ T z u) (fderiv ℝ T z v) (fderiv ℝ T z w))

-- Source: L18Aux.kahlerClosed_in_chart → L12Aux.kahlerClosed_in_chart
theorem kahlerClosed_in_chart {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    rDeriv (fun t => kahlerFormFn g.form x t b c) z a +
      rDeriv (fun t => kahlerFormFn g.form x t c a) z b +
      rDeriv (fun t => kahlerFormFn g.form x t a b) z c = 0 := by
  have hc := cyclic_chartKahlerBilin_on g hK x hz (realVec a) (realVec b) (realVec c)
  rw [fderiv_chartKahlerBilin_realVec g x hz,
    fderiv_chartKahlerBilin_realVec g x hz, fderiv_chartKahlerBilin_realVec g x hz] at hc
  exact hc


/- Signed complex-structure coordinates and the all-chart Kähler derivative
identity are copied from the same immutable L18-44 source and SHA256 above.
The 13 original/new same-suffix names are recorded individually below.
The following Christoffel-J compatibility lemmas are proved here from these
identities and the actual metric inverse; no compatibility is assumed. -/

-- Source: L18Aux.jIndex → L12Aux.jIndex
def jIndex (n : ℕ) : RIdx n ≃ RIdx n :=
  Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.swap (0 : Fin 2) 1)

-- Source: L18Aux.jSign → L12Aux.jSign
def jSign {n : ℕ} (a : RIdx n) : ℝ := if a.2 = 0 then 1 else -1

-- Source: L18Aux.jIndex_involutive → L12Aux.jIndex_involutive
theorem jIndex_involutive {n : ℕ} (a : RIdx n) : jIndex n (jIndex n a) = a := by
  rcases a with ⟨i, a⟩
  fin_cases a <;> simp [jIndex]

-- Source: L18Aux.jSign_jIndex → L12Aux.jSign_jIndex
theorem jSign_jIndex {n : ℕ} (a : RIdx n) : jSign (jIndex n a) = -jSign a := by
  rcases a with ⟨i, a⟩
  fin_cases a <;> simp [jIndex, jSign]

-- Source: L18Aux.jSign_sq → L12Aux.jSign_sq
theorem jSign_sq {n : ℕ} (a : RIdx n) : jSign a * jSign a = 1 := by
  simp only [jSign]
  split_ifs <;> norm_num

-- Source: L18Aux.kahlerFormFn_entries → L12Aux.kahlerFormFn_entries
theorem kahlerFormFn_entries {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn h x z a b = 2 *
      (if a.2 = b.2 then (hMat h x z a.1 b.1).im
        else if a.2 = 0 then (hMat h x z a.1 b.1).re
        else -(hMat h x z a.1 b.1).re) := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [kahlerFormFn, realVec, hMat, stdVec, chartVec_complex_smul,
      HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right]

-- Source: L18Aux.realMetricFn_jIndex → L12Aux.realMetricFn_jIndex
theorem realMetricFn_jIndex {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    realMetricFn h x z (jIndex n a) (jIndex n b) =
      jSign a * jSign b * realMetricFn h x z a b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [jIndex, jSign, realMetricFn_entries]

-- Source: L18Aux.kahlerFormFn_jIndex_left → L12Aux.kahlerFormFn_jIndex_left
theorem kahlerFormFn_jIndex_left {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn h x z (jIndex n a) b = -jSign a * realMetricFn h x z a b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [jIndex, jSign, realMetricFn_entries, kahlerFormFn_entries]

-- Source: L18Aux.kahlerFormFn_jIndex_right → L12Aux.kahlerFormFn_jIndex_right
theorem kahlerFormFn_jIndex_right {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn h x z a (jIndex n b) = jSign b * realMetricFn h x z a b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [jIndex, jSign, realMetricFn_entries, kahlerFormFn_entries]

-- Source: L18Aux.kahlerFormFn_eq_jIndex_metric → L12Aux.kahlerFormFn_eq_jIndex_metric
theorem kahlerFormFn_eq_jIndex_metric {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn h x z a b = jSign a * realMetricFn h x z (jIndex n a) b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [jIndex, jSign, realMetricFn_entries, kahlerFormFn_entries]

-- Source: L18Aux.realMetricFn_differentiableAt → L12Aux.realMetricFn_differentiableAt
theorem realMetricFn_differentiableAt {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    DifferentiableAt ℝ (fun w => realMetricFn g.form x w a b) z :=
  ((metricSmooth_of_smoothMetric g x a b).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt
      (by simp)

-- Source: L18Aux.rDeriv_const_mul → L12Aux.rDeriv_const_mul
theorem rDeriv_const_mul {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (c : ℝ) (a : RIdx n) :
    rDeriv (fun w => c * f w) z a = c * rDeriv f z a := by
  unfold rDeriv
  rw [fderiv_const_mul hf c]
  simp

-- Source: L18Aux.kahler_metric_derivative_identity_on → L12Aux.kahler_metric_derivative_identity_on
theorem kahler_metric_derivative_identity_on {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b d : RIdx n) :
    -rDeriv (fun w => realMetricFn g.form x w b d) z a +
      jSign b * jSign d * rDeriv
        (fun w => realMetricFn g.form x w (jIndex n d) a) z (jIndex n b) +
      rDeriv (fun w => realMetricFn g.form x w a b) z d = 0 := by
  have hk := kahlerClosed_in_chart g hK x hz a (jIndex n b) d
  have h1 : (fun w => kahlerFormFn g.form x w (jIndex n b) d) =
      (fun w => (-jSign b) * realMetricFn g.form x w b d) := by
    funext w
    exact kahlerFormFn_jIndex_left g.form x w b d
  have h2 : (fun w => kahlerFormFn g.form x w d a) =
      (fun w => jSign d * realMetricFn g.form x w (jIndex n d) a) := by
    funext w
    exact kahlerFormFn_eq_jIndex_metric g.form x w d a
  have h3 : (fun w => kahlerFormFn g.form x w a (jIndex n b)) =
      (fun w => jSign b * realMetricFn g.form x w a b) := by
    funext w
    exact kahlerFormFn_jIndex_right g.form x w a b
  change rDeriv _ z a + rDeriv _ z (jIndex n b) +
    rDeriv _ z d = 0 at hk
  have hG (p q : RIdx n) :
      DifferentiableAt ℝ (fun w => realMetricFn g.form x w p q) z :=
    realMetricFn_differentiableAt g x hz p q
  rw [h1, h2, h3,
    rDeriv_const_mul (hG b d) (-jSign b) a,
    rDeriv_const_mul (hG (jIndex n d) a) (jSign d) (jIndex n b),
    rDeriv_const_mul (hG a b) (jSign b) d] at hk
  by_cases hb : b.2 = 0
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith

theorem rDeriv_realMetricFn_symm {n : ℕ} {M : ComplexManifold n} (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a b c : RIdx n) :
    rDeriv (fun w => realMetricFn h x w b c) z a =
      rDeriv (fun w => realMetricFn h x w c b) z a := by
  exact congrArg (fun F => rDeriv F z a) (funext fun w => realMetricFn_symm h x w b c)

theorem christoffel_metric_jIndex {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    jSign b * (∑ d, christoffel g.form x z d a (jIndex n b) * realMetricFn g.form x z d c) +
      jSign c * (∑ d, christoffel g.form x z d a b * realMetricFn g.form x z d (jIndex n c)) = 0 := by
  rw [christoffel_metric_contraction g x z hz a (jIndex n b) c,
    christoffel_metric_contraction g x z hz a b (jIndex n c)]
  have h1 := kahler_metric_derivative_identity_on g hK x hz a (jIndex n b) c
  have h2 := kahler_metric_derivative_identity_on g hK x hz a b (jIndex n c)
  simp only [jIndex_involutive, jSign_jIndex] at h1 h2
  rw [rDeriv_realMetricFn_symm g.form x z b (jIndex n c) a] at h1
  rw [rDeriv_realMetricFn_symm g.form x z (jIndex n b) c a] at h2
  rcases b with ⟨bi, b⟩
  rcases c with ⟨ci, c⟩
  fin_cases b <;> fin_cases c <;> norm_num [jSign] at h1 h2 ⊢ <;> linarith

theorem christoffel_jIndex {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    jSign b * christoffel g.form x z c a (jIndex n b) =
      jSign (jIndex n c) * christoffel g.form x z (jIndex n c) a b := by
  let G := realMetricFn g.form x z
  let W : RIdx n → ℝ := fun d => jSign b * christoffel g.form x z d a (jIndex n b) -
    jSign (jIndex n d) * christoffel g.form x z (jIndex n d) a b
  have hvec : G *ᵥ W = 0 := by
    funext k
    have hk := christoffel_metric_jIndex g hK x z hz a b k
    have hswap : jSign k * (∑ d, christoffel g.form x z d a b * G d (jIndex n k)) =
        -(∑ d, jSign (jIndex n d) * christoffel g.form x z (jIndex n d) a b * G d k) := by
      calc
        _ = jSign k * (∑ d, christoffel g.form x z (jIndex n d) a b *
            G (jIndex n d) (jIndex n k)) := by
          exact congrArg (fun t : ℝ => jSign k * t)
            ((jIndex n).sum_comp (fun d => christoffel g.form x z d a b * G d (jIndex n k))).symm
        _ = ∑ d, jSign d * christoffel g.form x z (jIndex n d) a b * G d k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          rw [show G (jIndex n d) (jIndex n k) = jSign d * jSign k * G d k from
            realMetricFn_jIndex g.form x z d k]
          calc
            _ = (jSign k * jSign k) * (jSign d * christoffel g.form x z (jIndex n d) a b * G d k) := by ring
            _ = _ := by rw [jSign_sq]; ring
        _ = _ := by simp only [jSign_jIndex, neg_mul, Finset.sum_neg_distrib, neg_neg]
    change jSign b * (∑ d, christoffel g.form x z d a (jIndex n b) * G d k) +
      jSign k * (∑ d, christoffel g.form x z d a b * G d (jIndex n k)) = 0 at hk
    rw [hswap] at hk
    change (∑ d, G k d * W d) = 0
    calc
      _ = jSign b * (∑ d, christoffel g.form x z d a (jIndex n b) * G d k) -
          (∑ d, jSign (jIndex n d) * christoffel g.form x z (jIndex n d) a b * G d k) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro d _
        rw [show G k d = G d k from realMetricFn_symm g.form x z k d]
        dsimp [W]
        ring
      _ = 0 := by linarith
  have hinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr (realMetricFn_posDef g.form x z hz).det_pos.ne')
  have hW : W = 0 := by
    calc
      W = G⁻¹ *ᵥ (G *ᵥ W) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      _ = 0 := by rw [hvec, Matrix.mulVec_zero]
  have hc := congrFun hW c
  change jSign b * christoffel g.form x z c a (jIndex n b) -
    jSign (jIndex n c) * christoffel g.form x z (jIndex n c) a b = 0 at hc
  exact sub_eq_zero.mp hc


def jMatrix (n : ℕ) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun c b => if b = jIndex n c then jSign b else 0

theorem jMatrix_mul (A : Matrix (RIdx n) (RIdx n) ℝ) (c b : RIdx n) :
    (jMatrix n * A) c b = jSign (jIndex n c) * A (jIndex n c) b := by
  simp [jMatrix, Matrix.mul_apply, ite_mul]

theorem mul_jMatrix (A : Matrix (RIdx n) (RIdx n) ℝ) (c b : RIdx n) :
    (A * jMatrix n) c b = jSign b * A c (jIndex n b) := by
  have hp (d : RIdx n) : (b = jIndex n d) ↔ d = jIndex n b := by
    constructor
    · intro h
      rw [h, jIndex_involutive]
    · intro h
      rw [h, jIndex_involutive]
  simp [jMatrix, Matrix.mul_apply, hp, mul_ite, mul_comm]

theorem jMatrix_sq (n : ℕ) : jMatrix n * jMatrix n = -1 := by
  ext c b
  rw [jMatrix_mul]
  by_cases h : b = c
  · subst b
    simp only [jMatrix, jIndex_involutive, ite_true, Matrix.neg_apply, Matrix.one_apply, ite_true]
    rw [jSign_jIndex]
    nlinarith [jSign_sq c]
  · simp [jMatrix, jIndex_involutive, h, Ne.symm h]

def connectionMatrix (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a : RIdx n) :
    Matrix (RIdx n) (RIdx n) ℝ := fun c b => christoffel h x z c a b

def connectionDerivativeMatrix (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (d a : RIdx n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun c b => rDeriv (fun w => christoffel h x w c a b) z d

def curvatureMatrix (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    Matrix (RIdx n) (RIdx n) ℝ := fun l c => riemannCoeff h x z a b c l

theorem connectionMatrix_commute_jMatrix (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    Commute (connectionMatrix g.form x z a) (jMatrix n) := by
  ext c b
  rw [mul_jMatrix, jMatrix_mul]
  exact christoffel_jIndex g hK x z hz a b c

theorem rDeriv_christoffel_jIndex (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (d a b c : RIdx n) :
    jSign b * rDeriv (fun w => christoffel g.form x w c a (jIndex n b)) z d =
      jSign (jIndex n c) * rDeriv (fun w => christoffel g.form x w (jIndex n c) a b) z d := by
  have hdiff (l i j : RIdx n) : DifferentiableAt ℝ (fun w => christoffel g.form x w l i j) z :=
    ((christoffel_contDiffOn g x l i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  rw [← rDeriv_const_mul (hdiff c a (jIndex n b)) (jSign b) d,
    ← rDeriv_const_mul (hdiff (jIndex n c) a b) (jSign (jIndex n c)) d]
  have heq : (fun w => jSign b * christoffel g.form x w c a (jIndex n b)) =ᶠ[𝓝 z]
      (fun w => jSign (jIndex n c) * christoffel g.form x w (jIndex n c) a b) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact christoffel_jIndex g hK x w hw a b c
  exact congrArg (fun L => L (realVec d)) (heq.fderiv_eq (𝕜 := ℝ))

theorem connectionDerivativeMatrix_commute_jMatrix (g : SmoothMetric M) (hK : IsKahler g)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (d a : RIdx n) :
    Commute (connectionDerivativeMatrix g.form x z d a) (jMatrix n) := by
  ext c b
  rw [mul_jMatrix, jMatrix_mul]
  exact rDeriv_christoffel_jIndex g hK x z hz d a b c

theorem curvatureMatrix_eq (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    curvatureMatrix h x z a b = connectionDerivativeMatrix h x z a b -
      connectionDerivativeMatrix h x z b a +
      connectionMatrix h x z a * connectionMatrix h x z b -
      connectionMatrix h x z b * connectionMatrix h x z a := by
  ext l c
  simp only [curvatureMatrix, riemannCoeff, connectionDerivativeMatrix, connectionMatrix,
    Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
  simp_rw [mul_comm (christoffel h x z _ b c), mul_comm (christoffel h x z _ a c)]
  ring

theorem curvatureMatrix_commute_jMatrix (g : SmoothMetric M) (hK : IsKahler g)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    Commute (curvatureMatrix g.form x z a b) (jMatrix n) := by
  rw [curvatureMatrix_eq]
  have hDa := (connectionDerivativeMatrix_commute_jMatrix g hK x z hz a b).symm
  have hDb := (connectionDerivativeMatrix_commute_jMatrix g hK x z hz b a).symm
  have hA := (connectionMatrix_commute_jMatrix g hK x z hz a).symm
  have hB := (connectionMatrix_commute_jMatrix g hK x z hz b).symm
  exact ((hDa.sub_right hDb).add_right (hA.mul_right hB) |>.sub_right (hB.mul_right hA)).symm

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

def matrixDirectionalDerivative (A : E → Matrix ι ι ℝ) (z v : E) : Matrix ι ι ℝ :=
  fun i j => fderiv ℝ (fun w => A w i j) z v

theorem matrixDirectionalDerivative_mul {A B : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (v : E) :
    matrixDirectionalDerivative (fun w => A w * B w) z v =
      matrixDirectionalDerivative A z v * B z + A z * matrixDirectionalDerivative B z v := by
  ext i j
  change fderiv ℝ (fun w => ∑ k, A w i k * B w k j) z v = _
  have hs := fderiv_fun_sum (u := Finset.univ)
    (A := fun k w => A w i k * B w k j) (fun k _ => (hA i k).mul (hB k j))
  rw [hs]
  simp only [ContinuousLinearMap.sum_apply, Matrix.add_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hp := congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_mul (hA i k) (hB k j))
  calc
    _ = A z i k * matrixDirectionalDerivative B z v k j +
        B z k j * matrixDirectionalDerivative A z v i k := by convert! hp using 1
    _ = _ := by ring

theorem matrixDirectionalDerivative_add {A B : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (v : E) :
    matrixDirectionalDerivative (fun w => A w + B w) z v =
      matrixDirectionalDerivative A z v + matrixDirectionalDerivative B z v := by
  ext i j
  change fderiv ℝ (fun w => A w i j + B w i j) z v = _
  convert! congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_add (hA i j) (hB i j)) using 1

theorem matrixDirectionalDerivative_sub {A B : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (v : E) :
    matrixDirectionalDerivative (fun w => A w - B w) z v =
      matrixDirectionalDerivative A z v - matrixDirectionalDerivative B z v := by
  ext i j
  change fderiv ℝ (fun w => A w i j - B w i j) z v = _
  convert! congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_sub (hA i j) (hB i j)) using 1

theorem matrixDirectionalDerivative_transpose (A : E → Matrix ι ι ℝ) (z v : E) :
    matrixDirectionalDerivative (fun w => (A w)ᵀ) z v = (matrixDirectionalDerivative A z v)ᵀ := rfl

theorem matrixDirectionalDerivative_congr {A B : E → Matrix ι ι ℝ} {z : E}
    (heq : A =ᶠ[𝓝 z] B) (v : E) :
    matrixDirectionalDerivative A z v = matrixDirectionalDerivative B z v := by
  ext i j
  have he : (fun w => A w i j) =ᶠ[𝓝 z] (fun w => B w i j) :=
    heq.mono (fun _ hw => congrFun (congrFun hw i) j)
  exact congrArg (fun L => L v) (he.fderiv_eq (𝕜 := ℝ))

theorem matrixDirectionalDerivative_comm {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, ContDiffAt ℝ 2 (fun w => A w i j) z) (u v : E) :
    matrixDirectionalDerivative (fun w => matrixDirectionalDerivative A w u) z v =
      matrixDirectionalDerivative (fun w => matrixDirectionalDerivative A w v) z u := by
  ext i j
  have hdf := ((hA i j).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change fderiv ℝ (fun w => fderiv ℝ (fun y => A y i j) w u) z v =
    fderiv ℝ (fun w => fderiv ℝ (fun y => A y i j) w v) z u
  rw [fderiv_clm_apply hdf (differentiableAt_const u),
    fderiv_clm_apply hdf (differentiableAt_const v)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    map_zero, add_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact (hA i j).isSymmSndFDerivAt (by norm_num) v u

theorem matrix_entries_differentiable_mul {A B : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (i j : ι) :
    DifferentiableAt ℝ (fun w => (A w * B w) i j) z := by
  apply DifferentiableAt.fun_sum
  intro k _
  exact (hA i k).mul (hB k j)

theorem metric_curvature_matrix_skew (G A B DA DB : Matrix ι ι ℝ)
    (hcurl : DAᵀ * G + Bᵀ * (Aᵀ * G + G * A) + (Aᵀ * G + G * A) * B + G * DA =
      DBᵀ * G + Aᵀ * (Bᵀ * G + G * B) + (Bᵀ * G + G * B) * A + G * DB) :
    (DA - DB + A * B - B * A)ᵀ * G + G * (DA - DB + A * B - B * A) = 0 := by
  calc
    _ = (DAᵀ * G + Bᵀ * (Aᵀ * G + G * A) + (Aᵀ * G + G * A) * B + G * DA) -
        (DBᵀ * G + Aᵀ * (Bᵀ * G + G * B) + (Bᵀ * G + G * B) * A + G * DB) := by
      simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul]
      noncomm_ring
    _ = 0 := sub_eq_zero.mpr hcurl

theorem matrix_curvature_skew_of_metricCompatibility {G A B : E → Matrix ι ι ℝ} {z : E}
    (hG : ∀ i j, ContDiffAt ℝ 2 (fun w => G w i j) z)
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (u v : E)
    (hu : ∀ᶠ w in 𝓝 z, matrixDirectionalDerivative G w u = (A w)ᵀ * G w + G w * A w)
    (hv : ∀ᶠ w in 𝓝 z, matrixDirectionalDerivative G w v = (B w)ᵀ * G w + G w * B w) :
    let R := matrixDirectionalDerivative B z u - matrixDirectionalDerivative A z v +
      A z * B z - B z * A z
    Rᵀ * G z + G z * R = 0 := by
  have hGd (i j : ι) := (hG i j).differentiableAt (by norm_num)
  have hAu := matrixDirectionalDerivative_congr hu v
  have hBv := matrixDirectionalDerivative_congr hv u
  have hAt (i j : ι) : DifferentiableAt ℝ (fun w => (A w)ᵀ i j) z := hA j i
  have hBt (i j : ι) : DifferentiableAt ℝ (fun w => (B w)ᵀ i j) z := hB j i
  rw [matrixDirectionalDerivative_add (matrix_entries_differentiable_mul hAt hGd)
      (matrix_entries_differentiable_mul hGd hA) v,
    matrixDirectionalDerivative_mul hAt hGd v, matrixDirectionalDerivative_mul hGd hA v,
    matrixDirectionalDerivative_transpose] at hAu
  rw [matrixDirectionalDerivative_add (matrix_entries_differentiable_mul hBt hGd)
      (matrix_entries_differentiable_mul hGd hB) u,
    matrixDirectionalDerivative_mul hBt hGd u, matrixDirectionalDerivative_mul hGd hB u,
    matrixDirectionalDerivative_transpose] at hBv
  rw [hv.self_of_nhds] at hAu
  rw [hu.self_of_nhds] at hBv
  have hcomm := matrixDirectionalDerivative_comm hG v u
  have hcurl := hBv.symm.trans (hcomm.trans hAu)
  apply metric_curvature_matrix_skew (G z) (A z) (B z)
    (matrixDirectionalDerivative B z u) (matrixDirectionalDerivative A z v)
  convert! hcurl using 1 <;> noncomm_ring

variable {n : ℕ} {M : ComplexManifold n}

theorem christoffel_symm_lower (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (c a b : RIdx n) : christoffel h x z c a b = christoffel h x z c b a := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [rDeriv_realMetricFn_symm h x z d a b]
  ring

theorem metricDirectionalDerivative_eq_connection (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    matrixDirectionalDerivative (fun w => realMetricFn g.form x w) z (realVec a) =
      (connectionMatrix g.form x z a)ᵀ * realMetricFn g.form x z +
        realMetricFn g.form x z * connectionMatrix g.form x z a := by
  ext b c
  change rDeriv (fun w => realMetricFn g.form x w b c) z a = _
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix]
  have hswap : (∑ d, realMetricFn g.form x z b d * christoffel g.form x z d a c) =
      ∑ d, christoffel g.form x z d a c * realMetricFn g.form x z d b := by
    apply Finset.sum_congr rfl
    intro d _
    rw [realMetricFn_symm g.form x z b d]
    ring
  rw [hswap, christoffel_metric_contraction g x z hz a b c,
    christoffel_metric_contraction g x z hz a c b,
    rDeriv_realMetricFn_symm g.form x z a c b]
  ring

theorem curvatureMatrix_metric_skew (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    (curvatureMatrix g.form x z a b)ᵀ * realMetricFn g.form x z +
      realMetricFn g.form x z * curvatureMatrix g.form x z a b = 0 := by
  have hG (i j : RIdx n) : ContDiffAt ℝ 2 (fun w => realMetricFn g.form x w i j) z :=
    ((metricSmooth_of_smoothMetric g x i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hC (k i j : RIdx n) : DifferentiableAt ℝ (fun w => connectionMatrix g.form x w k i j) z :=
    ((christoffel_contDiffOn g x i k j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have he (k : RIdx n) : ∀ᶠ w in 𝓝 z,
      matrixDirectionalDerivative (fun p => realMetricFn g.form x p) w (realVec k) =
        (connectionMatrix g.form x w k)ᵀ * realMetricFn g.form x w +
          realMetricFn g.form x w * connectionMatrix g.form x w k := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact metricDirectionalDerivative_eq_connection g x w hw k
  have hs := matrix_curvature_skew_of_metricCompatibility hG (hC a) (hC b)
    (realVec a) (realVec b) (he a) (he b)
  rw [curvatureMatrix_eq]
  exact hs

theorem rDeriv_christoffel_symm_lower (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (d c a b : RIdx n) :
    rDeriv (fun w => christoffel h x w c a b) z d =
      rDeriv (fun w => christoffel h x w c b a) z d := by
  exact congrArg (fun F => rDeriv F z d) (funext fun w => christoffel_symm_lower h x w c a b)

theorem riemannCoeff_firstBianchi (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a b c l : RIdx n) :
    riemannCoeff h x z a b c l + riemannCoeff h x z b c a l +
      riemannCoeff h x z c a b l = 0 := by
  unfold riemannCoeff
  rw [rDeriv_christoffel_symm_lower h x z b l c a,
    rDeriv_christoffel_symm_lower h x z c l b a,
    rDeriv_christoffel_symm_lower h x z a l c b]
  have hsum : (∑ m, (christoffel h x z m b c * christoffel h x z l a m -
      christoffel h x z m a c * christoffel h x z l b m)) +
    (∑ m, (christoffel h x z m c a * christoffel h x z l b m -
      christoffel h x z m b a * christoffel h x z l c m)) +
    (∑ m, (christoffel h x z m a b * christoffel h x z l c m -
      christoffel h x z m c b * christoffel h x z l a m)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro m _
    rw [christoffel_symm_lower h x z m c a, christoffel_symm_lower h x z m b a,
      christoffel_symm_lower h x z m c b]
    ring
  linarith

theorem riemannCoeff_swap (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a b c l : RIdx n) : riemannCoeff h x z a b c l = -riemannCoeff h x z b a c l := by
  unfold riemannCoeff
  simp only [Finset.sum_sub_distrib]
  ring

def curvature4 (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a b c d : RIdx n) : ℝ :=
  ∑ l, realMetricFn h x z l d * riemannCoeff h x z a b c l

theorem curvature4_swap_first (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a b c d : RIdx n) : curvature4 h x z a b c d = -curvature4 h x z b a c d := by
  simp only [curvature4, riemannCoeff_swap h x z a b c, mul_neg, Finset.sum_neg_distrib]

theorem curvature4_swap_last (g : SmoothMetric M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    curvature4 g.form x z a b c d = -curvature4 g.form x z a b d c := by
  have hs := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A c d)
    (curvatureMatrix_metric_skew g x z hz a b)
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    curvatureMatrix] at hs
  have heq : (∑ l, realMetricFn g.form x z c l * riemannCoeff g.form x z a b d l) =
      curvature4 g.form x z a b d c := by
    unfold curvature4
    apply Finset.sum_congr rfl
    intro l _
    rw [realMetricFn_symm g.form x z c l]
  have hfirst : (∑ l, riemannCoeff g.form x z a b c l * realMetricFn g.form x z l d) =
      curvature4 g.form x z a b c d := by simp only [curvature4, mul_comm]
  rw [heq, hfirst] at hs
  linarith

theorem curvature4_firstBianchi (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a b c d : RIdx n) :
    curvature4 h x z a b c d + curvature4 h x z b c a d + curvature4 h x z c a b d = 0 := by
  unfold curvature4
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l _
  rw [← mul_add, ← mul_add, riemannCoeff_firstBianchi, mul_zero]

theorem algebraic_curvature_pair_swap {κ : Type*} (R : κ → κ → κ → κ → ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hb : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (a b c d : κ) : R a b c d = R c d a b := by
  linarith [hfirst a c b d, hfirst a d b c, hfirst a d c b, hfirst b d c a,
    hlast a b c d, hlast a c b d, hlast a d b c, hlast b c a d, hlast b d a c,
    hlast c d a b, hb a b c d, hb a b d c, hb a c d b, hb b c d a]

theorem curvature4_pair_swap (g : SmoothMetric M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    curvature4 g.form x z a b c d = curvature4 g.form x z c d a b :=
  algebraic_curvature_pair_swap (curvature4 g.form x z)
    (curvature4_swap_first g.form x z) (curvature4_swap_last g x z hz)
    (curvature4_firstBianchi g.form x z) a b c d

theorem realCurvatureFrame_inner (g : SmoothMetric M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    (underlyingRealRiemannianMetric g.form).inner (chartInv x z)
      (realCurvatureFrame g x a b c (chartInv x z))
      (realCoordinateField x (realVec d) (chartInv x z)) = curvature4 g.form x z a b c d := by
  rw [realCurvatureFrame_eq_riemannCoeff g x z hz a b c,
    map_sum ((underlyingRealRiemannianMetric g.form).inner (chartInv x z)),
    ContinuousLinearMap.sum_apply]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  unfold curvature4
  apply Finset.sum_congr rfl
  intro l _
  have hm := realCoordinateMetric_inChart g.form x z hz l d
  change (underlyingRealRiemannianMetric g.form).inner (chartInv x z)
    (realCoordinateField x (realVec l) (chartInv x z))
    (realCoordinateField x (realVec d) (chartInv x z)) = _ at hm
  rw [hm, mul_comm]


theorem jMatrix_transpose (n : ℕ) : (jMatrix n)ᵀ = -jMatrix n := by
  ext c b
  have hp : c = jIndex n b ↔ b = jIndex n c := by
    constructor <;> intro h <;> rw [h, jIndex_involutive]
  by_cases h : b = jIndex n c
  · subst b
    simp [jMatrix, jIndex_involutive, jSign_jIndex]
  · simp [jMatrix, hp, h]

theorem jMatrix_transpose_mul (A : Matrix (RIdx n) (RIdx n) ℝ) (c b : RIdx n) :
    ((jMatrix n)ᵀ * A) c b = jSign c * A (jIndex n c) b := by
  rw [jMatrix_transpose, Matrix.neg_mul, Matrix.neg_apply, jMatrix_mul, jSign_jIndex]
  ring

theorem jMatrix_conjugation_apply (A : Matrix (RIdx n) (RIdx n) ℝ) (c d : RIdx n) :
    ((jMatrix n)ᵀ * A * jMatrix n) c d =
      jSign c * jSign d * A (jIndex n c) (jIndex n d) := by
  rw [mul_jMatrix, jMatrix_transpose_mul]
  ring

theorem jMatrix_metric_orthogonal (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (jMatrix n)ᵀ * realMetricFn h x z * jMatrix n = realMetricFn h x z := by
  ext c d
  rw [jMatrix_conjugation_apply, realMetricFn_jIndex]
  calc
    _ = (jSign c * jSign c) * (jSign d * jSign d) * realMetricFn h x z c d := by ring
    _ = _ := by rw [jSign_sq, jSign_sq]; ring

theorem curvature4_eq_matrix (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a b c d : RIdx n) :
    curvature4 h x z a b c d = ((curvatureMatrix h x z a b)ᵀ * realMetricFn h x z) c d := by
  simp only [curvature4, curvatureMatrix, Matrix.mul_apply, Matrix.transpose_apply, mul_comm]

theorem curvature4_jIndex_last (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    jSign c * jSign d * curvature4 g.form x z a b (jIndex n c) (jIndex n d) =
      curvature4 g.form x z a b c d := by
  let R := curvatureMatrix g.form x z a b
  let G := realMetricFn g.form x z
  have hR : Commute R (jMatrix n) := curvatureMatrix_commute_jMatrix g hK x z hz a b
  have hm : (jMatrix n)ᵀ * (Rᵀ * G) * jMatrix n = Rᵀ * G := by
    calc
      _ = (R * jMatrix n)ᵀ * G * jMatrix n := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (jMatrix n * R)ᵀ * G * jMatrix n := by rw [hR.eq]
      _ = Rᵀ * ((jMatrix n)ᵀ * G * jMatrix n) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Rᵀ * G := by rw [jMatrix_metric_orthogonal g.form x z]
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A c d) hm
  rw [jMatrix_conjugation_apply] at he
  simpa only [curvature4_eq_matrix] using he

theorem curvature4_jIndex_first (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    jSign a * jSign b * curvature4 g.form x z (jIndex n a) (jIndex n b) c d =
      curvature4 g.form x z a b c d := by
  rw [curvature4_pair_swap g x z hz (jIndex n a) (jIndex n b) c d,
    curvature4_pair_swap g x z hz a b c d]
  exact curvature4_jIndex_last g hK x z hz c d a b

theorem curvatureMatrix_jIndex_first (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    (jSign a * jSign b) • curvatureMatrix g.form x z (jIndex n a) (jIndex n b) =
      curvatureMatrix g.form x z a b := by
  let G := realMetricFn g.form x z
  have hlow : ((jSign a * jSign b) • (curvatureMatrix g.form x z (jIndex n a) (jIndex n b))ᵀ) * G =
      (curvatureMatrix g.form x z a b)ᵀ * G := by
    ext c d
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    simpa only [curvature4_eq_matrix, G] using curvature4_jIndex_first g hK x z hz a b c d
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A * G⁻¹) hlow
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G
    (isUnit_iff_ne_zero.mpr (realMetricFn_posDef g.form x z hz).det_pos.ne')
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hGG, Matrix.mul_one, Matrix.mul_one] at he
  have ht := congrArg Matrix.transpose he
  simpa only [Matrix.transpose_smul, Matrix.transpose_transpose] using ht

theorem riemannCoeff_jIndex_first (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c l : RIdx n) :
    riemannCoeff g.form x z (jIndex n a) (jIndex n b) c l =
      jSign a * jSign b * riemannCoeff g.form x z a b c l := by
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A l c)
    (curvatureMatrix_jIndex_first g hK x z hz a b)
  change (jSign a * jSign b) * riemannCoeff g.form x z (jIndex n a) (jIndex n b) c l =
    riemannCoeff g.form x z a b c l at he
  calc
    _ = (jSign a * jSign a) * (jSign b * jSign b) *
      riemannCoeff g.form x z (jIndex n a) (jIndex n b) c l := by rw [jSign_sq, jSign_sq]; ring
    _ = (jSign a * jSign b) * ((jSign a * jSign b) *
      riemannCoeff g.form x z (jIndex n a) (jIndex n b) c l) := by ring
    _ = _ := by rw [he]

theorem riemannCoeff_jIndex_last (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c l : RIdx n) :
    riemannCoeff g.form x z a b (jIndex n c) (jIndex n l) =
      jSign l * jSign c * riemannCoeff g.form x z a b c l := by
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A (jIndex n l) c)
    (curvatureMatrix_commute_jMatrix g hK x z hz a b).eq
  rw [mul_jMatrix, jMatrix_mul, jIndex_involutive] at he
  change jSign c * riemannCoeff g.form x z a b (jIndex n c) (jIndex n l) =
    jSign l * riemannCoeff g.form x z a b c l at he
  calc
    _ = (jSign c * jSign c) * riemannCoeff g.form x z a b (jIndex n c) (jIndex n l) := by rw [jSign_sq]; ring
    _ = jSign c * (jSign c * riemannCoeff g.form x z a b (jIndex n c) (jIndex n l)) := by ring
    _ = _ := by rw [he]; ring

theorem matrix_trace_zero_of_metric_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G R : Matrix ι ι ℝ) (hG : IsUnit G.det) (hs : Rᵀ * G + G * R = 0) : R.trace = 0 := by
  have he := congrArg (fun A : Matrix ι ι ℝ => A * G⁻¹) hs
  rw [add_mul, Matrix.mul_assoc Rᵀ G G⁻¹, Matrix.mul_nonsing_inv G hG,
    Matrix.mul_one, Matrix.zero_mul] at he
  have hc : Matrix.trace (G * R * G⁻¹) = R.trace := by
    rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul G hG, Matrix.one_mul]
  have ht := congrArg Matrix.trace he
  rw [Matrix.trace_add, Matrix.trace_transpose, hc, Matrix.trace_zero] at ht
  linarith

theorem curvatureMatrix_trace_zero (g : SmoothMetric M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a b : RIdx n) : (curvatureMatrix g.form x z a b).trace = 0 :=
  matrix_trace_zero_of_metric_skew (realMetricFn g.form x z) (curvatureMatrix g.form x z a b)
    (isUnit_iff_ne_zero.mpr (realMetricFn_posDef g.form x z hz).det_pos.ne')
    (curvatureMatrix_metric_skew g x z hz a b)

def realRicciMatrix (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ := fun b c => ∑ a, riemannCoeff h x z a b c a

theorem realRicciMatrix_symm (g : SmoothMetric M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (b c : RIdx n) :
    realRicciMatrix g.form x z b c = realRicciMatrix g.form x z c b := by
  have hsum : realRicciMatrix g.form x z b c + (curvatureMatrix g.form x z b c).trace -
      realRicciMatrix g.form x z c b = 0 := by
    simp only [realRicciMatrix, Matrix.trace, Matrix.diag_apply, curvatureMatrix]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro a _
    have hb := riemannCoeff_firstBianchi g.form x z a b c a
    rw [riemannCoeff_swap g.form x z c a b a] at hb
    linarith
  rw [curvatureMatrix_trace_zero g x z hz b c] at hsum
  linarith

theorem realRicciMatrix_eq_jTrace (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (b c : RIdx n) :
    jSign c * Matrix.trace (jMatrix n * curvatureMatrix g.form x z b (jIndex n c)) =
      2 * realRicciMatrix g.form x z b c := by
  let S1 := ∑ a, jSign c * jSign (jIndex n a) *
    riemannCoeff g.form x z (jIndex n c) a b (jIndex n a)
  let S2 := ∑ a, jSign c * jSign (jIndex n a) *
    riemannCoeff g.form x z a b (jIndex n c) (jIndex n a)
  have hsum : jSign c * Matrix.trace (jMatrix n * curvatureMatrix g.form x z b (jIndex n c)) +
      S1 + S2 = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, jMatrix_mul, curvatureMatrix, S1, S2,
      Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    have hb := riemannCoeff_firstBianchi g.form x z b (jIndex n c) a (jIndex n a)
    calc
      _ = (jSign c * jSign (jIndex n a)) *
        (riemannCoeff g.form x z b (jIndex n c) a (jIndex n a) +
          riemannCoeff g.form x z (jIndex n c) a b (jIndex n a) +
          riemannCoeff g.form x z a b (jIndex n c) (jIndex n a)) := by ring
      _ = 0 := by rw [hb, mul_zero]
  have hS2 : S2 = -realRicciMatrix g.form x z b c := by
    dsimp [S2, realRicciMatrix]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [riemannCoeff_jIndex_last g hK x z hz a b c a, jSign_jIndex]
    calc
      _ = -(jSign c * jSign c) * (jSign a * jSign a) * riemannCoeff g.form x z a b c a := by ring
      _ = _ := by rw [jSign_sq, jSign_sq]; ring
  have hS1 : S1 = -realRicciMatrix g.form x z c b := by
    calc
      S1 = ∑ a, jSign c * jSign (jIndex n (jIndex n a)) *
          riemannCoeff g.form x z (jIndex n c) (jIndex n a) b (jIndex n (jIndex n a)) :=
        ((jIndex n).sum_comp (fun a => jSign c * jSign (jIndex n a) *
          riemannCoeff g.form x z (jIndex n c) a b (jIndex n a))).symm
      _ = _ := by
        simp only [jIndex_involutive, realRicciMatrix]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [riemannCoeff_swap g.form x z (jIndex n c) (jIndex n a) b a,
          riemannCoeff_jIndex_first g hK x z hz a c b a]
        calc
          _ = -(jSign c * jSign c) * (jSign a * jSign a) * riemannCoeff g.form x z a c b a := by ring
          _ = _ := by rw [jSign_sq, jSign_sq]; ring
  rw [hS1, hS2, realRicciMatrix_symm g x z hz c b] at hsum
  linarith


open scoped ComplexOrder
/- The determinant/logarithm subgraph below is copied from immutable
/tmp/yau-l18-44.lean, SHA256
dddb59386cd1d770fd51350b396d5f1c212aeafe91ef78dfdd0d25f1168fc568.
Original/new names are stated individually.  realBasis_repr is replaced by
realVec_basis_repr, proved from this file's realVec_basis reconstruction;
the realification determinant proofs use this same genuine real basis.
No L09 or L18 import is introduced. -/

-- Source: L18Aux.chartVec_sum → L12Aux.chartVec_sum
theorem chartVec_sum {n : ℕ} {M : ComplexManifold n} {ι : Type*}
    (x y : M.Carrier) (s : Finset ι) (v : ι → ComplexVector n) :
    chartVec x y (∑ i ∈ s, v i) = ∑ i ∈ s, chartVec x y (v i) := by
  exact map_sum (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x).symm (chartPt x y)) v s

-- Source: L18Aux.hMat_isHermitian → L12Aux.hMat_isHermitian
theorem hMat_isHermitian {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (hMat h x z).IsHermitian := by
  ext i j
  exact ((h (chartInv x z)).conjugate_symmetric _ _).symm

-- Source: L18Aux.hermitian_sum_left → L12Aux.hermitian_sum_left
theorem hermitian_sum_left {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s : Finset ι) (u : ι → V) (v : V) :
    h.toFun (∑ i ∈ s, u i) v = ∑ i ∈ s, h.toFun (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_smul_left (0 : ℂ) (0 : V) v
  | @insert a s ha ih => simp [Finset.sum_insert ha, h.map_add_left, ih]

-- Source: L18Aux.hermitian_sum_right → L12Aux.hermitian_sum_right
theorem hermitian_sum_right {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s : Finset ι) (u : V) (v : ι → V) :
    h.toFun u (∑ i ∈ s, v i) = ∑ i ∈ s, h.toFun u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_smul_right (0 : ℂ) u (0 : V)
  | @insert a s ha ih => simp [Finset.sum_insert ha, h.map_add_right, ih]

-- Source: L18Aux.hMat_quadratic → L12Aux.hMat_quadratic
theorem hMat_quadratic {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (u : Fin n → ℂ) :
    star u ⬝ᵥ ((hMat h x z) *ᵥ u) =
      (h (chartInv x z)).toFun
        (∑ i, u i • chartVec x (chartInv x z) (stdVec i))
        (∑ i, u i • chartVec x (chartInv x z) (stdVec i)) := by
  rw [hermitian_sum_left]
  simp only [hermitian_sum_right,
    HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, hMat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

-- Source: L18Aux.chartVec_injective → L12Aux.chartVec_injective
theorem chartVec_injective {n : ℕ} {M : ComplexManifold n}
    (x y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    Function.Injective (chartVec x y) := by
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
    (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  have hleft : Function.LeftInverse (tangentCoords x y) (chartVec x y) := by
    intro v
    have hv := congrArg (fun L => L v) hcomp
    change tangentCoords x y (chartVec x y v) = v at hv
    exact hv
  exact hleft.injective

-- Source: L18Aux.hMat_posDef → L12Aux.hMat_posDef
theorem hMat_posDef {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) : (hMat h x z).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hMat_isHermitian h x z)
  intro u hu
  rw [hMat_quadratic]
  apply Complex.pos_iff.mpr
  refine ⟨hermitianNormSq_pos (h (chartInv x z)) ?_,
    ((h (chartInv x z)).self_adjoint _).symm⟩
  intro hzero
  have hsum : ∑ i, u i • stdVec i = (WithLp.toLp 2 u : ComplexVector n) := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have heq : ∑ i, u i • chartVec x (chartInv x z) (stdVec i) =
      chartVec x (chartInv x z) (WithLp.toLp 2 u) := by
    rw [← hsum, chartVec_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (chartVec_complex_smul _ _ _ _).symm
  rw [heq] at hzero
  have hzsource := (extChartAt (ComplexModel n) x).map_target hz
  have hzero' : chartVec x (chartInv x z) (WithLp.toLp 2 u) =
      chartVec x (chartInv x z) 0 := by
    have hzv : chartVec x (chartInv x z) 0 = 0 := by
      simpa using chartVec_complex_smul x (chartInv x z) 0 0
    simpa only [hzv] using hzero
  have hu0 := chartVec_injective x (chartInv x z) hzsource hzero'
  apply hu
  ext i
  simpa using congrArg (fun v : ComplexVector n => v i) hu0

-- Source: L18Aux.hMat_det_re_pos → L12Aux.hMat_det_re_pos
theorem hMat_det_re_pos {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) : 0 < (hMat h x z).det.re :=
  (Complex.pos_iff.mp (hMat_posDef h x z hz).det_pos).1

-- Source: L18Aux.logDet_contDiffOn → L12Aux.logDet_contDiffOn
theorem logDet_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (logDet g.form x) (chartTarget x) := by
  have hd : ContDiffOn ℝ ∞ (fun z => (hMat g.form x z).det.re) (chartTarget x) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (contDiffOn_matrix_det (hMat_contDiffOn g x))
  exact hd.log fun z hz => ne_of_gt (hMat_det_re_pos g.form x hz)

-- Source: L18Aux.realBasis_repr → L12Aux.realVec_basis_repr
theorem realVec_basis_repr {n : ℕ} (v : ComplexVector n) (a : RIdx n) :
    (realVec_basis n).repr v a = realCoord v a := by
  have hs : (∑ b, (realVec_basis n).repr v b • realVec b) = v := by
    simpa only [realVec_basis_apply] using (realVec_basis n).sum_repr v
  have hc := congrArg (fun w => realCoord w a) hs
  rw [realCoord_sum_realVec] at hc
  exact hc

-- Source: L18Aux.complexMatrix_toLin_apply → L12Aux.complexMatrix_toLin_apply
theorem complexMatrix_toLin_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (v : ComplexVector n) (i : Fin n) :
    (Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis H v) i =
      ∑ j, H i j * v j := by
  rw [Matrix.toLin_apply]
  simp [EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, EuclideanSpace.single, Pi.single_apply,
    Matrix.mulVec, dotProduct]

-- Source: L18Aux.real_toMatrix_complex_toLin → L12Aux.real_toMatrix_complex_toLin
theorem real_toMatrix_complex_toLin {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : RIdx n) :
    LinearMap.toMatrix (realVec_basis n)
      (realVec_basis n)
      ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis H).restrictScalars ℝ) a b =
      if a.2 = b.2 then (H a.1 b.1).re
        else if a.2 = 0 then -(H a.1 b.1).im else (H a.1 b.1).im := by
  rw [LinearMap.toMatrix_apply]
  simp only [LinearMap.restrictScalars_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, realVec_basis_apply, realVec_basis_repr]
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realCoord, complexMatrix_toLin_apply, realVec, EuclideanSpace.single,
      Pi.single_apply, Complex.mul_re, Complex.mul_im]

-- Source: L18Aux.realMetricFn_eq_toMatrix → L12Aux.realMetricFn_eq_toMatrix
theorem realMetricFn_eq_toMatrix {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    realMetricFn h x z = (2 : ℝ) •
      LinearMap.toMatrix (realVec_basis n)
        (realVec_basis n)
        ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (hMat h x z)).restrictScalars ℝ) := by
  ext a b
  simp only [realMetricFn_entries, Matrix.smul_apply, smul_eq_mul,
    real_toMatrix_complex_toLin]

-- Source: L18Aux.realMetricFn_det → L12Aux.realMetricFn_det
theorem realMetricFn_det {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    (realMetricFn h x z).det = ((2 : ℝ) ^ n * (hMat h x z).det.re) ^ 2 := by
  rw [realMetricFn_eq_toMatrix, Matrix.det_smul, LinearMap.det_toMatrix,
    LinearMap.det_restrictScalars, LinearMap.det_toLin, Algebra.norm_complex_apply]
  have him : (hMat h x z).det.im = 0 :=
    (Complex.pos_iff.mp (hMat_posDef h x z hz).det_pos).2.symm
  simp only [RIdx, Fintype.card_prod, Fintype.card_fin, Complex.normSq_apply, him,
    mul_zero, add_zero, pow_mul]
  ring

-- Source: L18Aux.paperVolumeNormalization → L12Aux.paperVolumeNormalization
theorem paperVolumeNormalization {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) : PaperVolumeNormalization h := by
  intro x z hz
  rw [realMetricFn_det h x hz, Real.sqrt_sq]
  exact mul_nonneg (by positivity) (hMat_det_re_pos h x hz).le

-- Source: L18Aux.realMetricFn_isSymm → L12Aux.realMetricFn_isSymm
theorem realMetricFn_isSymm {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (realMetricFn h x z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  unfold realMetricFn
  rw [(h (chartInv x z)).conjugate_symmetric]
  simp

-- Source: L18Aux.fderiv_matrix_det_sum_updateRow → L12Aux.fderiv_matrix_det_sum_updateRow
theorem fderiv_matrix_det_sum_updateRow
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z) (v : E) :
    fderiv ℝ (fun w => (A w).det) z v =
      ∑ i, ((A z).updateRow i (fderiv ℝ (fun w => A w i) z v)).det := by
  let detAlt : (ι → ℝ) [⋀^ι]→L[ℝ] ℝ :=
    { Matrix.detRowAlternating with cont := continuous_id.matrix_det }
  have hrow (i : ι) : DifferentiableAt ℝ (fun w => A w i) z :=
    differentiableAt_pi.mpr (hA i)
  have h := fderiv_continuousAlternatingMap_apply_apply
    (f := fun _ : E => detAlt) (g := fun i w => A w i)
    (differentiableAt_const detAlt) hrow v
  have hfun : (fun w : E => detAlt (fun i => A w i)) = (fun w => (A w).det) := by rfl
  have hupdate (i : ι) :
      detAlt (Function.update (fun j => A z j) i (fderiv ℝ (fun w => A w i) z v)) =
        ((A z).updateRow i (fderiv ℝ (fun w => A w i) z v)).det := by rfl
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply,
    ContinuousAlternatingMap.coe_zero, zero_add] at h
  rw [hfun] at h
  simpa only [hupdate] using h

-- Source: L18Aux.det_updateRow_eq_det_mul_inverse_coordinate → L12Aux.det_updateRow_eq_det_mul_inverse_coordinate
theorem det_updateRow_eq_det_mul_inverse_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) (i : ι) (row : ι → ℝ) :
    (A.updateRow i row).det = A.det * (row ᵥ* A⁻¹) i := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hc : (row ᵥ* A⁻¹) ᵥ* A = row := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hunit, Matrix.vecMul_one]
  have hrow : (∑ k, (row ᵥ* A⁻¹) k • A k) = row := by
    ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] using
      congrFun hc j
  nth_rw 1 [← hrow]
  rw [Matrix.det_updateRow_sum]
  simp only [smul_eq_mul, mul_comm]

-- Source: L18Aux.fderiv_matrix_det_trace → L12Aux.fderiv_matrix_det_trace
theorem fderiv_matrix_det_trace
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (v : E) :
    fderiv ℝ (fun w => (A w).det) z v = (A z).det *
      Matrix.trace ((A z)⁻¹ * (Matrix.of fun i j => fderiv ℝ (fun w => A w i) z v j)) := by
  rw [fderiv_matrix_det_sum_updateRow hA]
  simp_rw [det_updateRow_eq_det_mul_inverse_coordinate (A z) hdet]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Matrix.vecMul, dotProduct, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

-- Source: L18Aux.christoffel_trace → L12Aux.christoffel_trace
theorem christoffel_trace {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a : RIdx n) :
    (∑ b, christoffel h x z b a b) = (1 / 2 : ℝ) *
      Matrix.trace ((realMetricFn h x z)⁻¹ *
        (Matrix.of fun p q => rDeriv (fun w => realMetricFn h x w p q) z a)) := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn h x z)⁻¹
  let D : RIdx n → Matrix (RIdx n) (RIdx n) ℝ := fun c =>
    Matrix.of fun p q => rDeriv (fun w => realMetricFn h x w p q) z c
  have hA (p q : RIdx n) : A p q = A q p :=
    (realMetricFn_isSymm h x z).inv.apply q p
  have hD (c p q : RIdx n) : D c p q = D c q p :=
    rDeriv_realMetricFn_symm h x z c p q
  have hswap : (∑ b, ∑ d, A b d * D b a d) = ∑ b, ∑ d, A b d * D d a b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    rw [hA d b]
  have htrace : (∑ b, ∑ d, A b d * D a b d) = Matrix.trace (A * D a) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    rw [hD a b d]
  change (∑ b, (1 / 2 : ℝ) * ∑ d, A b d * (D a b d + D b a d - D d a b)) = _
  rw [← Finset.mul_sum]
  congr 1
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hswap, htrace]
  ring

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

theorem matrixDirectionalDerivative_const (A : Matrix ι ι ℝ) (z v : E) :
    matrixDirectionalDerivative (fun _ : E => A) z v = 0 := by
  ext i j
  simp [matrixDirectionalDerivative]

theorem matrixDirectionalDerivative_const_mul (A : Matrix ι ι ℝ) {B : E → Matrix ι ι ℝ}
    {z : E} (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (v : E) :
    matrixDirectionalDerivative (fun w => A * B w) z v = A * matrixDirectionalDerivative B z v := by
  rw [matrixDirectionalDerivative_mul (A := fun _ : E => A)
    (fun i j => differentiableAt_const (A i j)) hB v,
    matrixDirectionalDerivative_const, Matrix.zero_mul, zero_add]

theorem matrixDirectionalDerivative_trace {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z) (v : E) :
    fderiv ℝ (fun w => Matrix.trace (A w)) z v = Matrix.trace (matrixDirectionalDerivative A z v) := by
  have hs := fderiv_fun_sum (u := Finset.univ) (A := fun i w => A w i i)
    (fun i _ => hA i i)
  convert! congrArg (fun L : E →L[ℝ] ℝ => L v) hs using 1
  simp only [ContinuousLinearMap.sum_apply]
  rfl

variable {n : ℕ} {M : ComplexManifold n}

theorem connectionMatrix_jIndex_direction (g : SmoothMetric M) (hK : IsKahler g)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (b : RIdx n) :
    jSign b • connectionMatrix g.form x z (jIndex n b) = jMatrix n * connectionMatrix g.form x z b := by
  ext c d
  rw [jMatrix_mul]
  change jSign b * christoffel g.form x z c (jIndex n b) d =
    jSign (jIndex n c) * christoffel g.form x z (jIndex n c) b d
  rw [christoffel_symm_lower g.form x z c (jIndex n b) d,
    christoffel_jIndex g hK x z hz d b c,
    christoffel_symm_lower g.form x z (jIndex n c) d b]

def connectionTrace (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (b : RIdx n) : ℝ :=
  Matrix.trace (connectionMatrix h x z b)

theorem connectionTrace_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => connectionTrace g.form x z b) (chartTarget x) := by
  apply ContDiffOn.sum
  intro i _
  exact christoffel_contDiffOn g x i b i

theorem trace_jMatrix_connectionDerivative (g : SmoothMetric M) (hK : IsKahler g)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    Matrix.trace (jMatrix n * connectionDerivativeMatrix g.form x z a b) =
      jSign b * rDeriv (fun w => connectionTrace g.form x w (jIndex n b)) z a := by
  have hC (i j : RIdx n) : DifferentiableAt ℝ (fun w => connectionMatrix g.form x w b i j) z :=
    ((christoffel_contDiffOn g x i b j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hprod := matrix_entries_differentiable_mul (A := fun _ : ComplexVector n => jMatrix n)
    (fun i j => differentiableAt_const (jMatrix n i j)) hC
  have ht := matrixDirectionalDerivative_trace hprod (realVec a)
  rw [matrixDirectionalDerivative_const_mul (jMatrix n) hC] at ht
  have heq : (fun w => Matrix.trace (jMatrix n * connectionMatrix g.form x w b)) =ᶠ[𝓝 z]
      (fun w => jSign b * connectionTrace g.form x w (jIndex n b)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    have he := congrArg Matrix.trace (connectionMatrix_jIndex_direction g hK x w hw b)
    rw [Matrix.trace_smul, smul_eq_mul] at he
    exact he.symm
  have hd := congrArg (fun L => L (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))
  have hT := ((connectionTrace_contDiffOn g x (jIndex n b)).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  calc
    _ = fderiv ℝ (fun w => Matrix.trace (jMatrix n * connectionMatrix g.form x w b)) z (realVec a) := ht.symm
    _ = _ := hd
    _ = _ := rDeriv_const_mul hT (jSign b) a

theorem curvatureMatrix_jTrace_eq (g : SmoothMetric M) (hK : IsKahler g)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    Matrix.trace (jMatrix n * curvatureMatrix g.form x z a b) =
      jSign b * rDeriv (fun w => connectionTrace g.form x w (jIndex n b)) z a -
      jSign a * rDeriv (fun w => connectionTrace g.form x w (jIndex n a)) z b := by
  let A := connectionMatrix g.form x z a
  let B := connectionMatrix g.form x z b
  have hcomm : Matrix.trace (jMatrix n * (A * B)) = Matrix.trace (jMatrix n * (B * A)) := by
    calc
      _ = Matrix.trace (A * (jMatrix n * B)) := by
        rw [← Matrix.mul_assoc, ← (connectionMatrix_commute_jMatrix g hK x z hz a).eq,
          Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [curvatureMatrix_eq, mul_sub, mul_add, mul_sub, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_sub, trace_jMatrix_connectionDerivative g hK x z hz a b,
    trace_jMatrix_connectionDerivative g hK x z hz b a]
  change (_ - _ + Matrix.trace (jMatrix n * (A * B))) - Matrix.trace (jMatrix n * (B * A)) = _
  rw [hcomm]
  ring

theorem realRicciMatrix_eq_connectionTrace (g : SmoothMetric M) (hK : IsKahler g)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (b c : RIdx n) :
    2 * realRicciMatrix g.form x z b c =
      -rDeriv (fun w => connectionTrace g.form x w c) z b -
        jSign b * jSign c * rDeriv (fun w => connectionTrace g.form x w (jIndex n b)) z (jIndex n c) := by
  have he := realRicciMatrix_eq_jTrace g hK x z hz b c
  rw [curvatureMatrix_jTrace_eq g hK x z hz b (jIndex n c),
    jIndex_involutive, jSign_jIndex] at he
  calc
    _ = jSign c * ((-jSign c) * rDeriv (fun w => connectionTrace g.form x w c) z b -
        jSign b * rDeriv (fun w => connectionTrace g.form x w (jIndex n b)) z (jIndex n c)) := he.symm
    _ = -(jSign c * jSign c) * rDeriv (fun w => connectionTrace g.form x w c) z b -
        jSign b * jSign c * rDeriv (fun w => connectionTrace g.form x w (jIndex n b)) z (jIndex n c) := by ring
    _ = _ := by rw [jSign_sq]; ring


/- The six elementary scalar/Wirtinger calculus helpers marked below are
transcribed from immutable /tmp/yau-l18-44.lean, SHA256
dddb59386cd1d770fd51350b396d5f1c212aeafe91ef78dfdd0d25f1168fc568.
The remaining results below derive the actual Levi--Civita Ricci trace from
connectionTrace and identify it with the original complex Ricci calculator.
-/

theorem log_realMetricFn_det (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) :
    Real.log (realMetricFn h x z).det = 2 * logDet h x z + 2 * (n : ℝ) * Real.log 2 := by
  rw [realMetricFn_det h x hz, Real.log_pow,
    Real.log_mul (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))
      (hMat_det_re_pos h x hz).ne', Real.log_pow]
  unfold logDet
  ring

theorem rDeriv_log_realMetricFn_det (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    rDeriv (fun w => Real.log (realMetricFn g.form x w).det) z a =
      2 * rDeriv (logDet g.form x) z a := by
  have heq : (fun w => Real.log (realMetricFn g.form x w).det) =ᶠ[𝓝 z]
      (fun w => 2 * logDet g.form x w + 2 * (n : ℝ) * Real.log 2) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact log_realMetricFn_det g.form x w hw
  have hH : DifferentiableAt ℝ (logDet g.form x) z :=
    ((logDet_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have he := congrArg (fun L => L (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_add_const, fderiv_const_mul hH 2] at he
  exact he

-- Source: L18Aux.fderiv_matrix_row_apply → L12Aux.fderiv_matrix_row_apply
theorem fderiv_matrix_row_apply {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z) (v : E) (i j : ι) :
    fderiv ℝ (fun w => A w i) z v j = fderiv ℝ (fun w => A w i j) z v := by
  have hrow : DifferentiableAt ℝ (fun w => A w i) z := differentiableAt_pi.mpr (hA i)
  rw [fderiv_apply hrow j]
  simp

theorem rDeriv_log_realMetricFn_det_trace (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    rDeriv (fun w => Real.log (realMetricFn g.form x w).det) z a =
      Matrix.trace ((realMetricFn g.form x z)⁻¹ *
        matrixDirectionalDerivative (fun w => realMetricFn g.form x w) z (realVec a)) := by
  have hG (i j : RIdx n) := realMetricFn_differentiableAt g x hz i j
  have hdetd : DifferentiableAt ℝ (fun w => (realMetricFn g.form x w).det) z :=
    ((contDiffOn_matrix_det (metricSmooth_of_smoothMetric g x)).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (realMetricFn g.form x z).det ≠ 0 := (realMetricFn_posDef g.form x z hz).det_pos.ne'
  have hj := fderiv_matrix_det_trace hG hdet (realVec a)
  simp_rw [fderiv_matrix_row_apply hG] at hj
  unfold rDeriv
  rw [fderiv.log hdetd hdet]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hj]
  change (realMetricFn g.form x z).det⁻¹ *
    ((realMetricFn g.form x z).det * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
  rfl

theorem connectionTrace_eq_logDet (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    connectionTrace g.form x z a = rDeriv (logDet g.form x) z a := by
  have ht := christoffel_trace g.form x z a
  change connectionTrace g.form x z a = (1 / 2 : ℝ) *
    Matrix.trace ((realMetricFn g.form x z)⁻¹ *
      matrixDirectionalDerivative (fun w => realMetricFn g.form x w) z (realVec a)) at ht
  have hlog := rDeriv_log_realMetricFn_det_trace g x z hz a
  rw [rDeriv_log_realMetricFn_det g x z hz a] at hlog
  linarith

theorem rDeriv_connectionTrace_eq_logDet (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    rDeriv (fun w => connectionTrace g.form x w b) z a =
      rDeriv (fun w => rDeriv (logDet g.form x) w b) z a := by
  have heq : (fun w => connectionTrace g.form x w b) =ᶠ[𝓝 z]
      (fun w => rDeriv (logDet g.form x) w b) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact connectionTrace_eq_logDet g x w hw b
  exact congrArg (fun L => L (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))

theorem realRicciMatrix_eq_logDet (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (b c : RIdx n) :
    2 * realRicciMatrix g.form x z b c =
      -rDeriv (fun w => rDeriv (logDet g.form x) w c) z b -
      jSign b * jSign c * rDeriv
        (fun w => rDeriv (logDet g.form x) w (jIndex n b)) z (jIndex n c) := by
  rw [realRicciMatrix_eq_connectionTrace g hK x z hz b c,
    rDeriv_connectionTrace_eq_logDet g x z hz b c,
    rDeriv_connectionTrace_eq_logDet g x z hz (jIndex n c) (jIndex n b)]

-- Source: L18Aux.fderiv_wirtBar → L12Aux.fderiv_wirtBar
theorem fderiv_wirtBar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} {z : E}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) z) (v w : E) :
    fderiv ℝ (fun y => wirtBar F y v) z w =
      (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ F) z w v +
        Complex.I * fderiv ℝ (fderiv ℝ F) z w (Complex.I • v)) := by
  have hv : DifferentiableAt ℝ (fun y => fderiv ℝ F y v) z :=
    hF.clm_apply (differentiableAt_const v)
  have hIv : DifferentiableAt ℝ (fun y => fderiv ℝ F y (Complex.I • v)) z :=
    hF.clm_apply (differentiableAt_const (Complex.I • v))
  simp only [wirtBar]
  rw [fderiv_const_mul (hv.fun_add (hIv.const_mul Complex.I)),
    fderiv_fun_add hv (hIv.const_mul Complex.I), fderiv_const_mul hIv,
    fderiv_clm_apply hF (differentiableAt_const v),
    fderiv_clm_apply hF (differentiableAt_const (Complex.I • v))]
  simp
  ring

-- Source: L18Aux.wirt_wirtBar_eq_secondFDeriv → L12Aux.wirt_wirtBar_eq_secondFDeriv
theorem wirt_wirtBar_eq_secondFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} {z : E}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) z) (v w : E) :
    wirt (fun y => wirtBar F y v) z w =
      (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ F) z w v +
        fderiv ℝ (fderiv ℝ F) z (Complex.I • w) (Complex.I • v) +
        Complex.I * (fderiv ℝ (fderiv ℝ F) z w (Complex.I • v) -
          fderiv ℝ (fderiv ℝ F) z (Complex.I • w) v)) := by
  rw [wirt, fderiv_wirtBar hF, fderiv_wirtBar hF]
  linear_combination -(1 / 4 : ℂ) *
    fderiv ℝ (fderiv ℝ F) z (Complex.I • w) (Complex.I • v) * Complex.I_sq

-- Source: L18Aux.secondFDeriv_ofReal → L12Aux.secondFDeriv_ofReal
theorem secondFDeriv_ofReal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => (f y : ℂ))) z w v =
      (fderiv ℝ (fderiv ℝ f) z w v : ℂ) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF : DifferentiableAt ℝ (fderiv ℝ (fun y => (f y : ℂ))) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun y => (f y : ℂ)) y v) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ f y v : ℂ)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    have hd := hy.differentiableAt (by norm_num)
    change fderiv ℝ (Complex.ofRealCLM ∘ f) y v = _
    rw [fderiv_comp y Complex.ofRealCLM.differentiableAt hd]
    simp
  have h := congrArg (fun L : E →L[ℝ] ℂ => L w) heq.fderiv_eq
  rw [fderiv_clm_apply hdF (differentiableAt_const v)] at h
  change _ = fderiv ℝ (Complex.ofRealCLM ∘ (fun y => fderiv ℝ f y v)) z w at h
  rw [fderiv_comp z Complex.ofRealCLM.differentiableAt
    (hdf.clm_apply (differentiableAt_const v)),
    fderiv_clm_apply hdf (differentiableAt_const v)] at h
  simpa using h

-- Source: L18Aux.leviMatrix_entry_re_im → L12Aux.leviMatrix_entry_re_im
theorem leviMatrix_entry_re_im
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (dir : ι → E) (i j : ι) :
    (leviMatrix f z dir i j).re = (1 / 4 : ℝ) *
      (fderiv ℝ (fderiv ℝ f) z (dir j) (dir i) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • dir j) (Complex.I • dir i)) ∧
    (leviMatrix f z dir i j).im = (1 / 4 : ℝ) *
      (fderiv ℝ (fderiv ℝ f) z (dir j) (Complex.I • dir i) -
        fderiv ℝ (fderiv ℝ f) z (Complex.I • dir j) (dir i)) := by
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [leviMatrix, wirt_wirtBar_eq_secondFDeriv hdF]
  simp only [secondFDeriv_ofReal hf]
  constructor <;> simp [Complex.mul_re, Complex.mul_im]

-- Source: L18Aux.rDeriv_rDeriv_eq_hessian → L12Aux.rDeriv_rDeriv_eq_hessian
theorem rDeriv_rDeriv_eq_hessian {n : ℕ} {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) (a b : RIdx n) :
    rDeriv (fun w => rDeriv f w b) z a =
      fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold rDeriv
  rw [fderiv_clm_apply hdf (differentiableAt_const (realVec b))]
  simp

def hermitianRealification (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun a b => 2 * (if a.2 = b.2 then (H a.1 b.1).re
    else if a.2 = 0 then -(H a.1 b.1).im else (H a.1 b.1).im)

theorem realRicciMatrix_eq_realification (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) :
    realRicciMatrix g.form x z = hermitianRealification (-leviC (logDet g.form x) z) := by
  have hf : ContDiffAt ℝ 2 (logDet g.form x) z :=
    ((logDet_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hs (u v : ComplexVector n) := hf.isSymmSndFDerivAt (by norm_num) u v
  ext a b
  have hR := realRicciMatrix_eq_logDet g hK x z hz a b
  rw [rDeriv_rDeriv_eq_hessian hf, rDeriv_rDeriv_eq_hessian hf] at hR
  have hre (i j : Fin n) := (leviMatrix_entry_re_im hf stdVec i j).1
  have him (i j : Fin n) := (leviMatrix_entry_re_im hf stdVec i j).2
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [hermitianRealification, leviC, jIndex, jSign, realVec, stdVec] at hR ⊢
  all_goals
    simp only [hre, him]
    dsimp only [stdVec]
    linarith [hs (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      hs (Complex.I • EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1),
      hs (EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1),
      hs (Complex.I • EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]

def complexCoordsOfReal (r : RIdx n → ℝ) : Fin n → ℂ :=
  fun i => (r (i, 0) : ℂ) + Complex.I * (r (i, 1) : ℂ)

theorem hermitianRealification_quadratic (H : Matrix (Fin n) (Fin n) ℂ) (r : RIdx n → ℝ) :
    star r ⬝ᵥ (hermitianRealification H *ᵥ r) =
      2 * (star (complexCoordsOfReal r) ⬝ᵥ (H *ᵥ complexCoordsOfReal r)).re := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
    Complex.re_sum, Fintype.sum_prod_type, Fin.sum_univ_two, hermitianRealification]
  norm_num only [Fin.zero_eta, Fin.mk.injEq, ↓reduceIte]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [complexCoordsOfReal, Complex.mul_re, Complex.mul_im]
  ring

theorem hermitianRealification_quadratic_nonneg (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) (r : RIdx n → ℝ) :
    0 ≤ star r ⬝ᵥ (hermitianRealification H *ᵥ r) := by
  rw [hermitianRealification_quadratic]
  have hp := (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg (complexCoordsOfReal r))).1
  exact mul_nonneg (by norm_num) hp

theorem realRicciMatrix_posSemidef (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    (hR : (ricci g.form x).PosSemidef) :
    (realRicciMatrix g.form x (chartPt x x)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    exact realRicciMatrix_symm g x (chartPt x x) (mem_extChartAt_target x) b a
  · intro r
    rw [realRicciMatrix_eq_realification g hK x (chartPt x x) (mem_extChartAt_target x)]
    exact hermitianRealification_quadratic_nonneg (ricci g.form x) hR r

theorem complexCoordsOfReal_realCoord (v : ComplexVector n) :
    complexCoordsOfReal (realCoord v) = (fun i => v i) := by
  funext i
  apply Complex.ext <;> simp [complexCoordsOfReal, realCoord, Complex.mul_re, Complex.mul_im]

/-- The quadratic Ricci trace of the actual Levi--Civita curvature in the
 genuine chart basis at x, evaluated on the actual real tangent vector. -/
def realRicciQuadratic (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : ℝ :=
  ∑ a, ∑ b, realRicciMatrix g.form x (chartPt x x) a b *
    realCoord (tangentCoords x x (realTangentEquiv x v)) a *
    realCoord (tangentCoords x x (realTangentEquiv x v)) b

theorem realRicciQuadratic_nonneg (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ x, (ricci g.form x).PosSemidef) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : 0 ≤ realRicciQuadratic g x v := by
  let r := realCoord (tangentCoords x x (realTangentEquiv x v))
  have hp := (realRicciMatrix_posSemidef g hK x (hR x)).dotProduct_mulVec_nonneg r
  unfold realRicciQuadratic
  convert! hp using 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem realRicciQuadratic_eq_projectRicci (g : SmoothMetric M) (hK : IsKahler g)
    (x : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    realRicciQuadratic g x v =
      2 * (star (fun i => tangentCoords x x (realTangentEquiv x v) i) ⬝ᵥ
        (ricci g.form x *ᵥ (fun i => tangentCoords x x (realTangentEquiv x v) i))).re := by
  let r := realCoord (tangentCoords x x (realTangentEquiv x v))
  have hq : star r ⬝ᵥ (realRicciMatrix g.form x (chartPt x x) *ᵥ r) =
      realRicciQuadratic g x v := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, realRicciQuadratic]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [← hq, realRicciMatrix_eq_realification g hK x (chartPt x x) (mem_extChartAt_target x),
    hermitianRealification_quadratic]
  have hc : complexCoordsOfReal r = (fun i => tangentCoords x x (realTangentEquiv x v) i) :=
    complexCoordsOfReal_realCoord _
  rw [hc]
  rfl


def realCoordCLM (a : RIdx n) : ComplexVector n →L[ℝ] ℝ :=
  ((realVec_basis n).coord a).toContinuousLinearMap

theorem realCoordCLM_apply (a : RIdx n) (v : ComplexVector n) : realCoordCLM a v = realCoord v a :=
  realVec_basis_repr v a

theorem contDiff_realCoord (a : RIdx n) : ContDiff ℝ ∞ (fun v : ComplexVector n => realCoord v a) := by
  convert! (realCoordCLM a).contDiff using 1
  funext v
  exact (realCoordCLM_apply a v).symm

def chartGeodesicAcceleration (h : HermitianField M) (x : M.Carrier)
    (z v : ComplexVector n) : ComplexVector n :=
  -∑ c, (∑ a, ∑ b, christoffel h x z c a b * realCoord v a * realCoord v b) • realVec c

def chartGeodesicSpray (h : HermitianField M) (x : M.Carrier)
    (q : ComplexVector n × ComplexVector n) : ComplexVector n × ComplexVector n :=
  (q.2, chartGeodesicAcceleration h x q.1 q.2)

theorem chartGeodesicSpray_contDiffOn (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartGeodesicSpray g.form x) (chartTarget x ×ˢ Set.univ) := by
  have hΓ (c a b : RIdx n) : ContDiffOn ℝ ∞
      (fun q : ComplexVector n × ComplexVector n => christoffel g.form x q.1 c a b)
      (chartTarget x ×ˢ Set.univ) :=
    (christoffel_contDiffOn g x c a b).comp contDiffOn_fst (fun _ hq => hq.1)
  have hcoord (a : RIdx n) : ContDiffOn ℝ ∞
      (fun q : ComplexVector n × ComplexVector n => realCoord q.2 a)
      (chartTarget x ×ˢ Set.univ) :=
    ((contDiff_realCoord a).comp contDiff_snd).contDiffOn
  apply contDiffOn_snd.prodMk
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro c _
  apply ContDiffOn.fun_smul _ contDiffOn_const
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact ((hΓ c a b).mul (hcoord a)).mul (hcoord b)

theorem exists_local_chartGeodesic (g : SmoothMetric M) (x : M.Carrier)
    (z v : ComplexVector n) (hz : z ∈ chartTarget x) (t₀ : ℝ) :
    ∃ η : ℝ → ComplexVector n × ComplexVector n, η t₀ = (z, v) ∧
      ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        (η t).1 ∈ chartTarget x ∧ HasDerivAt η (chartGeodesicSpray g.form x (η t)) t := by
  have hO : IsOpen (chartTarget x ×ˢ (Set.univ : Set (ComplexVector n))) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hq : (z, v) ∈ chartTarget x ×ˢ (Set.univ : Set (ComplexVector n)) := ⟨hz, Set.mem_univ _⟩
  have hs := ((chartGeodesicSpray_contDiffOn g x).contDiffAt (hO.mem_nhds hq)).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  obtain ⟨η, hη, ε, hε, hsol⟩ :=
    hs.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have hc : ContinuousAt η t₀ := (hsol t₀ (by constructor <;> linarith)).continuousAt
  have hmem : η ⁻¹' (chartTarget x ×ˢ (Set.univ : Set (ComplexVector n))) ∈ 𝓝 t₀ :=
    hc.preimage_mem_nhds (hη.symm ▸ hO.mem_nhds hq)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨η, hη, min ε δ, lt_min hε hδ, ?_⟩
  intro t ht
  have htε : t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) :=
    ⟨by linarith [ht.1, ht.2, min_le_left ε δ], by linarith [ht.1, ht.2, min_le_left ε δ]⟩
  have htδ : t ∈ Metric.ball t₀ δ := by
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [ht.1, ht.2, min_le_right ε δ], by linarith [ht.1, ht.2, min_le_right ε δ]⟩
  exact ⟨(hsub htδ).1, hsol t htε⟩

theorem contMDiffAt_chartInv_real (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) :
    ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ (chartInv x) z := by
  letI := manifold_realSmooth M
  have hs := contMDiffWithinAt_extChartAt_symm_range
    (I := 𝓘(ℝ, ComplexVector n)) (n := ∞) x hz
  rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hs
  exact hs

theorem realCurveVelocity_chartGeodesic (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray g.form x (η t)) t) :
    realCurveVelocity (fun s => chartInv x (η s).1) t = realChartVec x (η t).1 (η t).2 := by
  letI := manifold_realSmooth M
  have hi := (contMDiffAt_chartInv_real x (η t).1 hz).mdifferentiableAt (by simp)
  have hp : HasDerivAt (fun s => (η s).1) (η t).2 t := by
    convert! hη.hasFDerivAt.fst.hasDerivAt using 1
    simp [chartGeodesicSpray]
  have hpd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) (fun s => (η s).1) t :=
    hp.differentiableAt.mdifferentiableAt
  unfold realCurveVelocity
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n)
    (chartInv x ∘ fun s => (η s).1) t
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1) = _
  rw [mfderiv_comp t hi hpd, ContinuousLinearMap.comp_apply,
    mfderiv_eq_fderiv, hp.hasFDerivAt.fderiv]
  simp [realChartVec, NormedSpace.fromTangentSpace, mfld_simps]

/-! Quantitative finite-dimensional smoothing for the later complete-metric
cutoff construction. The norm on E may be the frozen actual Riemannian tangent
norm; no comparison with the canonical chart norm is assumed here. -/
open ContinuousLinearMap
open scoped Convolution NNReal
section QuantitativeSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positiveConvolution_lipschitz [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {φ f : E → ℝ} {K : ℝ≥0}
    (hφ : Integrable φ μ) (hs : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ1 : ∫ x, φ x ∂μ = 1) (hf : LipschitzWith K f) :
    LipschitzWith K (φ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hconv := hs.convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) hφ.locallyIntegrable hf.continuous
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : Integrable (fun t => φ t * f (x - t)) μ := hconv x
  have hy : Integrable (fun t => φ t * f (y - t)) μ := hconv y
  rw [dist_eq_norm, convolution_def, convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  rw [← integral_sub hx hy]
  calc
    _ ≤ ∫ t, ‖φ t * f (x - t) - φ t * f (y - t)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, φ t * ((K : ℝ) * dist x y) ∂μ := by
      apply integral_mono (hx.sub hy).norm (hφ.mul_const _)
      intro t
      change ‖φ t * f (x - t) - φ t * f (y - t)‖ ≤ φ t * ((K : ℝ) * dist x y)
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hφ0 t)]
      have hdist : dist (x - t) (y - t) = dist x y := dist_sub_right x y t
      exact mul_le_mul_of_nonneg_left (by have hb := hf.dist_le_mul (x - t) (y - t); rw [hdist] at hb; simpa only [dist_eq_norm] using hb) (hφ0 t)
    _ = (K : ℝ) * dist x y := by rw [integral_mul_const, hφ1, one_mul]

theorem exists_contDiff_lipschitz_approx [FiniteDimensional ℝ E]
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith K g ∧
      (∀ x, dist (g x) (f x) < ε) ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ (K : ℝ)) := by
  borelize E
  let μ : Measure E := .addHaar
  let δ : ℝ := ε / (2 * ((K : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let φ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let g : E → ℝ := φ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hgs : ContDiff ℝ ∞ g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf.continuous.locallyIntegrable
  have hgl : LipschitzWith K g := positiveConvolution_lipschitz μ
    φ.integrable_normed φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hf
  refine ⟨g, hgs, hgl, ?_, fun x => norm_fderiv_le_of_lipschitz ℝ hgl⟩
  intro x
  have happrox : dist (g x) (f x) ≤ (K : ℝ) * δ :=
    φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable (fun y hy =>
      (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le K.coe_nonneg))
  apply happrox.trans_lt
  dsimp [δ]
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2 * ((K : ℝ) + 1))]
  nlinarith [K.coe_nonneg]

theorem exists_contDiff_lipschitz_approx_on [FiniteDimensional ℝ E]
    {f : E → ℝ} {K : ℝ≥0} {s : Set E} (hf : LipschitzOnWith K f s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith K g ∧
      (∀ x ∈ s, dist (g x) (f x) < ε) ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ (K : ℝ)) := by
  obtain ⟨F, hF, he⟩ := hf.extend_real
  obtain ⟨g, hgs, hgl, hga, hgd⟩ := exists_contDiff_lipschitz_approx hF hε
  exact ⟨g, hgs, hgl, fun x hx => he hx ▸ hga x, hgd⟩


end QuantitativeSmoothing


/-! Metric-adapted local charts freeze the norm in the actual tangent fiber. -/

theorem realTangent_trivialization_almostIsometry (g : SmoothMetric M) (x : M.Carrier)
    {r : ℝ} (hr : 1 < r) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ∀ᶠ y in 𝓝 x,
      ‖((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ x)
        ∘L ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ y)‖ < r ∧
      ‖((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ y)
        ∘L ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ x)‖ < r := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  letI := realRiemannianBundle_continuous g
  exact (eventually_norm_symmL_trivializationAt_self_comp_lt (ComplexVector n)
      (TangentSpace 𝓘(ℝ, ComplexVector n)) x hr).and
    (eventually_norm_symmL_trivializationAt_comp_self_lt (ComplexVector n)
      (TangentSpace 𝓘(ℝ, ComplexVector n)) x hr)

def realFrozenChart (x : M.Carrier) (y : M.Carrier) : TangentSpace 𝓘(ℝ, ComplexVector n) x := by
  letI := manifold_realSmooth M
  exact (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmₗ ℝ x (chartPt x y)

def realFrozenChartInv (x : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : M.Carrier := by
  letI := manifold_realSmooth M
  exact chartInv x ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).linearMapAt ℝ x v)

def realFrozenChartDomain (x : M.Carrier) : Set (TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := manifold_realSmooth M
  exact {v | (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).linearMapAt ℝ x v ∈ chartTarget x}

theorem realFrozenChartInv_realFrozenChart (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    realFrozenChartInv x (realFrozenChart x y) = y := by
  letI := manifold_realSmooth M
  simp only [realFrozenChartInv, realFrozenChart]
  rw [Trivialization.linearMapAt_symmₗ _ (FiberBundle.mem_baseSet_trivializationAt' x)]
  exact (extChartAt (ComplexModel n) x).left_inv hy

theorem realFrozenChart_realFrozenChartInv (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hv : v ∈ realFrozenChartDomain x) :
    realFrozenChart x (realFrozenChartInv x v) = v := by
  letI := manifold_realSmooth M
  simp only [realFrozenChartInv, realFrozenChart]
  have he : chartPt x (chartInv x ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).linearMapAt ℝ x v)) =
      (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).linearMapAt ℝ x v :=
    (extChartAt (ComplexModel n) x).right_inv hv
  rw [he]
  exact Trivialization.symmₗ_linearMapAt _ (FiberBundle.mem_baseSet_trivializationAt' x) v

theorem realFrozenChartInv_contMDiffAt (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) (hv : v ∈ realFrozenChartDomain x) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n) ∞
      (realFrozenChartInv x) v := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let e := (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ x
  have he : ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n) ∞ e := by
    rw [contMDiff_iff_contDiff]
    exact e.contDiff
  exact (contMDiffAt_chartInv_real x (e v) hv).comp v he.contMDiffAt

theorem realFrozenChartInv_mfderiv (g : SmoothMetric M) (x : M.Carrier)
    (v w : TangentSpace 𝓘(ℝ, ComplexVector n) x) (hv : v ∈ realFrozenChartDomain x) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n)
      (realFrozenChartInv x) v ((NormedSpace.fromTangentSpace v).symm w) =
      (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ (realFrozenChartInv x v)
        ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ x w) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let e := (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ x
  have hi := (contMDiffAt_chartInv_real x (e v) hv).mdifferentiableAt (by simp)
  have he : MDifferentiableAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n) e v :=
    e.differentiableAt.mdifferentiableAt
  have hz : realFrozenChartInv x v ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv, realFrozenChartInv] using (extChartAt (ComplexModel n) x).map_target hv
  have hchart : chartPt x (realFrozenChartInv x v) = e v :=
    (extChartAt (ComplexModel n) x).right_inv hv
  have hs := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, ComplexVector n)) hz
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hs
  change mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n)
      (chartInv x ∘ e) v ((NormedSpace.fromTangentSpace v).symm w) = _
  rw [mfderiv_comp v hi he, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, e.fderiv]
  have hs' := congrArg (fun L => L (e w)) hs
  refine Eq.trans ?_ hs'.symm
  change mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
    (chartInv x) (e v) (e w) = mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
      (chartInv x) (chartPt x (realFrozenChartInv x v)) (e w)
  rw [hchart]

theorem realFrozenChartDomain_isOpen (x : M.Carrier) : IsOpen (realFrozenChartDomain x) := by
  letI := manifold_realSmooth M
  exact (isOpen_extChartAt_target (I := ComplexModel n) x).preimage
    ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ x).continuous

theorem realFrozenChart_self_mem (x : M.Carrier) : realFrozenChart x x ∈ realFrozenChartDomain x := by
  letI := manifold_realSmooth M
  change (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).linearMapAt ℝ x
    ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmₗ ℝ x (chartPt x x)) ∈ chartTarget x
  rw [Trivialization.linearMapAt_symmₗ _ (FiberBundle.mem_baseSet_trivializationAt' x)]
  exact mem_extChartAt_target x


def realFrozenTransport (g : SmoothMetric M) (x y : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    TangentSpace 𝓘(ℝ, ComplexVector n) x →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ y) ∘L
    ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ x)

def realFrozenTransportBack (g : SmoothMetric M) (x y : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    TangentSpace 𝓘(ℝ, ComplexVector n) y →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ x) ∘L
    ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ y)

theorem exists_realFrozenChart_ball (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ∃ ρ > (0 : ℝ), Metric.ball (realFrozenChart x x) ρ ⊆ realFrozenChartDomain x ∧
      ∀ v ∈ Metric.ball (realFrozenChart x x) ρ,
        ‖realFrozenTransport g x (realFrozenChartInv x v)‖ < 2 ∧
        ‖realFrozenTransportBack g x (realFrozenChartInv x v)‖ < 2 := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hc := (realFrozenChartInv_contMDiffAt g x (realFrozenChart x x)
    (realFrozenChart_self_mem x)).continuousAt
  have he : realFrozenChartInv x (realFrozenChart x x) = x :=
    realFrozenChartInv_realFrozenChart x x (mem_extChartAt_source x)
  have hc' : Tendsto (realFrozenChartInv x) (𝓝 (realFrozenChart x x)) (𝓝 x) := by
    simpa only [ContinuousAt, he] using hc
  have hn := hc'.eventually (realTangent_trivialization_almostIsometry g x (by norm_num : (1 : ℝ) < 2))
  have ho : realFrozenChartDomain x ∈ 𝓝 (realFrozenChart x x) :=
    (realFrozenChartDomain_isOpen x).mem_nhds (realFrozenChart_self_mem x)
  have hh : {v | v ∈ realFrozenChartDomain x ∧
      ‖realFrozenTransport g x (realFrozenChartInv x v)‖ < 2 ∧
      ‖realFrozenTransportBack g x (realFrozenChartInv x v)‖ < 2} ∈ 𝓝 (realFrozenChart x x) := by
    filter_upwards [ho, hn] with v hv hnorm
    exact ⟨hv, hnorm.2, hnorm.1⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hh
  exact ⟨ρ, hρ, fun v hv => (hsub hv).1, fun v hv => (hsub hv).2⟩


section ChartDistance
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem inducedDistance_le_of_chart_deriv (g : SmoothMetric M)
    (ψ : V → M.Carrier) {s : Set V} (hs : IsOpen s) (hconv : Convex ℝ s)
    {C : ℝ} (hC : 0 ≤ C) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, ComplexVector n) 1 ψ s →
    (∀ z ∈ s, ∀ u : V, ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ComplexVector n) ψ z
      ((NormedSpace.fromTangentSpace z).symm u)‖ ≤ C * ‖u‖) →
    ∀ v ∈ s, ∀ w ∈ s, inducedDistance g.form (ψ v) (ψ w) ≤ C * dist v w := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hψ hD v hv w hw
  let η := ContinuousAffineMap.lineMap (R := ℝ) v w
  let γ := ψ ∘ η
  have hηs : Set.MapsTo η (Set.Icc 0 1) s := by
    change Set.Icc 0 1 ⊆ η ⁻¹' s
    rw [← Set.image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact hconv.segment_subset hv hw
  have hηsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 η := by
    rw [contMDiff_iff_contDiff]
    exact η.contDiff
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ (Set.Icc 0 1) :=
    hψ.comp hηsmooth.contMDiffOn hηs
  have hd : ENNReal.ofReal (inducedDistance g.form (ψ v) (ψ w)) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ 0 1 := by
    rw [inducedDistance_eq_riemannianEDist g]
    apply Manifold.riemannianEDist_le_pathELength hγ _ _ zero_le_one
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hlen : Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ 0 1 ≤
      ENNReal.ofReal (C * dist v w) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have hconst : (∫⁻ _t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (C * dist v w)) =
        ENNReal.ofReal (C * dist v w) := by simp
    rw [← hconst]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have hpd := ((hψ (η t) (hηs ht)).contMDiffAt (hs.mem_nhds (hηs ht))).mdifferentiableAt (by simp)
    have hline : HasDerivAt η (w - v) t := AffineMap.hasDerivAt_lineMap
    have he : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ t 1 =
        mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ComplexVector n) ψ (η t)
          ((NormedSpace.fromTangentSpace (η t)).symm (w - v)) := by
      rw [mfderiv_comp t hpd hline.differentiableAt.mdifferentiableAt,
        ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, hline.hasFDerivAt.fderiv]
      simp [NormedSpace.fromTangentSpace, tangentSpaceCastModel, mfld_simps]
      change (1 : ℝ) • _ = _
      exact one_smul ℝ _
    rw [he, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_eq_norm, norm_sub_rev] using hD (η t) (hηs ht) (w - v)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC dist_nonneg)).mp (hd.trans hlen)


end ChartDistance

theorem exists_realFrozenChart_lipschitz (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    letI := inducedMetricSpace g
    ∃ ρ > (0 : ℝ), Metric.ball (realFrozenChart x x) ρ ⊆ realFrozenChartDomain x ∧
      LipschitzOnWith 2 (realFrozenChartInv x) (Metric.ball (realFrozenChart x x) ρ) ∧
      ∀ v ∈ Metric.ball (realFrozenChart x x) ρ,
        ‖realFrozenTransportBack g x (realFrozenChartInv x v)‖ < 2 := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  letI := inducedMetricSpace g
  obtain ⟨ρ, hρ, hdom, hnorm⟩ := exists_realFrozenChart_ball g x
  refine ⟨ρ, hρ, hdom, ?_, fun v hv => (hnorm v hv).2⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  apply inducedDistance_le_of_chart_deriv g (realFrozenChartInv x) Metric.isOpen_ball
    (convex_ball _ _) (by norm_num : (0 : ℝ) ≤ 2) _ _ v hv w hw
  · intro z hz
    exact (realFrozenChartInv_contMDiffAt g x z (hdom hz)).contMDiffWithinAt.of_le (by simp)
  · intro z hz u
    rw [realFrozenChartInv_mfderiv g x z u (hdom hz)]
    exact ((realFrozenTransport g x (realFrozenChartInv x z)).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hnorm z hz).1.le (norm_nonneg u))


/-- A local C∞ approximation in a metric-adapted chart, with a derivative
bound independent of the metric and the chart. This is local data, not yet
an assembled compactly supported cutoff. -/
theorem exists_local_metric_lipschitz_smoothing (g : SmoothMetric M) (x : M.Carrier)
    (f : M.Carrier → ℝ) (K : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    letI := inducedMetricSpace g
    LipschitzWith K f →
    ∃ ρ > (0 : ℝ), ∃ F : TangentSpace 𝓘(ℝ, ComplexVector n) x → ℝ,
      Metric.ball (realFrozenChart x x) ρ ⊆ realFrozenChartDomain x ∧
      ContDiff ℝ ∞ F ∧ LipschitzWith (K * 2) F ∧
      (∀ v ∈ Metric.ball (realFrozenChart x x) ρ, dist (F v) (f (realFrozenChartInv x v)) < ε) ∧
      (∀ v, ‖fderiv ℝ F v‖ ≤ 2 * (K : ℝ)) ∧
      ∀ v ∈ Metric.ball (realFrozenChart x x) ρ,
        ‖realFrozenTransportBack g x (realFrozenChartInv x v)‖ < 2 := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  letI := inducedMetricSpace g
  intro hf
  obtain ⟨ρ, hρ, hdom, hψ, hback⟩ := exists_realFrozenChart_lipschitz g x
  have hl := hf.comp_lipschitzOnWith hψ
  obtain ⟨F, hFs, hFL, hFa, hFd⟩ := exists_contDiff_lipschitz_approx_on hl hε
  refine ⟨ρ, hρ, F, hdom, hFs, hFL, hFa, ?_, hback⟩
  intro v
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_comm] using hFd v


/-! Ordinary real differential and quantitative local smoothing on fixed neighborhoods. -/

/-- The ordinary real differential, normed with the actual Riemannian source
fiber and the usual real target. -/
def realDifferential (g : SmoothMetric M) (f : M.Carrier → ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    TangentSpace 𝓘(ℝ, ComplexVector n) x →L[ℝ] ℝ := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  exact (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap ∘L
    mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) f x

theorem realFrozenChart_contMDiffAt (g : SmoothMetric M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) ∞
      (realFrozenChart x) y := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  let e := (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ x
  have he : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) ∞ e := by
    rw [contMDiff_iff_contDiff]
    exact e.contDiff
  have hi : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ (chartPt x) y := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (x := x) (x' := y) (by simpa only [extChartAt_source] using hy)) using 1
    infer_instance
  exact he.contMDiffAt.comp y hi

theorem realFrozenChart_mfderiv (g : SmoothMetric M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source)
    (u : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    (NormedSpace.fromTangentSpace (realFrozenChart x y))
      (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x)
        (realFrozenChart x) y u) = realFrozenTransportBack g x y u := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  let e := (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ x
  have he : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) e (chartPt x y) :=
    e.differentiableAt.mdifferentiableAt
  have hs : y ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source] using hy
  have hi := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, ComplexVector n)) hs
  change (NormedSpace.fromTangentSpace (realFrozenChart x y))
    (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x)
      (e ∘ chartPt x) y u) = _
  rw [mfderiv_comp y he hi, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, e.fderiv]
  rw [realFrozenTransportBack, ContinuousLinearMap.comp_apply,
    TangentBundle.continuousLinearMapAt_trivializationAt hs]
  rfl


theorem realDifferential_frozenChart (g : SmoothMetric M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source)
    (F : TangentSpace 𝓘(ℝ, ComplexVector n) x → ℝ) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    DifferentiableAt ℝ F (realFrozenChart x y) →
    realDifferential g (F ∘ realFrozenChart x) y =
      (fderiv ℝ F (realFrozenChart x y)) ∘L (realFrozenTransportBack g x y) := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hF
  have hc := (realFrozenChart_contMDiffAt g x y hy).mdifferentiableAt (by simp)
  ext u
  unfold realDifferential
  simp only [ContinuousLinearMap.comp_apply]
  rw [mfderiv_comp y hF.mdifferentiableAt hc, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
  change (fderiv ℝ F (realFrozenChart x y))
    ((NormedSpace.fromTangentSpace (realFrozenChart x y))
      (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x)
        (realFrozenChart x) y u)) = _
  rw [realFrozenChart_mfderiv g x y hy u]

theorem norm_realDifferential_frozenChart_le (g : SmoothMetric M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source)
    (F : TangentSpace 𝓘(ℝ, ComplexVector n) x → ℝ) {K : ℝ} (hK : 0 ≤ K) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    DifferentiableAt ℝ F (realFrozenChart x y) →
    ‖fderiv ℝ F (realFrozenChart x y)‖ ≤ 2 * K →
    ‖realFrozenTransportBack g x y‖ ≤ 2 →
    ‖realDifferential g (F ∘ realFrozenChart x) y‖ ≤ 4 * K := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hF hd hb
  rw [realDifferential_frozenChart g x y hy F hF]
  calc
    _ ≤ ‖fderiv ℝ F (realFrozenChart x y)‖ * ‖realFrozenTransportBack g x y‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (2 * K) * 2 := mul_le_mul hd hb (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    _ = 4 * K := by ring


def realFrozenChartBall (g : SmoothMetric M) (x : M.Carrier) (ρ : ℝ) : Set M.Carrier := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  exact (extChartAt (ComplexModel n) x).source ∩
    (realFrozenChart x) ⁻¹' Metric.ball (realFrozenChart x x) ρ

theorem realFrozenChartBall_isOpen (g : SmoothMetric M) (x : M.Carrier) (ρ : ℝ) :
    IsOpen (realFrozenChartBall g x ρ) := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  have hc : ContinuousOn (realFrozenChart x) (extChartAt (ComplexModel n) x).source :=
    fun y hy => (realFrozenChart_contMDiffAt g x y hy).continuousAt.continuousWithinAt
  exact hc.isOpen_inter_preimage (isOpen_extChartAt_source (I := ComplexModel n) x) Metric.isOpen_ball

theorem realFrozenChartBall_self_mem (g : SmoothMetric M) (x : M.Carrier) {ρ : ℝ} (hρ : 0 < ρ) :
    x ∈ realFrozenChartBall g x ρ := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  exact ⟨mem_extChartAt_source x, Metric.mem_ball_self hρ⟩

theorem exists_local_smooth_realDifferential_le (g : SmoothMetric M) (x : M.Carrier)
    (f : M.Carrier → ℝ) (K : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    letI := inducedMetricSpace g
    LipschitzWith K f →
    ∃ U : Set M.Carrier, IsOpen U ∧ x ∈ U ∧ ∃ h : M.Carrier → ℝ,
      ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ h U ∧
      (∀ y ∈ U, dist (h y) (f y) < ε) ∧
      ∀ y ∈ U, ‖realDifferential g h y‖ ≤ 4 * (K : ℝ) := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  letI := inducedMetricSpace g
  intro hf
  obtain ⟨ρ, hρ, F, hdom, hFs, hFL, hFa, hFd, hback⟩ :=
    exists_local_metric_lipschitz_smoothing g x f K hε hf
  refine ⟨realFrozenChartBall g x ρ, realFrozenChartBall_isOpen g x ρ,
    realFrozenChartBall_self_mem g x hρ, F ∘ realFrozenChart x, ?_, ?_, ?_⟩
  · intro y hy
    exact ((hFs.contMDiff.contMDiffAt).comp y
      (realFrozenChart_contMDiffAt g x y hy.1)).contMDiffWithinAt
  · intro y hy
    have he : realFrozenChartInv x (realFrozenChart x y) = y :=
      realFrozenChartInv_realFrozenChart x y hy.1
    simpa only [Function.comp_apply, he] using hFa (realFrozenChart x y) hy.2
  · intro y hy
    apply norm_realDifferential_frozenChart_le g x y hy.1 F K.coe_nonneg
      (hFs.differentiable (by simp)).differentiableAt (hFd _)
    have he : realFrozenChartInv x (realFrozenChart x y) = y :=
      realFrozenChartInv_realFrozenChart x y hy.1
    have hb := (hback (realFrozenChart x y) hy.2).le
    rw [he] at hb
    exact hb

theorem smoothFn_of_contMDiff_real (f : M.Carrier → ℝ) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ f → SmoothFn f := by
  letI := manifold_realSmooth M
  intro hf x
  have hi := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) (n := ∞) x
  have hc := hf.comp_contMDiffOn hi
  exact hc.contDiffOn


/-- The neighborhood is fixed before the approximation tolerance, allowing
partition derivatives to be bounded before local approximation errors are chosen. -/
theorem exists_metric_smoothing_neighborhood (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    letI := inducedMetricSpace g
    ∃ U : Set M.Carrier, IsOpen U ∧ x ∈ U ∧
      ∀ (f : M.Carrier → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε > (0 : ℝ),
        ∃ h : M.Carrier → ℝ, ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ h U ∧
          (∀ y ∈ U, dist (h y) (f y) < ε) ∧
          ∀ y ∈ U, ‖realDifferential g h y‖ ≤ 4 * (K : ℝ) := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  letI := inducedMetricSpace g
  obtain ⟨ρ, hρ, hdom, hψ, hback⟩ := exists_realFrozenChart_lipschitz g x
  refine ⟨realFrozenChartBall g x ρ, realFrozenChartBall_isOpen g x ρ,
    realFrozenChartBall_self_mem g x hρ, ?_⟩
  intro f K hf ε hε
  obtain ⟨F, hFs, hFL, hFa, hFd⟩ :=
    exists_contDiff_lipschitz_approx_on (hf.comp_lipschitzOnWith hψ) hε
  have hdF : ∀ v, ‖fderiv ℝ F v‖ ≤ 2 * (K : ℝ) := by
    intro v
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_comm] using hFd v
  refine ⟨F ∘ realFrozenChart x, ?_, ?_, ?_⟩
  · intro y hy
    exact (hFs.contMDiff.contMDiffAt.comp y
      (realFrozenChart_contMDiffAt g x y hy.1)).contMDiffWithinAt
  · intro y hy
    have he : realFrozenChartInv x (realFrozenChart x y) = y :=
      realFrozenChartInv_realFrozenChart x y hy.1
    simpa only [Function.comp_apply, he] using hFa (realFrozenChart x y) hy.2
  · intro y hy
    apply norm_realDifferential_frozenChart_le g x y hy.1 F K.coe_nonneg
      (hFs.differentiable (by simp)).differentiableAt (hdF _)
    have he : realFrozenChartInv x (realFrozenChart x y) = y :=
      realFrozenChartInv_realFrozenChart x y hy.1
    have hb := (hback (realFrozenChart x y) hy.2).le
    rw [he] at hb
    exact hb




theorem realDifferential_congr_of_eventuallyEq (g : SmoothMetric M) {f h : M.Carrier → ℝ}
    {x : M.Carrier} (he : f =ᶠ[𝓝 x] h) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    realDifferential g f x = realDifferential g h x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  ext u
  change mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) f x u =
    mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) h x u
  rw [he.mfderiv_eq]
  rfl

theorem exists_local_bound_realDifferential (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ f →
    ∃ U : Set M.Carrier, IsOpen U ∧ x ∈ U ∧ ∃ B > (0 : ℝ),
      ∀ y ∈ U, ‖realDifferential g f y‖ ≤ B := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hf
  let F := f ∘ realFrozenChartInv x
  have hF : ContDiffOn ℝ ∞ F (realFrozenChartDomain x) := by
    apply ContMDiffOn.contDiffOn
    intro v hv
    exact (hf.contMDiffAt.comp v (realFrozenChartInv_contMDiffAt g x v hv)).contMDiffWithinAt
  have hcenter := realFrozenChart_self_mem x
  have hco := realFrozenChartDomain_isOpen x
  have hcont : ContinuousAt (fun v => ‖fderiv ℝ F v‖) (realFrozenChart x x) :=
    ((hF.continuousOn_fderiv_of_isOpen hco (by simp)) _ hcenter).continuousAt
      (hco.mem_nhds hcenter) |>.norm
  let A := ‖fderiv ℝ F (realFrozenChart x x)‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmall : {v | ‖fderiv ℝ F v‖ < A} ∈ 𝓝 (realFrozenChart x x) :=
    hcont.preimage_mem_nhds (Iio_mem_nhds (by dsimp [A]; linarith))
  obtain ⟨ρ, hρ, hdom, hback⟩ := exists_realFrozenChart_ball g x
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (Metric.ball_mem_nhds _ hρ) hsmall)
  refine ⟨realFrozenChartBall g x δ, realFrozenChartBall_isOpen g x δ,
    realFrozenChartBall_self_mem g x hδ, 2 * A, by positivity, ?_⟩
  intro y hy
  have hvρ := (hsub hy.2).1
  have hvdom := hdom hvρ
  have hFd : DifferentiableAt ℝ F (realFrozenChart x y) :=
    ((hF _ hvdom).contDiffAt (hco.mem_nhds hvdom)).differentiableAt (by simp)
  have he : realFrozenChartInv x (realFrozenChart x y) = y :=
    realFrozenChartInv_realFrozenChart x y hy.1
  have hnorm := (hback (realFrozenChart x y) hvρ).2.le
  rw [he] at hnorm
  have hEq : F ∘ realFrozenChart x =ᶠ[𝓝 y] f := by
    filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hy.1] with z hz
    exact congrArg f (realFrozenChartInv_realFrozenChart x z hz)
  rw [← realDifferential_congr_of_eventuallyEq g hEq,
    realDifferential_frozenChart g x y hy.1 F hFd]
  calc
    _ ≤ ‖fderiv ℝ F (realFrozenChart x y)‖ * ‖realFrozenTransportBack g x y‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ A * 2 := mul_le_mul (hsub hy.2).2.le hnorm (ContinuousLinearMap.opNorm_nonneg _) hA.le
    _ = 2 * A := by ring


theorem exists_bound_realDifferential_on_isCompact (g : SmoothMetric M) (f : M.Carrier → ℝ)
    {K : Set M.Carrier} (hK : IsCompact K) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ f →
    ∃ B > (0 : ℝ), ∀ x ∈ K, ‖realDifferential g f x‖ ≤ B := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  classical
  intro hf
  choose U ho hm B hB hb using fun x => exists_local_bound_realDifferential g f x hf
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U ho (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  have hsum : 0 ≤ ∑ i ∈ s, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨1 + ∑ i ∈ s, B i, by linarith, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
  obtain ⟨his, hix⟩ := Set.mem_iUnion.mp hi
  have hsingle : B i ≤ ∑ j ∈ s, B j := Finset.single_le_sum (fun j _ => (hB j).le) his
  exact (hb i x hix).trans (by linarith)

theorem realDifferential_zero (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    realDifferential g (fun _ => (0 : ℝ)) x = 0 := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  unfold realDifferential
  rw [mfderiv_const, ContinuousLinearMap.comp_zero]

theorem realDifferential_of_notMem_tsupport (g : SmoothMetric M) {f : M.Carrier → ℝ}
    {x : M.Carrier} (hx : x ∉ tsupport f) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    realDifferential g f x = 0 := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  rw [realDifferential_congr_of_eventuallyEq g (notMem_tsupport_iff_eventuallyEq.mp hx)]
  exact realDifferential_zero g x

theorem exists_bound_realDifferential_of_hasCompactSupport (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hc : HasCompactSupport f) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ f →
    ∃ B > (0 : ℝ), ∀ x, ‖realDifferential g f x‖ ≤ B := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hf
  obtain ⟨B, hB, hb⟩ := exists_bound_realDifferential_on_isCompact g f hc hf
  refine ⟨B, hB, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hb x hx
  · rw [realDifferential_of_notMem_tsupport g hx, ContinuousLinearMap.opNorm_zero]
    exact hB.le



def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clamp01_lipschitz : LipschitzWith 1 clamp01 :=
  (LipschitzWith.id.const_min 1).const_max 0

theorem clamp01_eq_zero {t : ℝ} (ht : t ≤ 0) : clamp01 t = 0 := by
  simp only [clamp01, min_eq_right (ht.trans zero_le_one), max_eq_left ht]

theorem clamp01_eq_one {t : ℝ} (ht : 1 ≤ t) : clamp01 t = 1 := by
  simp only [clamp01, min_eq_left ht, max_eq_right zero_le_one]

theorem smoothTransition_clamp01 (t : ℝ) : Real.smoothTransition (clamp01 t) = Real.smoothTransition t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [clamp01_eq_zero ht, Real.smoothTransition.zero, Real.smoothTransition.zero_of_nonpos ht]
  rcases le_or_gt 1 t with h1 | h1
  · rw [clamp01_eq_one h1, Real.smoothTransition.one, Real.smoothTransition.one_of_one_le h1]
  · simp only [clamp01, min_eq_right h1.le, max_eq_right ht.le]

theorem exists_smoothTransition_lipschitz :
    ∃ L : ℝ≥0, 0 < L ∧ LipschitzWith L Real.smoothTransition := by
  obtain ⟨K, hK⟩ := (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_Icc (0 : ℝ) 1) isCompact_Icc
  have hglobal : LipschitzWith K Real.smoothTransition := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [← smoothTransition_clamp01 x, ← smoothTransition_clamp01 y]
    exact (hK.dist_le_mul _ (clamp01_mem x) _ (clamp01_mem y)).trans
      (mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one, one_mul] using clamp01_lipschitz.dist_le_mul x y) K.coe_nonneg)
  refine ⟨K + 1, by positivity, hglobal.weaken (by simp)⟩

def cutoffTransition (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

theorem cutoffTransition_contDiff : ContDiff ℝ ∞ cutoffTransition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem cutoffTransition_mem (t : ℝ) : cutoffTransition t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoffTransition_zero {t : ℝ} (ht : t ≤ 1 / 4) : cutoffTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoffTransition_one {t : ℝ} (ht : 3 / 4 ≤ t) : cutoffTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem exists_cutoffTransition_lipschitz :
    ∃ L : ℝ≥0, 0 < L ∧ LipschitzWith L cutoffTransition := by
  obtain ⟨K, hK, hLip⟩ := exists_smoothTransition_lipschitz
  have haff : LipschitzWith 2 (fun t : ℝ => 2 * t - 1 / 2) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    have he : (2 * x - 1 / 2) - (2 * y - 1 / 2) = 2 * (x - y) := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rfl
  exact ⟨K * 2, mul_pos hK (by norm_num), hLip.comp haff⟩

def distanceCutoff (h : HermitianField M) (x : M.Carrier) (R : ℝ) (y : M.Carrier) : ℝ :=
  clamp01 (2 - inducedDistance h x y / R)

theorem distanceCutoff_mem (h : HermitianField M) (x y : M.Carrier) (R : ℝ) :
    distanceCutoff h x R y ∈ Set.Icc (0 : ℝ) 1 := clamp01_mem _

theorem distanceCutoff_one (h : HermitianField M) (x y : M.Carrier) {R : ℝ} (hR : 0 < R)
    (hy : inducedDistance h x y ≤ R) : distanceCutoff h x R y = 1 := by
  apply clamp01_eq_one
  have hd : inducedDistance h x y / R ≤ 1 := (div_le_one hR).mpr hy
  linarith

theorem distanceCutoff_zero (h : HermitianField M) (x y : M.Carrier) {R : ℝ} (hR : 0 < R)
    (hy : 2 * R ≤ inducedDistance h x y) : distanceCutoff h x R y = 0 := by
  apply clamp01_eq_zero
  have hd : 2 ≤ inducedDistance h x y / R := (le_div_iff₀ hR).mpr hy
  linarith

theorem distanceCutoff_lipschitz (g : SmoothMetric M) (x : M.Carrier) {R : ℝ} (hR : 0 < R) :
    letI := inducedMetricSpace g
    LipschitzWith (Real.toNNReal R⁻¹) (distanceCutoff g.form x R) := by
  letI := inducedMetricSpace g
  have haff : LipschitzWith (Real.toNNReal R⁻¹)
      (fun t : ℝ => 2 - t / R) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Real.dist_eq, Real.dist_eq]
    have he : (2 - a / R) - (2 - b / R) = (b - a) / R := by ring
    rw [he, abs_div, abs_of_pos hR, abs_sub_comm, Real.coe_toNNReal _ (inv_nonneg.mpr hR.le)]
    exact le_of_eq (by ring)
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hp := clamp01_lipschitz.dist_le_mul
    (2 - dist x y / R) (2 - dist x z / R)
  simp only [NNReal.coe_one, one_mul] at hp
  have hd := (LipschitzWith.dist_right x).dist_le_mul y z
  simp only [NNReal.coe_one, one_mul] at hd
  exact (hp.trans (haff.dist_le_mul _ _)).trans
    (mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _))



theorem exists_finite_metric_smoothing_partition (g : SmoothMetric M)
    {K₀ : Set M.Carrier} (hK₀ : IsCompact K₀) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    letI := inducedMetricSpace g
    ∃ s : Finset M.Carrier, ∃ p : SmoothPartitionOfUnity s 𝓘(ℝ, ComplexVector n) M.Carrier K₀,
      (∀ i, HasCompactSupport (p i)) ∧
      ∀ i (f : M.Carrier → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε > (0 : ℝ),
        ∃ h : M.Carrier → ℝ,
          (∀ y ∈ tsupport (p i), ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ h y) ∧
          (∀ y ∈ tsupport (p i), dist (h y) (f y) < ε) ∧
          ∀ y ∈ tsupport (p i), ‖realDifferential g h y‖ ≤ 4 * (K : ℝ) := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  letI := inducedMetricSpace g
  letI := inducedMetricSpace_proper g
  letI : LocallyCompactSpace M.Carrier := manifold_locallyCompact M
  letI : SecondCountableTopology M.Carrier := M.secondCountable
  classical
  choose U ho hm happrox using fun x => exists_metric_smoothing_neighborhood g x
  let V (x : M.Carrier) := U x ∩ Metric.ball x 1
  have hVo (x) : IsOpen (V x) := (ho x).inter Metric.isOpen_ball
  have hVm (x) : x ∈ V x := ⟨hm x, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨s, hs⟩ := hK₀.elim_finite_subcover V hVo (fun x _ => Set.mem_iUnion.mpr ⟨x, hVm x⟩)
  have hcover : K₀ ⊆ ⋃ i : s, V i := by
    intro y hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hs hy)
    obtain ⟨hxs, hxy⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hxs⟩, hxy⟩
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ComplexVector n)) hK₀.isClosed (fun i : s => V i) (fun i => hVo i) hcover
  refine ⟨s, p, ?_, ?_⟩
  · intro i
    exact (isCompact_closedBall (i : M.Carrier) 1).of_isClosed_subset (isClosed_tsupport _)
      (fun y hy => Metric.ball_subset_closedBall ((hp i hy).2))
  · intro i f K hf ε hε
    obtain ⟨h, hhs, hha, hhd⟩ := happrox (i : M.Carrier) f K hf ε hε
    refine ⟨h, ?_, ?_, ?_⟩
    · intro y hy
      exact (hhs y (hp i hy).1).contMDiffAt ((ho i).mem_nhds (hp i hy).1)
    · intro y hy
      exact hha y (hp i hy).1
    · intro y hy
      exact hhd y (hp i hy).1



/-! Finite quantitative smoothing and complete-metric smooth distance cutoffs. -/

theorem realDifferential_eq_mvfderiv (g : SmoothMetric M) (f : M.Carrier → ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    realDifferential g f x = mvfderiv 𝓘(ℝ, ComplexVector n) f x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  rfl

theorem realDifferential_const (g : SmoothMetric M) (c : ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    realDifferential g (fun _ => c) x = 0 := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  exact mvfderiv_const c

theorem realDifferential_add (g : SmoothMetric M) (f h : M.Carrier → ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) f x →
    MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) h x →
    realDifferential g (fun y => f y + h y) x = realDifferential g f x + realDifferential g h x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hf hh
  exact mvfderiv_add hf hh

theorem realDifferential_sub (g : SmoothMetric M) (f h : M.Carrier → ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) f x →
    MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) h x →
    realDifferential g (fun y => f y - h y) x = realDifferential g f x - realDifferential g h x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hf hh
  exact mvfderiv_sub hf hh

theorem realDifferential_finset_sum {ι : Type*} (g : SmoothMetric M) (s : Finset ι)
    (F : ι → M.Carrier → ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    (∀ i ∈ s, MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (F i) x) →
    realDifferential g (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, realDifferential g (F i) x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty]
    exact realDifferential_const g 0 x
  | @insert a s ha ih =>
    intro hF
    have hFa := hF a (Finset.mem_insert_self _ _)
    have hFs : ∀ i ∈ s, MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (F i) x :=
      fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hsum : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, F i y) x := by
      convert! MDifferentiableAt.sum hFs using 1
      funext y
      simp only [Finset.sum_apply]
    simp only [Finset.sum_insert ha]
    rw [realDifferential_add g _ _ x hFa hsum, ih hFs]

theorem realDifferential_mul_sub_const_supported (g : SmoothMetric M)
    (φ h : M.Carrier → ℝ) (c : ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) φ x →
    (x ∈ tsupport φ → MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) h x) →
    realDifferential g (fun y => φ y * (h y - c)) x =
      φ x • realDifferential g h x + (h x - c) • realDifferential g φ x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hφ hh
  by_cases hx : x ∈ tsupport φ
  · have hm := hh hx
    change mvfderiv 𝓘(ℝ, ComplexVector n) (φ * (h - fun _ => c)) x = _
    rw [mvfderiv_mul hφ (hm.sub mdifferentiableAt_const),
      mvfderiv_sub hm mdifferentiableAt_const, mvfderiv_const]
    simp only [sub_zero]
    rfl
  · have hprod : x ∉ tsupport (fun y => φ y * (h y - c)) :=
      fun hp => hx (tsupport_mul_subset_left hp)
    rw [realDifferential_of_notMem_tsupport g hprod,
      realDifferential_of_notMem_tsupport g hx, image_eq_zero_of_notMem_tsupport hx]
    simp only [zero_smul, smul_zero, zero_add]



section WeightedEstimates
variable {ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem norm_nonnegative_weighted_sum_le (p : ι → ℝ) (v : ι → W) {A : ℝ}
    (hA : 0 ≤ A) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    (hv : ∀ i, p i ≠ 0 → ‖v i‖ ≤ A) : ‖∑ i, p i • v i‖ ≤ A := by
  calc
    _ ≤ ∑ i, ‖p i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, p i * A := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : p i = 0
      · simp only [hi, zero_smul, norm_zero, zero_mul, le_refl]
      · rw [norm_smul, Real.norm_of_nonneg (hp i)]
        exact mul_le_mul_of_nonneg_left (hv i hi) (hp i)
    _ = (∑ i, p i) * A := (Finset.sum_mul _ _ _).symm
    _ ≤ A := by nlinarith

theorem norm_sum_le_of_card_bound (v : ι → W) {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ i, ‖v i‖ ≤ K / ((Fintype.card ι : ℝ) + 1)) : ‖∑ i, v i‖ ≤ K := by
  calc
    _ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, K / ((Fintype.card ι : ℝ) + 1) := Finset.sum_le_sum (fun i _ => hv i)
    _ = (Fintype.card ι : ℝ) * (K / ((Fintype.card ι : ℝ) + 1)) := by simp
    _ ≤ K := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (Fintype.card ι : ℝ) + 1)]
      nlinarith

theorem norm_blend_derivative_le (p : ι → ℝ) (v e : ι → W) {K : ℝ} (hK : 0 ≤ K)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    (hv : ∀ i, p i ≠ 0 → ‖v i‖ ≤ 4 * K)
    (he : ∀ i, ‖e i‖ ≤ K / ((Fintype.card ι : ℝ) + 1)) :
    ‖(∑ i, p i • v i) + ∑ i, e i‖ ≤ 5 * K := by
  calc
    _ ≤ ‖∑ i, p i • v i‖ + ‖∑ i, e i‖ := norm_add_le _ _
    _ ≤ 4 * K + K := add_le_add
      (norm_nonnegative_weighted_sum_le p v (by positivity) hp hs hv)
      (norm_sum_le_of_card_bound e hK he)
    _ = 5 * K := by ring

end WeightedEstimates

def finiteBlend {ι X : Type*} [Fintype ι] (p h : ι → X → ℝ) (f : X → ℝ) (x : X) : ℝ :=
  f x + ∑ i, p i x * (h i x - f x)

theorem finiteBlend_eq_sum_of_sum_eq_one {ι X : Type*} [Fintype ι]
    (p h : ι → X → ℝ) (f : X → ℝ) {x : X} (hp : ∑ i, p i x = 1) :
    finiteBlend p h f x = ∑ i, p i x * h i x := by
  simp only [finiteBlend, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
  ring

theorem finiteBlend_dist_le {ι X : Type*} [Fintype ι]
    (p h : ι → X → ℝ) (f : X → ℝ) (x : X) {ε : ℝ} (hε : 0 ≤ ε)
    (hp : ∀ i, 0 ≤ p i x) (hs : ∑ i, p i x ≤ 1)
    (hh : ∀ i, p i x ≠ 0 → dist (h i x) (f x) ≤ ε) :
    dist (finiteBlend p h f x) (f x) ≤ ε := by
  rw [dist_eq_norm]
  change ‖f x + ∑ i, p i x * (h i x - f x) - f x‖ ≤ ε
  rw [add_sub_cancel_left]
  have hb := norm_nonnegative_weighted_sum_le (fun i => p i x) (fun i => h i x - f x)
    hε hp hs (fun i hi => by simpa only [dist_eq_norm] using hh i hi)
  simpa only [smul_eq_mul] using hb

theorem finiteBlend_eventuallyEq_centered {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (p h : ι → X → ℝ) (f : X → ℝ) {K L : Set X} (hKL : K ⊆ interior L)
    (hs : ∀ x ∈ L, ∑ i, p i x = 1)
    (hc : ∀ x ∉ K, f =ᶠ[𝓝 x] fun _ => f x) (x : X) :
    finiteBlend p h f =ᶠ[𝓝 x] finiteBlend p h (fun _ => f x) := by
  by_cases hx : x ∈ K
  · filter_upwards [isOpen_interior.mem_nhds (hKL hx)] with y hy
    rw [finiteBlend_eq_sum_of_sum_eq_one p h f (hs y (interior_subset hy)),
      finiteBlend_eq_sum_of_sum_eq_one p h (fun _ => f x) (hs y (interior_subset hy))]
  · filter_upwards [hc x hx] with y hy
    simp only [finiteBlend, hy]

theorem finiteBlend_centered_contMDiff {ι : Type*} [Fintype ι] {L : Set M.Carrier}
    (p : SmoothPartitionOfUnity ι 𝓘(ℝ, ComplexVector n) M.Carrier L)
    (h : ι → M.Carrier → ℝ) (c : ℝ) :
    letI := manifold_realSmooth M
    (∀ i, ∀ x ∈ tsupport (p i), ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (h i) x) →
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (finiteBlend (fun i => p i) h (fun _ => c)) := by
  letI := manifold_realSmooth M
  intro hh
  have hsum := p.contMDiff_finsum_smul (g := fun i y => h i y - c)
    (fun i y hy => (hh i y hy).sub contMDiffAt_const)
  have hc : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ i, p i y * (h i y - c)) := by
    simpa only [finsum_eq_sum_of_fintype, smul_eq_mul] using hsum
  exact contMDiff_const.add hc

theorem finiteBlend_contMDiff {ι : Type*} [Fintype ι] {K L : Set M.Carrier}
    (p : SmoothPartitionOfUnity ι 𝓘(ℝ, ComplexVector n) M.Carrier L)
    (h : ι → M.Carrier → ℝ) (f : M.Carrier → ℝ) (hKL : K ⊆ interior L)
    (hc : ∀ x ∉ K, f =ᶠ[𝓝 x] fun _ => f x) :
    letI := manifold_realSmooth M
    (∀ i, ∀ x ∈ tsupport (p i), ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (h i) x) →
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (finiteBlend (fun i => p i) h f) := by
  letI := manifold_realSmooth M
  intro hh x
  have hs : ∀ y ∈ L, ∑ i, p i y = 1 := fun y hy => by
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hy
  exact (finiteBlend_centered_contMDiff p h (f x) hh).contMDiffAt.congr_of_eventuallyEq
    (finiteBlend_eventuallyEq_centered (fun i => p i) h f hKL hs hc x)


theorem realDifferential_finiteBlend_centered {ι : Type*} [Fintype ι]
    (g : SmoothMetric M) {L : Set M.Carrier}
    (p : SmoothPartitionOfUnity ι 𝓘(ℝ, ComplexVector n) M.Carrier L)
    (h : ι → M.Carrier → ℝ) (c : ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    (∀ i, ∀ y ∈ tsupport (p i), ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (h i) y) →
    realDifferential g (finiteBlend (fun i => p i) h (fun _ => c)) x =
      (∑ i, p i x • realDifferential g (h i) x) +
        ∑ i, (h i x - c) • realDifferential g (p i) x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hh
  let P : ι → M.Carrier → ℝ := fun i y => p i y * (h i y - c)
  have hP (i) : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (P i) := by
    have hs := p.contMDiff_smul (i := i) (g := fun y => h i y - c)
      (fun y hy => (hh i y hy).sub contMDiffAt_const)
    simpa only [smul_eq_mul] using hs
  have hPd : ∀ i ∈ (Finset.univ : Finset ι),
      MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (P i) x :=
    fun i _ => (hP i).mdifferentiable (by simp) x
  have hsum : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (fun y => ∑ i, P i y) x := by
    convert! MDifferentiableAt.sum hPd using 1
    funext y
    simp only [Finset.sum_apply]
  change realDifferential g (fun y => c + ∑ i, P i y) x = _
  rw [realDifferential_add g _ _ x mdifferentiableAt_const hsum,
    realDifferential_const, zero_add, realDifferential_finset_sum g Finset.univ P x hPd,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact realDifferential_mul_sub_const_supported g (p i) (h i) c x
    ((p i).contMDiff.mdifferentiable (by simp) x)
    (fun hx => (hh i x hx).mdifferentiableAt (by simp))

theorem realDifferential_finiteBlend {ι : Type*} [Fintype ι] (g : SmoothMetric M)
    {K L : Set M.Carrier} (p : SmoothPartitionOfUnity ι 𝓘(ℝ, ComplexVector n) M.Carrier L)
    (h : ι → M.Carrier → ℝ) (f : M.Carrier → ℝ) (hKL : K ⊆ interior L)
    (hc : ∀ x ∉ K, f =ᶠ[𝓝 x] fun _ => f x) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    (∀ i, ∀ y ∈ tsupport (p i), ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (h i) y) →
    realDifferential g (finiteBlend (fun i => p i) h f) x =
      (∑ i, p i x • realDifferential g (h i) x) +
        ∑ i, (h i x - f x) • realDifferential g (p i) x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hh
  have hs : ∀ y ∈ L, ∑ i, p i y = 1 := fun y hy => by
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hy
  rw [realDifferential_congr_of_eventuallyEq g
    (finiteBlend_eventuallyEq_centered (fun i => p i) h f hKL hs hc x)]
  exact realDifferential_finiteBlend_centered g p h (f x) x hh


/-- Global quantitative smoothing when all possible nonsmoothness lies in a
compact set. Local errors are chosen after the partition derivative bounds. -/
theorem exists_contMDiff_approx_of_locallyConstant_off_compact
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (κ : ℝ≥0) (hκ : 0 < κ)
    {K₀ : Set M.Carrier} (hK₀ : IsCompact K₀)
    (hc : ∀ x ∉ K₀, f =ᶠ[𝓝 x] fun _ => f x) {ε : ℝ} (hε : 0 < ε) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    letI := inducedMetricSpace g
    LipschitzWith κ f → ∃ H : M.Carrier → ℝ,
      ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ H ∧
      (∀ x, dist (H x) (f x) < ε) ∧
      ∀ x, ‖realDifferential g H x‖ ≤ 5 * (κ : ℝ) := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  letI := inducedMetricSpace g
  letI : LocallyCompactSpace M.Carrier := manifold_locallyCompact M
  classical
  intro hf
  obtain ⟨L, hL, hKL, _⟩ := exists_compact_between hK₀ isOpen_univ (Set.subset_univ _)
  obtain ⟨s, p, hpc, hpa⟩ := exists_finite_metric_smoothing_partition g hL
  choose B hB hb using fun i =>
    exists_bound_realDifferential_of_hasCompactSupport g (p i) (hpc i) (p i).contMDiff
  let N : ℝ := Fintype.card s
  let δ (i : s) : ℝ := min (ε / 2) ((κ : ℝ) / ((N + 1) * (B i + 1)))
  have hκr : 0 < (κ : ℝ) := hκ
  have hN : 0 < N + 1 := by dsimp [N]; positivity
  have hδ (i : s) : 0 < δ i := by
    apply lt_min (half_pos hε)
    exact div_pos hκr (mul_pos hN (by linarith [hB i]))
  choose h hhs hha hhd using fun i => hpa i f κ hf (δ i) (hδ i)
  let H := finiteBlend (fun i => p i) h f
  refine ⟨H, finiteBlend_contMDiff p h f hKL hc hhs, ?_, ?_⟩
  · intro x
    have hsum : ∑ i, p i x ≤ 1 := by
      simpa only [finsum_eq_sum_of_fintype] using p.sum_le_one x
    have he : dist (H x) (f x) ≤ ε / 2 := finiteBlend_dist_le (fun i => p i) h f x
      (half_pos hε).le (fun i => p.nonneg i x) hsum (fun i hi => by
        have hx : x ∈ tsupport (p i) := subset_closure hi
        exact (hha i x hx).le.trans (min_le_left _ _))
    exact he.trans_lt (half_lt_self hε)
  · intro x
    rw [realDifferential_finiteBlend g p h f hKL hc x hhs]
    have hsum : ∑ i, p i x ≤ 1 := by
      simpa only [finsum_eq_sum_of_fintype] using p.sum_le_one x
    apply norm_blend_derivative_le (fun i => p i x) (fun i => realDifferential g (h i) x)
      (fun i => (h i x - f x) • realDifferential g (p i) x) κ.coe_nonneg
      (fun i => p.nonneg i x) hsum
    · intro i hi
      exact hhd i x (subset_closure hi)
    · intro i
      by_cases hx : x ∈ tsupport (p i)
      · have hdiff : ‖h i x - f x‖ ≤ δ i := by
          simpa only [dist_eq_norm] using (hha i x hx).le
        calc
          _ ≤ ‖h i x - f x‖ * ‖realDifferential g (p i) x‖ := ContinuousLinearMap.opNorm_smul_le _ _
          _ ≤ δ i * B i := mul_le_mul hdiff (hb i x)
            (ContinuousLinearMap.opNorm_nonneg _) (hδ i).le
          _ ≤ ((κ : ℝ) / ((N + 1) * (B i + 1))) * B i :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (hB i).le
          _ = ((κ : ℝ) / (N + 1)) * (B i / (B i + 1)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
          _ ≤ ((κ : ℝ) / (N + 1)) * 1 :=
            mul_le_mul_of_nonneg_left ((div_le_one (by linarith [hB i])).mpr (by linarith))
              (div_nonneg κ.coe_nonneg hN.le)
          _ = (κ : ℝ) / ((Fintype.card s : ℝ) + 1) := mul_one _
      · rw [realDifferential_of_notMem_tsupport g hx, smul_zero, ContinuousLinearMap.opNorm_zero]
        exact div_nonneg κ.coe_nonneg (by positivity)


theorem realDifferential_comp_real (g : SmoothMetric M) (Φ : ℝ → ℝ)
    (H : M.Carrier → ℝ) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    DifferentiableAt ℝ Φ (H x) → MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) H x →
    realDifferential g (Φ ∘ H) x = (fderiv ℝ Φ (H x)) ∘L realDifferential g H x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hΦ hH
  change mvfderiv 𝓘(ℝ, ComplexVector n) (Φ ∘ H) x = _
  rw [mvfderiv_comp x hΦ.mdifferentiableAt hH, mvfderiv_eq_fderiv]
  rfl

theorem norm_realDifferential_comp_real_le (g : SmoothMetric M) (Φ : ℝ → ℝ)
    (H : M.Carrier → ℝ) (x : M.Carrier) (L : ℝ≥0) (hLip : LipschitzWith L Φ) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    DifferentiableAt ℝ Φ (H x) → MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) H x →
    ‖realDifferential g (Φ ∘ H) x‖ ≤ (L : ℝ) * ‖realDifferential g H x‖ := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hΦ hH
  rw [realDifferential_comp_real g Φ H x hΦ hH]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip)
      (ContinuousLinearMap.opNorm_nonneg _))

theorem isCompact_distanceCutoff_annulus (g : SmoothMetric M) (o : M.Carrier) (R : ℝ) :
    IsCompact {y : M.Carrier | R ≤ inducedDistance g.form o y ∧ inducedDistance g.form o y ≤ 2 * R} := by
  have hd : Continuous (fun y => inducedDistance g.form o y) := continuous_distFrom g o
  exact (isCompact_inducedDistance_sublevel g o (2 * R)).of_isClosed_subset
    ((isClosed_le continuous_const hd).inter (isClosed_le hd continuous_const))
    (fun y hy => hy.2)

theorem distanceCutoff_locallyConstant_off_annulus (g : SmoothMetric M) (o : M.Carrier)
    {R : ℝ} (hR : 0 < R) (y : M.Carrier)
    (hy : y ∉ {z : M.Carrier | R ≤ inducedDistance g.form o z ∧ inducedDistance g.form o z ≤ 2 * R}) :
    distanceCutoff g.form o R =ᶠ[𝓝 y] fun _ => distanceCutoff g.form o R y := by
  have hd : Continuous (fun z => inducedDistance g.form o z) := continuous_distFrom g o
  by_cases hinner : inducedDistance g.form o y < R
  · have hn : {z : M.Carrier | inducedDistance g.form o z < R} ∈ 𝓝 y :=
      hd.continuousAt.preimage_mem_nhds (Iio_mem_nhds hinner)
    filter_upwards [hn] with z hz
    rw [distanceCutoff_one g.form o z hR hz.le, distanceCutoff_one g.form o y hR hinner.le]
  · have houter : 2 * R < inducedDistance g.form o y :=
      lt_of_not_ge (fun hupper => hy ⟨le_of_not_gt hinner, hupper⟩)
    have hn : {z : M.Carrier | 2 * R < inducedDistance g.form o z} ∈ 𝓝 y :=
      hd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds houter)
    filter_upwards [hn] with z hz
    rw [distanceCutoff_zero g.form o z hR hz.le, distanceCutoff_zero g.form o y hR houter.le]

/-- A quantitative smooth cutoff with the ordinary differential norm measured
in the actual Riemannian tangent metric. -/
theorem exists_smooth_distance_cutoff_of_transition_lipschitz
    (g : SmoothMetric M) (o : M.Carrier) {R : ℝ} (hR : 0 < R)
    (L : ℝ≥0) (hLip : LipschitzWith L cutoffTransition) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    ∃ η : M.Carrier → ℝ,
      ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
      (∀ y, η y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ y, inducedDistance g.form o y ≤ R → η y = 1) ∧
      tsupport η ⊆ {y | inducedDistance g.form o y ≤ 2 * R} ∧
      ∀ y, ‖realDifferential g η y‖ ≤ (5 * (L : ℝ)) / R := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  letI := inducedMetricSpace g
  let κ := Real.toNNReal R⁻¹
  have hκ : 0 < κ := Real.toNNReal_pos.mpr (inv_pos.mpr hR)
  have hκcoe : (κ : ℝ) = R⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr hR.le)
  obtain ⟨H, hHs, hHa, hHd⟩ := exists_contMDiff_approx_of_locallyConstant_off_compact g
    (distanceCutoff g.form o R) κ hκ (isCompact_distanceCutoff_annulus g o R)
    (distanceCutoff_locallyConstant_off_annulus g o hR) (by norm_num : (0 : ℝ) < 1 / 8)
    (distanceCutoff_lipschitz g o hR)
  let η := cutoffTransition ∘ H
  have hηs : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η :=
    cutoffTransition_contDiff.contMDiff.comp hHs
  have hzero (y) (hy : 2 * R ≤ inducedDistance g.form o y) : η y = 0 := by
    have ha := hHa y
    rw [distanceCutoff_zero g.form o y hR hy, Real.dist_eq] at ha
    have hh : H y ≤ 1 / 4 := by linarith [(abs_lt.mp ha).2]
    exact cutoffTransition_zero hh
  have hsupport : tsupport η ⊆ {y | inducedDistance g.form o y ≤ 2 * R} := by
    apply closure_minimal _ (isCompact_inducedDistance_sublevel g o (2 * R)).isClosed
    intro y hy
    by_contra hn
    exact hy (hzero y (le_of_lt (lt_of_not_ge hn)))
  have hηc : HasCompactSupport η :=
    (isCompact_inducedDistance_sublevel g o (2 * R)).of_isClosed_subset
      (isClosed_tsupport _) hsupport
  refine ⟨η, hηs, smoothFn_of_contMDiff_real η hηs, hηc,
    fun y => cutoffTransition_mem (H y), ?_, hsupport, ?_⟩
  · intro y hy
    have ha := hHa y
    rw [distanceCutoff_one g.form o y hR hy, Real.dist_eq] at ha
    have hh : 3 / 4 ≤ H y := by linarith [(abs_lt.mp ha).1]
    exact cutoffTransition_one hh
  · intro y
    calc
      _ ≤ (L : ℝ) * ‖realDifferential g H y‖ := norm_realDifferential_comp_real_le
        g cutoffTransition H y L hLip (cutoffTransition_contDiff.differentiable (by simp) _)
        (hHs.mdifferentiable (by simp) y)
      _ ≤ (L : ℝ) * (5 * (κ : ℝ)) := mul_le_mul_of_nonneg_left (hHd y) L.coe_nonneg
      _ = (5 * (L : ℝ)) / R := by rw [hκcoe]; ring


/-- The cutoff constant is chosen before the manifold, metric, center and scale. -/
theorem exists_quantitative_smooth_distance_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ComplexManifold d) (g : SmoothMetric N) (o : N.Carrier)
      (R : ℝ), 0 < R →
      letI := manifold_realSmooth N
      letI : ∀ z : N.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector d) z) :=
        fun z => underlyingRealTangentNormedAddCommGroup g.form z
      letI : ∀ z : N.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector d) z) :=
        fun z => underlyingRealTangentInnerProductSpace g.form z
      ∃ η : N.Carrier → ℝ,
        ContMDiff 𝓘(ℝ, ComplexVector d) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
        (∀ y, η y ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ y, inducedDistance g.form o y ≤ R → η y = 1) ∧
        tsupport η ⊆ {y | inducedDistance g.form o y ≤ 2 * R} ∧
        ∀ y, ‖realDifferential g η y‖ ≤ C / R := by
  obtain ⟨L, hL, hLip⟩ := exists_cutoffTransition_lipschitz
  refine ⟨5 * (L : ℝ), mul_pos (by norm_num) hL, ?_⟩
  intro N g o R hR
  exact exists_smooth_distance_cutoff_of_transition_lipschitz g o hR L hLip



/-! Actual local geodesic energy conservation and original-distance control. -/

def chartChristoffelBilin (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  ∑ c, ∑ a, ∑ b, christoffel h x z c a b •
    (realCoordCLM a).smulRight ((realCoordCLM b).smulRight (realVec c))

theorem chartChristoffelBilin_apply (h : HermitianField M) (x : M.Carrier)
    (z u v : ComplexVector n) :
    chartChristoffelBilin h x z u v =
      ∑ c, (∑ a, ∑ b, christoffel h x z c a b * realCoord u a * realCoord v b) • realVec c := by
  simp only [chartChristoffelBilin, sum_apply, smul_apply, smulRight_apply,
    realCoordCLM_apply, smul_smul, Finset.sum_smul]

theorem chartGeodesicAcceleration_eq (h : HermitianField M) (x : M.Carrier)
    (z v : ComplexVector n) : chartGeodesicAcceleration h x z v =
      -chartChristoffelBilin h x z v v := by
  rw [chartChristoffelBilin_apply]
  rfl

theorem chartChristoffelBilin_symm (h : HermitianField M) (x : M.Carrier)
    (z u v : ComplexVector n) : chartChristoffelBilin h x z u v = chartChristoffelBilin h x z v u := by
  rw [chartChristoffelBilin_apply, chartChristoffelBilin_apply]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [christoffel_symm_lower h x z c b a]
  ring

theorem realCoord_realVec (a b : RIdx n) :
    realCoord (realVec a) b = if a = b then 1 else 0 := by
  rw [← realVec_basis_repr, ← realVec_basis_apply n a]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]

theorem chartChristoffelBilin_basis (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a b : RIdx n) :
    chartChristoffelBilin h x z (realVec a) (realVec b) =
      ∑ c, christoffel h x z c a b • realVec c := by
  rw [chartChristoffelBilin_apply]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [realCoord_realVec]

theorem realMetricInChart_basis (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    realMetricInChart h x z (realVec a) (realVec b) = realMetricFn h x z a b :=
  underlyingRealRiemannianMetric_frame h x z hz a b

theorem metricCompatibility_of_basis {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (Γ : E →L[ℝ] E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h : ∀ i j k, D (e i) (e j) (e k) = B (Γ (e i) (e j)) (e k) + B (e j) (Γ (e i) (e k)))
    (w u v : E) : D w u v = B (Γ w u) v + B u (Γ w v) := by
  have hthird (i j : ι) (q : E) :
      D (e i) (e j) q = B (Γ (e i) (e j)) q + B (e j) (Γ (e i) q) := by
    let L : E →L[ℝ] ℝ := D (e i) (e j) - B (Γ (e i) (e j)) - (B (e j)).comp (Γ (e i))
    have hL : L.toLinearMap = 0 := by
      apply e.ext
      intro k
      change D (e i) (e j) (e k) - B (Γ (e i) (e j)) (e k) - B (e j) (Γ (e i) (e k)) = 0
      linarith [h i j k]
    have ht := congrArg (fun A : E →ₗ[ℝ] ℝ => A q) hL
    change D (e i) (e j) q - B (Γ (e i) (e j)) q - B (e j) (Γ (e i) q) = 0 at ht
    linarith
  have hsecond (i : ι) (p q : E) :
      D (e i) p q = B (Γ (e i) p) q + B p (Γ (e i) q) := by
    let L : E →L[ℝ] ℝ := (D (e i)).flip q - (B.flip q).comp (Γ (e i)) - B.flip (Γ (e i) q)
    have hL : L.toLinearMap = 0 := by
      apply e.ext
      intro j
      change D (e i) (e j) q - B (Γ (e i) (e j)) q - B (e j) (Γ (e i) q) = 0
      linarith [hthird i j q]
    have ht := congrArg (fun A : E →ₗ[ℝ] ℝ => A p) hL
    change D (e i) p q - B (Γ (e i) p) q - B p (Γ (e i) q) = 0 at ht
    linarith
  let L : E →L[ℝ] ℝ := (D.flip u).flip v - (B.flip v).comp (Γ.flip u) - (B u).comp (Γ.flip v)
  have hL : L.toLinearMap = 0 := by
    apply e.ext
    intro i
    change D (e i) u v - B (Γ (e i) u) v - B u (Γ (e i) v) = 0
    linarith [hsecond i u v]
  have ht := congrArg (fun A : E →ₗ[ℝ] ℝ => A w) hL
  change D w u v - B (Γ w u) v - B u (Γ w v) = 0 at ht
  linarith

set_option synthInstance.maxHeartbeats 200000 in
theorem realMetricInChart_connection_compatibility (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (w u v : ComplexVector n) :
    (fderiv ℝ (realMetricInChart g.form x) z w) u v =
      realMetricInChart g.form x z (chartChristoffelBilin g.form x z w u) v +
        realMetricInChart g.form x z u (chartChristoffelBilin g.form x z w v) := by
  have hB := ((realMetricInChart_smooth g x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  apply metricCompatibility_of_basis (realVec_basis n) (realMetricInChart g.form x z)
    (chartChristoffelBilin g.form x z) (fderiv ℝ (realMetricInChart g.form x) z) _ w u v
  intro a b c
  simp only [realVec_basis_apply]
  rw [← fderiv_bilin_apply_const hB (realVec a) (realVec b) (realVec c)]
  have he : (fun t => realMetricInChart g.form x t (realVec b) (realVec c)) =ᶠ[𝓝 z]
      (fun t => realMetricFn g.form x t b c) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with t ht
    exact realMetricInChart_basis g.form x t ht b c
  rw [he.fderiv_eq, chartChristoffelBilin_basis, chartChristoffelBilin_basis]
  rw [map_sum, sum_apply, map_sum]
  simp only [map_smul, smul_apply, smul_eq_mul, realMetricInChart_basis g.form x z hz]
  have hh := congrFun (congrFun (metricDirectionalDerivative_eq_connection g x z hz a) b) c
  change rDeriv (fun t => realMetricFn g.form x t b c) z a = _ at hh
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix] at hh
  simpa only [rDeriv, mul_comm] using hh

def chartGeodesicEnergy (h : HermitianField M) (x : M.Carrier)
    (q : ComplexVector n × ComplexVector n) : ℝ := realMetricInChart h x q.1 q.2 q.2

theorem chartGeodesicEnergy_contDiffOn (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartGeodesicEnergy g.form x) (chartTarget x ×ˢ Set.univ) := by
  have hB := (realMetricInChart_smooth g x).comp contDiffOn_fst
    (show Set.MapsTo (fun q : ComplexVector n × ComplexVector n => q.1)
      (chartTarget x ×ˢ Set.univ) (chartTarget x) from fun _ hq => hq.1)
  exact (hB.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd

set_option synthInstance.maxHeartbeats 200000 in
theorem chartGeodesicEnergy_fderiv_spray (g : SmoothMetric M) (x : M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget x) :
    fderiv ℝ (chartGeodesicEnergy g.form x) q (chartGeodesicSpray g.form x q) = 0 := by
  have hB := ((realMetricInChart_smooth g x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hq)).differentiableAt (by simp)
  have hG := hB.hasFDerivAt.comp q (hasFDerivAt_fst (p := q))
  have hV := hasFDerivAt_snd (𝕜 := ℝ) (p := q)
  have hE := (hG.clm_apply hV).clm_apply hV
  change fderiv ℝ (fun p : ComplexVector n × ComplexVector n =>
    ((realMetricInChart g.form x ∘ Prod.fst) p) p.2 p.2) q (chartGeodesicSpray g.form x q) = 0
  rw [hE.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,
    Function.comp_apply, chartGeodesicSpray]
  change realMetricInChart g.form x q.1 q.2 (chartGeodesicAcceleration g.form x q.1 q.2) +
    (realMetricInChart g.form x q.1 (chartGeodesicAcceleration g.form x q.1 q.2) q.2 +
      fderiv ℝ (realMetricInChart g.form x) q.1 q.2 q.2 q.2) = 0
  rw [realMetricInChart_connection_compatibility g x q.1 hq q.2 q.2 q.2,
    chartGeodesicAcceleration_eq]
  simp only [map_neg, neg_apply]
  ring

theorem chartGeodesicEnergy_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray g.form x (η t)) t) :
    HasDerivAt (fun s => chartGeodesicEnergy g.form x (η s)) 0 t := by
  have hO : IsOpen (chartTarget x ×ˢ (Set.univ : Set (ComplexVector n))) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hE := ((chartGeodesicEnergy_contDiffOn g x).contDiffAt
    (hO.mem_nhds ⟨hz, Set.mem_univ _⟩)).differentiableAt (by simp)
  have hs := hE.hasFDerivAt.comp_hasDerivAt t hη
  rw [chartGeodesicEnergy_fderiv_spray g x (η t) hz] at hs
  exact hs

theorem chartGeodesicEnergy_constant (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {a b s t : ℝ}
    (hη : ∀ r ∈ Set.Ioo a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartGeodesicSpray g.form x (η r)) r)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    chartGeodesicEnergy g.form x (η s) = chartGeodesicEnergy g.form x (η t) := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero
    (f := fun r => chartGeodesicEnergy g.form x (η r)) (convex_Ioo a b).isPreconnected
  · intro r hr
    exact (chartGeodesicEnergy_hasDerivAt g x η (hη r hr).1 (hη r hr).2).differentiableAt.differentiableWithinAt
  · intro r hr
    exact (chartGeodesicEnergy_hasDerivAt g x η (hη r hr).1 (hη r hr).2).deriv
  · exact hs
  · exact ht

theorem chartGeodesicEnergy_eq_actual_speed_sq (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray g.form x (η t)) t) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    chartGeodesicEnergy g.form x (η t) =
      ‖realCurveVelocity (fun s => chartInv x (η s).1) t‖ ^ 2 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  rw [← real_inner_self_eq_norm_sq, realCurveVelocity_chartGeodesic g x η hz hη]
  rfl

theorem chartGeodesic_contDiffOn_Icc (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {a b : ℝ}
    (hη : ∀ r ∈ Set.Icc a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartGeodesicSpray g.form x (η r)) r) :
    ContDiffOn ℝ ∞ η (Set.Icc a b) := by
  have hf := (chartGeodesicSpray_contDiffOn g x).comp contDiffOn_snd
    (show Set.MapsTo Prod.snd (Set.Icc a b ×ˢ (chartTarget x ×ˢ Set.univ))
      (chartTarget x ×ˢ Set.univ) from fun _ hq => hq.2)
  exact ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := (⊤ : ℕ∞))
    (f := fun (_r : ℝ) (q : ComplexVector n × ComplexVector n) => chartGeodesicSpray g.form x q)
    (u := chartTarget x ×ˢ Set.univ) (α := η) hf
    (fun r hr => (hη r hr).2.hasDerivWithinAt)
    (fun r hr => ⟨(hη r hr).1, Set.mem_univ _⟩)

theorem chartGeodesic_curve_contMDiffOn_Icc (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {a b : ℝ}
    (hη : ∀ r ∈ Set.Icc a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartGeodesicSpray g.form x (η r)) r) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞
      (fun r => chartInv x (η r).1) (Set.Icc a b) := by
  letI := manifold_realSmooth M
  have hfst := contDiff_fst.comp_contDiffOn (chartGeodesic_contDiffOn_Icc g x η hη)
  exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) (n := ∞) x).comp
    hfst.contMDiffOn (fun r hr => (hη r hr).1)

theorem chartGeodesic_actual_speed_constant (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {a b s t : ℝ}
    (hη : ∀ r ∈ Set.Ioo a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartGeodesicSpray g.form x (η r)) r)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ‖realCurveVelocity (fun r => chartInv x (η r).1) s‖ =
      ‖realCurveVelocity (fun r => chartInv x (η r).1) t‖ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have he := chartGeodesicEnergy_constant g x η hη hs ht
  rw [chartGeodesicEnergy_eq_actual_speed_sq g x η (hη s hs).1 (hη s hs).2,
    chartGeodesicEnergy_eq_actual_speed_sq g x η (hη t ht).1 (hη t ht).2] at he
  nlinarith [norm_nonneg (realCurveVelocity (fun r => chartInv x (η r).1) s),
    norm_nonneg (realCurveVelocity (fun r => chartInv x (η r).1) t)]

theorem chartGeodesic_inducedDistance_le (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {a b s t : ℝ}
    (hη : ∀ r ∈ Set.Ioo a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartGeodesicSpray g.form x (η r)) r)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) (hst : s ≤ t) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    inducedDistance g.form (chartInv x (η s).1) (chartInv x (η t).1) ≤
      ‖realCurveVelocity (fun r => chartInv x (η r).1) s‖ * (t - s) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let γ := fun r => chartInv x (η r).1
  have hsub : Set.Icc s t ⊆ Set.Ioo a b :=
    fun r hr => ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
  have hγ := (chartGeodesic_curve_contMDiffOn_Icc g x η (fun r hr => hη r (hsub hr))).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hd : ENNReal.ofReal (inducedDistance g.form (γ s) (γ t)) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ s t := by
    rw [inducedDistance_eq_riemannianEDist g]
    exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hst
  have hlen : Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ s t =
      ENNReal.ofReal (‖realCurveVelocity γ s‖ * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have hconst : (fun r => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ r 1‖ₑ) =ᵐ[volume.restrict (Set.Icc s t)]
        (fun _ => ENNReal.ofReal ‖realCurveVelocity γ s‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      change ‖realCurveVelocity γ r‖ₑ = _
      rw [← ofReal_norm, chartGeodesic_actual_speed_constant g x η hη (hsub hr) hs]
    rw [lintegral_congr_ae hconst, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.ofReal_mul (norm_nonneg _)]
  rw [hlen] at hd
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hst))).mp hd



/-! Annular cutoffs reuse the same quantitative smoothing construction. -/

def radialAnnulusProfile (h : HermitianField M) (o : M.Carrier) (r s : ℝ) (y : M.Carrier) : ℝ :=
  clamp01 ((s - inducedDistance h o y) / (s - r))

theorem radialAnnulusProfile_mem (h : HermitianField M) (o y : M.Carrier) (r s : ℝ) :
    radialAnnulusProfile h o r s y ∈ Set.Icc (0 : ℝ) 1 := clamp01_mem _

theorem radialAnnulusProfile_one (h : HermitianField M) (o y : M.Carrier) {r s : ℝ}
    (hrs : r < s) (hy : inducedDistance h o y ≤ r) : radialAnnulusProfile h o r s y = 1 := by
  apply clamp01_eq_one
  apply (le_div_iff₀ (sub_pos.mpr hrs)).mpr
  linarith

theorem radialAnnulusProfile_zero (h : HermitianField M) (o y : M.Carrier) {r s : ℝ}
    (hrs : r < s) (hy : s ≤ inducedDistance h o y) : radialAnnulusProfile h o r s y = 0 := by
  apply clamp01_eq_zero
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) (sub_pos.mpr hrs).le

theorem radialAnnulusProfile_lipschitz (g : SmoothMetric M) (o : M.Carrier) {r s : ℝ} (hrs : r < s) :
    letI := inducedMetricSpace g
    LipschitzWith (Real.toNNReal (s - r)⁻¹) (radialAnnulusProfile g.form o r s) := by
  letI := inducedMetricSpace g
  have hg : 0 < s - r := sub_pos.mpr hrs
  have haff : LipschitzWith (Real.toNNReal (s - r)⁻¹) (fun t : ℝ => (s - t) / (s - r)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Real.dist_eq, Real.dist_eq]
    have he : (s - a) / (s - r) - (s - b) / (s - r) = (b - a) / (s - r) := by ring
    rw [he, abs_div, abs_of_pos hg, abs_sub_comm,
      Real.coe_toNNReal _ (inv_nonneg.mpr hg.le)]
    exact le_of_eq (by ring)
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hp := clamp01_lipschitz.dist_le_mul ((s - dist o y) / (s - r)) ((s - dist o z) / (s - r))
  simp only [NNReal.coe_one, one_mul] at hp
  have hd := (LipschitzWith.dist_right o).dist_le_mul y z
  simp only [NNReal.coe_one, one_mul] at hd
  exact (hp.trans (haff.dist_le_mul _ _)).trans
    (mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _))

theorem isCompact_radialAnnulusProfile_annulus (g : SmoothMetric M) (o : M.Carrier) (r s : ℝ) :
    IsCompact {y : M.Carrier | r ≤ inducedDistance g.form o y ∧ inducedDistance g.form o y ≤ s} := by
  have hd : Continuous (fun y => inducedDistance g.form o y) := continuous_distFrom g o
  exact (isCompact_inducedDistance_sublevel g o s).of_isClosed_subset
    ((isClosed_le continuous_const hd).inter (isClosed_le hd continuous_const)) (fun _ hy => hy.2)

theorem radialAnnulusProfile_locallyConstant_off_annulus (g : SmoothMetric M) (o : M.Carrier)
    {r s : ℝ} (hrs : r < s) (y : M.Carrier)
    (hy : y ∉ {z : M.Carrier | r ≤ inducedDistance g.form o z ∧ inducedDistance g.form o z ≤ s}) :
    radialAnnulusProfile g.form o r s =ᶠ[𝓝 y] fun _ => radialAnnulusProfile g.form o r s y := by
  have hd : Continuous (fun z => inducedDistance g.form o z) := continuous_distFrom g o
  by_cases hinner : inducedDistance g.form o y < r
  · have hn : {z : M.Carrier | inducedDistance g.form o z < r} ∈ 𝓝 y :=
      hd.continuousAt.preimage_mem_nhds (Iio_mem_nhds hinner)
    filter_upwards [hn] with z hz
    rw [radialAnnulusProfile_one g.form o z hrs hz.le, radialAnnulusProfile_one g.form o y hrs hinner.le]
  · have houter : s < inducedDistance g.form o y :=
      lt_of_not_ge (fun hupper => hy ⟨le_of_not_gt hinner, hupper⟩)
    have hn : {z : M.Carrier | s < inducedDistance g.form o z} ∈ 𝓝 y :=
      hd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds houter)
    filter_upwards [hn] with z hz
    rw [radialAnnulusProfile_zero g.form o z hrs hz.le, radialAnnulusProfile_zero g.form o y hrs houter.le]


theorem exists_smooth_annular_cutoff_of_transition_lipschitz
    (g : SmoothMetric M) (o : M.Carrier) {r R : ℝ} (hrR : r < R)
    (L : ℝ≥0) (hLip : LipschitzWith L cutoffTransition) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace g.form z
    ∃ η : M.Carrier → ℝ,
      ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
      (∀ y, η y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ y, inducedDistance g.form o y ≤ r → η y = 1) ∧
      tsupport η ⊆ {y | inducedDistance g.form o y < R} ∧
      ∀ y, ‖realDifferential g η y‖ ≤ (10 * (L : ℝ)) / (R - r) := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  letI := inducedMetricSpace g
  let S := (r + R) / 2
  have hrS : r < S := by dsimp [S]; linarith
  have hSR : S < R := by dsimp [S]; linarith
  let κ := Real.toNNReal (S - r)⁻¹
  have hκ : 0 < κ := Real.toNNReal_pos.mpr (inv_pos.mpr (sub_pos.mpr hrS))
  have hκcoe : (κ : ℝ) = (S - r)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr (sub_pos.mpr hrS).le)
  obtain ⟨H, hHs, hHa, hHd⟩ := exists_contMDiff_approx_of_locallyConstant_off_compact g
    (radialAnnulusProfile g.form o r S) κ hκ (isCompact_radialAnnulusProfile_annulus g o r S)
    (radialAnnulusProfile_locallyConstant_off_annulus g o hrS) (by norm_num : (0 : ℝ) < 1 / 8)
    (radialAnnulusProfile_lipschitz g o hrS)
  let η := cutoffTransition ∘ H
  have hηs : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η :=
    cutoffTransition_contDiff.contMDiff.comp hHs
  have hzero (y) (hy : S ≤ inducedDistance g.form o y) : η y = 0 := by
    have ha := hHa y
    rw [radialAnnulusProfile_zero g.form o y hrS hy, Real.dist_eq] at ha
    exact cutoffTransition_zero (by linarith [(abs_lt.mp ha).2])
  have hsupport : tsupport η ⊆ {y | inducedDistance g.form o y ≤ S} := by
    apply closure_minimal _ (isCompact_inducedDistance_sublevel g o S).isClosed
    intro y hy
    by_contra hn
    exact hy (hzero y (le_of_lt (lt_of_not_ge hn)))
  have hηc : HasCompactSupport η :=
    (isCompact_inducedDistance_sublevel g o S).of_isClosed_subset (isClosed_tsupport _) hsupport
  refine ⟨η, hηs, smoothFn_of_contMDiff_real η hηs, hηc,
    fun y => cutoffTransition_mem (H y), ?_, fun y hy => (hsupport hy).trans_lt hSR, ?_⟩
  · intro y hy
    have ha := hHa y
    rw [radialAnnulusProfile_one g.form o y hrS hy, Real.dist_eq] at ha
    exact cutoffTransition_one (by linarith [(abs_lt.mp ha).1])
  · intro y
    calc
      _ ≤ (L : ℝ) * ‖realDifferential g H y‖ := norm_realDifferential_comp_real_le
        g cutoffTransition H y L hLip (cutoffTransition_contDiff.differentiable (by simp) _)
        (hHs.mdifferentiable (by simp) y)
      _ ≤ (L : ℝ) * (5 * (κ : ℝ)) := mul_le_mul_of_nonneg_left (hHd y) L.coe_nonneg
      _ = (10 * (L : ℝ)) / (R - r) := by
        have hgap : S - r = (R - r) / 2 := by dsimp [S]; ring
        rw [hκcoe, hgap, inv_div]
        ring

theorem exists_quantitative_smooth_annular_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ComplexManifold d) (g : SmoothMetric N) (o : N.Carrier)
      (r R : ℝ), r < R →
      letI := manifold_realSmooth N
      letI : ∀ z : N.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector d) z) :=
        fun z => underlyingRealTangentNormedAddCommGroup g.form z
      letI : ∀ z : N.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector d) z) :=
        fun z => underlyingRealTangentInnerProductSpace g.form z
      ∃ η : N.Carrier → ℝ,
        ContMDiff 𝓘(ℝ, ComplexVector d) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
        (∀ y, η y ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ y, inducedDistance g.form o y ≤ r → η y = 1) ∧
        tsupport η ⊆ {y | inducedDistance g.form o y < R} ∧
        ∀ y, ‖realDifferential g η y‖ ≤ C / (R - r) := by
  obtain ⟨L, hL, hLip⟩ := exists_cutoffTransition_lipschitz
  refine ⟨10 * (L : ℝ), mul_pos (by norm_num) hL, ?_⟩
  intro N g o r R hrR
  exact exists_smooth_annular_cutoff_of_transition_lipschitz g o hrR L hLip



/-! Actual Levi--Civita coordinates for arbitrary local smooth vector fields. -/

theorem contMDiffAt_chartLift_of_contDiffAt {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (x y : M.Carrier) (hy : y ∈ (chartAt (ComplexVector n) x).source)
    {F : ComplexVector n → D} (hF : ContDiffAt ℝ ∞ F (chartPt x y)) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, D) ∞ (fun p => F (chartPt x p)) y := by
  letI := manifold_realSmooth M
  have hi : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ (chartPt x) y :=
    contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) hy
  exact hF.contMDiffAt.comp y hi

def realCoordinateVectorField (x : M.Carrier) (V : ComplexVector n → ComplexVector n) :
    ∀ y : M.Carrier, TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  letI := manifold_realSmooth M
  exact fun y => (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symm y (V (chartPt x y))

theorem realCoordinateVectorField_contMDiffAt (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source)
    (V : ComplexVector n → ComplexVector n) (hV : ContDiffAt ℝ ∞ V (chartPt x y)) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ComplexVector n) (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) ∞
      (fun p => (⟨p, realCoordinateVectorField x V p⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) y := by
  letI := manifold_realSmooth M
  let e := trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x
  have hbase : y ∈ e.baseSet := hy
  rw [e.contMDiffAt_section_iff hbase]
  apply (contMDiffAt_chartLift_of_contDiffAt x y hy hV).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hbase] with p hp
  change (e ⟨p, e.symm p (V (chartPt x p))⟩).2 = V (chartPt x p)
  simp [hp]

theorem realCoordinateVectorField_eq_sum (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) (V : ComplexVector n → ComplexVector n) :
    realCoordinateVectorField x V y =
      ∑ d, realCoord (V (chartPt x y)) d • realCoordinateField x (realVec d) y := by
  letI := manifold_realSmooth M
  let e := trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x
  have hbase : y ∈ e.baseSet := hy
  have hs := congrArg (e.symmL ℝ y) (sum_realCoord_realVec (V (chartPt x y)))
  rw [map_sum] at hs
  simp only [map_smul] at hs
  change e.symm y (V (chartPt x y)) =
    ∑ d, realCoord (V (chartPt x y)) d • e.symm y (realVec d)
  simpa only [e.symmL_apply hbase] using hs.symm

theorem mvfderiv_chartLift_of_contDiffAt (x : M.Carrier) (z v : ComplexVector n)
    (hz : z ∈ chartTarget x) {F : ComplexVector n → ℝ} (hF : ContDiffAt ℝ ∞ F z) :
    mvfderiv 𝓘(ℝ, ComplexVector n) (fun y => F (chartPt x y)) (chartInv x z)
      (realCoordinateField x v (chartInv x z)) = fderiv ℝ F z v := by
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have hpt : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  have hCF := contMDiffAt_chartLift_of_contDiffAt x (chartInv x z) hy (hpt.symm ▸ hF)
  rw [mvfderiv_realCoordinateField _ x z v hz (hCF.mdifferentiableAt (by simp))]
  have heq : (fun w => F (chartPt x (chartInv x w))) =ᶠ[𝓝 z] F := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact congrArg F ((extChartAt (ComplexModel n) x).right_inv hw)
  rw [heq.fderiv_eq]

theorem realCoord_fderiv_comp {V : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hV : DifferentiableAt ℝ V z) (u : ComplexVector n) (d : RIdx n) :
    fderiv ℝ (fun w => realCoord (V w) d) z u = realCoord (fderiv ℝ V z u) d := by
  have hc := (realCoordCLM d).hasFDerivAt.comp z hV.hasFDerivAt
  have hc' : HasFDerivAt (fun w => realCoord (V w) d)
      ((realCoordCLM d).comp (fderiv ℝ V z)) z :=
    hc.congr_of_eventuallyEq (Eventually.of_forall fun w => (realCoordCLM_apply d (V w)).symm)
  rw [hc'.fderiv, ContinuousLinearMap.comp_apply, realCoordCLM_apply]

def realFrameCLM (x y : M.Carrier) : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  letI := manifold_realSmooth M
  exact (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ y

theorem realFrameCLM_apply (x y : M.Carrier) (hy : y ∈ (chartAt (ComplexVector n) x).source)
    (v : ComplexVector n) : realFrameCLM x y v = realCoordinateField x v y := by
  letI := manifold_realSmooth M
  exact (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL_apply hy v

set_option maxHeartbeats 500000 in
theorem realLeviCivitaConnection_coordinateVectorField_basis (g : SmoothMetric M)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (V : ComplexVector n → ComplexVector n) (hV : ContDiffAt ℝ ∞ V z) (a : RIdx n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (realCoordinateVectorField x V) (chartInv x z)
      (realCoordinateField x (realVec a) (chartInv x z)) =
      realFrameCLM x (chartInv x z)
        (fderiv ℝ V z (realVec a) + chartChristoffelBilin g.form x z (realVec a) (V z)) := by
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection g
  let y := chartInv x z
  have hy : y ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv, y] using (extChartAt (ComplexModel n) x).map_target hz
  have hpt : chartPt x y = z := (extChartAt (ComplexModel n) x).right_inv hz
  let F : RIdx n → ComplexVector n → ℝ := fun d w => realCoord (V w) d
  let C : RIdx n → M.Carrier → ℝ := fun d p => F d (chartPt x p)
  have hF (d) : ContDiffAt ℝ ∞ (F d) z :=
    (contDiff_realCoord d).contDiffAt.comp z hV
  have hC (d) : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (C d) y := by
    apply (contMDiffAt_chartLift_of_contDiffAt x y hy _).mdifferentiableAt (by simp)
    simpa only [hpt] using hF d
  have hW : MDifferentiableAt 𝓘(ℝ, ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (fun p => (⟨p, realCoordinateVectorField x V p⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) y := by
    apply (realCoordinateVectorField_contMDiffAt x y hy V _).mdifferentiableAt (by simp)
    simpa only [hpt] using hV
  let W := ∑ d, C d • realCoordinateField x (realVec d)
  have hWs : MDifferentiableAt 𝓘(ℝ, ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (fun p => (⟨p, W p⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) y := by
    convert! MDifferentiableAt.sum_section (s := Finset.univ) (fun d _ =>
      (hC d).smul_section ((realCoordinateField_contMDiffAt x y (realVec d) hy).mdifferentiableAt (by simp))) using 1
    simp only [W, Finset.sum_apply, Pi.smul_apply]
  have heq : realCoordinateVectorField x V =ᶠ[𝓝 y] W := by
    filter_upwards [(chartAt (ComplexVector n) x).open_source.mem_nhds hy] with p hp
    rw [realCoordinateVectorField_eq_sum x p hp V]
    simp only [W, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro d _
    rfl
  have hloc := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hW hWs Filter.univ_mem heq
  change cov (realCoordinateVectorField x V) y _ = _
  rw [hloc]
  have hsum := realLeviCivitaConnection_frame_sum g x y hy a C hC
  change cov W y (realCoordinateField x (realVec a) y) = _ at hsum
  rw [hsum]
  have hd (d) : mvfderiv 𝓘(ℝ, ComplexVector n) (C d) y
      (realCoordinateField x (realVec a) y) = realCoord (fderiv ℝ V z (realVec a)) d := by
    rw [mvfderiv_chartLift_of_contDiffAt x z (realVec a) hz (hF d)]
    exact realCoord_fderiv_comp (hV.differentiableAt (by simp)) (realVec a) d
  have hΓ : chartChristoffelBilin g.form x z (realVec a) (V z) =
      ∑ d, realCoord (V z) d • (∑ e, christoffel g.form x z e a d • realVec e) := by
    conv_lhs => rw [← sum_realCoord_realVec (V z)]
    rw [map_sum]
    simp only [map_smul, chartChristoffelBilin_basis]
  simp only [C, F, hpt, hd]
  conv_rhs => rw [map_add, ← sum_realCoord_realVec (fderiv ℝ V z (realVec a)), hΓ]
  simp only [map_sum, map_smul]
  simp only [realFrameCLM_apply x (chartInv x z) hy]
  rw [Finset.sum_add_distrib, add_comm]

theorem realLeviCivitaConnection_coordinateVectorField (g : SmoothMetric M)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (V : ComplexVector n → ComplexVector n) (hV : ContDiffAt ℝ ∞ V z) (u : ComplexVector n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (realCoordinateVectorField x V) (chartInv x z)
      (realCoordinateField x u (chartInv x z)) =
      realFrameCLM x (chartInv x z) (fderiv ℝ V z u + chartChristoffelBilin g.form x z u (V z)) := by
  letI := manifold_realSmooth M
  let y := chartInv x z
  have hy : y ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv, y] using (extChartAt (ComplexModel n) x).map_target hz
  let cov := realLeviCivitaConnection g
  let A := (cov (realCoordinateVectorField x V) y).comp (realFrameCLM x y)
  let B := (realFrameCLM x y).comp (fderiv ℝ V z + (chartChristoffelBilin g.form x z).flip (V z))
  have hAB : A.toLinearMap = B.toLinearMap := by
    apply (realVec_basis n).ext
    intro a
    change cov (realCoordinateVectorField x V) y (realFrameCLM x y (realVec_basis n a)) =
      realFrameCLM x y (fderiv ℝ V z (realVec_basis n a) + chartChristoffelBilin g.form x z (realVec_basis n a) (V z))
    rw [realVec_basis_apply, realFrameCLM_apply x y hy]
    exact realLeviCivitaConnection_coordinateVectorField_basis g x z hz V hV a
  have he := congrArg (fun L : ComplexVector n →ₗ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y => L u) hAB
  change cov (realCoordinateVectorField x V) y (realFrameCLM x y u) =
    realFrameCLM x y (fderiv ℝ V z u + chartChristoffelBilin g.form x z u (V z)) at he
  rw [realFrameCLM_apply x y hy u] at he
  exact he

theorem realLeviCivitaConnection_coordinateVectorField_realChartVec (g : SmoothMetric M)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (V : ComplexVector n → ComplexVector n) (hV : ContDiffAt ℝ ∞ V z) (u : ComplexVector n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (realCoordinateVectorField x V) (chartInv x z) (realChartVec x z u) =
      realChartVec x z (fderiv ℝ V z u + chartChristoffelBilin g.form x z u (V z)) := by
  letI := manifold_realSmooth M
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have he := realLeviCivitaConnection_coordinateVectorField g x z hz V hV u
  rw [realFrameCLM_apply x (chartInv x z) hy,
    realCoordinateField_eq_realChartVec x z u hz,
    realCoordinateField_eq_realChartVec x z _ hz] at he
  exact he



/-! Coordinate invariance of the actual Levi--Civita geodesic spray. -/

def realTangentCoords (x y : M.Carrier) : TangentSpace 𝓘(ℝ, ComplexVector n) y →L[ℝ] ComplexVector n := by
  letI := manifold_realSmooth M
  exact (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt ℝ y

theorem realTangentCoords_eq_mvfderiv (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    realTangentCoords x y = mvfderiv 𝓘(ℝ, ComplexVector n) (chartPt x) y := by
  letI := manifold_realSmooth M
  ext v
  unfold realTangentCoords
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy]
  rfl

theorem realTangentCoords_realFrameCLM (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) (v : ComplexVector n) :
    realTangentCoords x y (realFrameCLM x y v) = v := by
  letI := manifold_realSmooth M
  exact (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).continuousLinearMapAt_symmL hy v

theorem realFrameCLM_realTangentCoords (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) y) : realFrameCLM x y (realTangentCoords x y v) = v := by
  letI := manifold_realSmooth M
  exact (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL_continuousLinearMapAt hy v

theorem mvfderiv_realCoordinateField_target {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (F : M.Carrier → D) (x : M.Carrier) (z v : ComplexVector n) (hz : z ∈ chartTarget x)
    (hF : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, D) F (chartInv x z)) :
    mvfderiv 𝓘(ℝ, ComplexVector n) F (chartInv x z) (realCoordinateField x v (chartInv x z)) =
      fderiv ℝ (fun w => F (chartInv x w)) z v := by
  letI := manifold_realSmooth M
  have hi := (contMDiffAt_chartInv_real x z hz).mdifferentiableAt (by simp)
  rw [realCoordinateField_eq_realChartVec x z v hz]
  have hc := mvfderiv_comp_apply z hF hi ((NormedSpace.fromTangentSpace z).symm v)
  rw [mvfderiv_eq_fderiv] at hc
  exact hc.symm

def realChartChange (a b : M.Carrier) (z : ComplexVector n) : ComplexVector n := chartPt b (chartInv a z)

theorem realChartChange_contDiffAt (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    ContDiffAt ℝ ∞ (realChartChange a b) z :=
  (chartTransition_contDiffAt a b hz hy).restrict_scalars ℝ

theorem realChartChange_fderiv (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v : ComplexVector n) : fderiv ℝ (realChartChange a b) z v =
      realTangentCoords b (chartInv a z) (realCoordinateField a v (chartInv a z)) := by
  letI := manifold_realSmooth M
  have hb : chartInv a z ∈ (chartAt (ComplexVector n) b).source := by
    simpa only [extChartAt_source] using hy
  have hF : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (chartPt b) (chartInv a z) :=
    mdifferentiableAt_extChartAt (I := 𝓘(ℝ, ComplexVector n)) hb
  rw [realTangentCoords_eq_mvfderiv b (chartInv a z) hb]
  exact (mvfderiv_realCoordinateField_target (chartPt b) a z v hz hF).symm

theorem realChartChange_inverse_apply (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    realChartChange b a (realChartChange a b z) = z := by
  have hb : chartInv b (chartPt b (chartInv a z)) = chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  unfold realChartChange
  rw [hb]
  exact (extChartAt (ComplexModel n) a).right_inv hz

theorem realLeviCivitaConnection_constFrame (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (u v : ComplexVector n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (realCoordinateField x v) (chartInv x z)
      (realCoordinateField x u (chartInv x z)) =
      realFrameCLM x (chartInv x z) (chartChristoffelBilin g.form x z u v) := by
  letI := manifold_realSmooth M
  have he := realLeviCivitaConnection_coordinateVectorField g x z hz (fun _ => v) contDiffAt_const u
  change realLeviCivitaConnection g (realCoordinateField x v) (chartInv x z)
    (realCoordinateField x u (chartInv x z)) = realFrameCLM x (chartInv x z)
      (fderiv ℝ (fun _ : ComplexVector n => v) z u + chartChristoffelBilin g.form x z u v) at he
  simpa only [fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_add] using he

theorem realTangentCoords_realCoordinateField (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) (v : ComplexVector n) :
    realTangentCoords x y (realCoordinateField x v y) = v := by
  rw [← realFrameCLM_apply x y hy v]
  exact realTangentCoords_realFrameCLM x y hy v

theorem realChartChange_frame (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v : ComplexVector n) : realFrameCLM b (chartInv a z) (fderiv ℝ (realChartChange a b) z v) =
      realCoordinateField a v (chartInv a z) := by
  have hb : chartInv a z ∈ (chartAt (ComplexVector n) b).source := by
    simpa only [extChartAt_source] using hy
  rw [realChartChange_fderiv a b hz hy v]
  exact realFrameCLM_realTangentCoords b (chartInv a z) hb _

theorem realChartChange_fderiv_inverse (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v : ComplexVector n) :
    fderiv ℝ (realChartChange b a) (realChartChange a b z) (fderiv ℝ (realChartChange a b) z v) = v := by
  have hzB : realChartChange a b z ∈ chartTarget b := (extChartAt (ComplexModel n) b).map_source hy
  have hbInv : chartInv b (realChartChange a b z) = chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  have hA : chartInv a z ∈ (extChartAt (ComplexModel n) a).source :=
    (extChartAt (ComplexModel n) a).map_target hz
  have hA' : chartInv b (realChartChange a b z) ∈ (extChartAt (ComplexModel n) a).source := by
    simpa only [hbInv] using hA
  have hAr : chartInv a z ∈ (chartAt (ComplexVector n) a).source := by
    simpa only [extChartAt_source] using hA
  have hBr : chartInv a z ∈ (chartAt (ComplexVector n) b).source := by
    simpa only [extChartAt_source] using hy
  have hd := realChartChange_fderiv b a hzB hA' (fderiv ℝ (realChartChange a b) z v)
  rw [hbInv, ← realFrameCLM_apply b (chartInv a z) hBr,
    realChartChange_frame a b hz hy v, realTangentCoords_realCoordinateField a (chartInv a z) hAr] at hd
  exact hd

def realChartChange_pushVector (a b : M.Carrier) (w : ComplexVector n) (q : ComplexVector n) : ComplexVector n :=
  fderiv ℝ (realChartChange a b) (realChartChange b a q) w

theorem realChartChange_pushVector_contDiffAt (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (w : ComplexVector n) : ContDiffAt ℝ ∞ (realChartChange_pushVector a b w) (realChartChange a b z) := by
  have hzB : realChartChange a b z ∈ chartTarget b := (extChartAt (ComplexModel n) b).map_source hy
  have hbInv : chartInv b (realChartChange a b z) = chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  have hA : chartInv b (realChartChange a b z) ∈ (extChartAt (ComplexModel n) a).source := by
    rw [hbInv]
    exact (extChartAt (ComplexModel n) a).map_target hz
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) z :=
    (realChartChange_contDiffAt a b hz hy).fderiv_right (by simp)
  have hF : ContDiffAt ℝ ∞ (fun q => fderiv ℝ (realChartChange a b) q w)
      (realChartChange b a (realChartChange a b z)) := by
    rw [realChartChange_inverse_apply a b hz hy]
    exact hD.clm_apply contDiffAt_const
  exact hF.comp _ (realChartChange_contDiffAt b a hzB hA)

theorem realChartChange_pushVector_fderiv (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (u w : ComplexVector n) :
    fderiv ℝ (realChartChange_pushVector a b w) (realChartChange a b z)
      (fderiv ℝ (realChartChange a b) z u) =
        fderiv ℝ (fderiv ℝ (realChartChange a b)) z u w := by
  have hzB : realChartChange a b z ∈ chartTarget b := (extChartAt (ComplexModel n) b).map_source hy
  have hbInv : chartInv b (realChartChange a b z) = chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  have hA : chartInv b (realChartChange a b z) ∈ (extChartAt (ComplexModel n) a).source := by
    rw [hbInv]
    exact (extChartAt (ComplexModel n) a).map_target hz
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) z :=
    (realChartChange_contDiffAt a b hz hy).fderiv_right (by simp)
  let F := fun q => fderiv ℝ (realChartChange a b) q w
  have hF : DifferentiableAt ℝ F (realChartChange b a (realChartChange a b z)) := by
    rw [realChartChange_inverse_apply a b hz hy]
    exact (hD.clm_apply contDiffAt_const).differentiableAt (by simp)
  have hτ := (realChartChange_contDiffAt b a hzB hA).differentiableAt (by simp)
  change fderiv ℝ (F ∘ realChartChange b a) (realChartChange a b z)
    (fderiv ℝ (realChartChange a b) z u) = _
  rw [fderiv_comp _ hF hτ, ContinuousLinearMap.comp_apply,
    realChartChange_inverse_apply a b hz hy, realChartChange_fderiv_inverse a b hz hy u]
  change fderiv ℝ (fun q => fderiv ℝ (realChartChange a b) q w) z u = _
  rw [fderiv_clm_apply (hD.differentiableAt (by simp)) (differentiableAt_const w)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    map_zero, zero_add]

theorem realCoordinateField_eq_pushVector_eventually (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (w : ComplexVector n) : realCoordinateField a w =ᶠ[𝓝 (chartInv a z)]
      realCoordinateVectorField b (realChartChange_pushVector a b w) := by
  letI := manifold_realSmooth M
  have hA : chartInv a z ∈ (extChartAt (ComplexModel n) a).source :=
    (extChartAt (ComplexModel n) a).map_target hz
  filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) a).mem_nhds hA,
    (isOpen_extChartAt_source (I := ComplexModel n) b).mem_nhds hy] with p hpA hpB
  have hzA : chartPt a p ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source hpA
  have heA : chartInv a (chartPt a p) = p := (extChartAt (ComplexModel n) a).left_inv hpA
  have hBp : chartInv a (chartPt a p) ∈ (extChartAt (ComplexModel n) b).source := by
    rw [heA]
    exact hpB
  have hfr := realChartChange_frame a b hzA hBp w
  rw [heA] at hfr
  have heB : chartInv b (chartPt b p) = p := (extChartAt (ComplexModel n) b).left_inv hpB
  have hpt : realChartChange b a (chartPt b p) = chartPt a p := by
    change chartPt a (chartInv b (chartPt b p)) = chartPt a p
    rw [heB]
  have hpBr : p ∈ (chartAt (ComplexVector n) b).source := by
    simpa only [extChartAt_source] using hpB
  change realCoordinateField a w p = realCoordinateField b
    (fderiv ℝ (realChartChange a b) (realChartChange b a (chartPt b p)) w) p
  rw [hpt, ← realFrameCLM_apply b p hpBr]
  exact hfr.symm

set_option maxHeartbeats 800000 in
theorem chartChristoffelBilin_change (g : SmoothMetric M) (a b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) (u w : ComplexVector n) :
    fderiv ℝ (realChartChange a b) z (chartChristoffelBilin g.form a z u w) =
      fderiv ℝ (fderiv ℝ (realChartChange a b)) z u w +
        chartChristoffelBilin g.form b (realChartChange a b z)
          (fderiv ℝ (realChartChange a b) z u) (fderiv ℝ (realChartChange a b) z w) := by
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection g
  let p := chartInv a z
  let zB := realChartChange a b z
  have hA : p ∈ (extChartAt (ComplexModel n) a).source := (extChartAt (ComplexModel n) a).map_target hz
  have hAr : p ∈ (chartAt (ComplexVector n) a).source := by simpa only [extChartAt_source] using hA
  have hBr : p ∈ (chartAt (ComplexVector n) b).source := by simpa only [extChartAt_source] using hy
  have hzB : zB ∈ chartTarget b := (extChartAt (ComplexModel n) b).map_source hy
  have hbInv : chartInv b zB = p := (extChartAt (ComplexModel n) b).left_inv hy
  have hV := realChartChange_pushVector_contDiffAt a b hz hy w
  have hWA := (realCoordinateField_contMDiffAt a p w hAr).mdifferentiableAt (by simp)
  have hWB := (realCoordinateVectorField_contMDiffAt b p hBr
    (realChartChange_pushVector a b w) hV).mdifferentiableAt (by simp)
  have hloc := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hWA hWB Filter.univ_mem
    (realCoordinateField_eq_pushVector_eventually a b hz hy w)
  have hAconn := realLeviCivitaConnection_constFrame g a z hz u w
  have hBconn := realLeviCivitaConnection_coordinateVectorField g b zB hzB
    (realChartChange_pushVector a b w) hV (fderiv ℝ (realChartChange a b) z u)
  rw [hbInv] at hBconn
  have hVp : realChartChange_pushVector a b w zB = fderiv ℝ (realChartChange a b) z w := by
    unfold realChartChange_pushVector
    rw [realChartChange_inverse_apply a b hz hy]
  rw [realChartChange_pushVector_fderiv a b hz hy u w, hVp] at hBconn
  have hU : realCoordinateField a u p =
      realCoordinateField b (fderiv ℝ (realChartChange a b) z u) p := by
    have hh := realChartChange_frame a b hz hy u
    rw [realFrameCLM_apply b (chartInv a z) hBr] at hh
    exact hh.symm
  have hconn : realFrameCLM a p (chartChristoffelBilin g.form a z u w) =
      realFrameCLM b p (fderiv ℝ (fderiv ℝ (realChartChange a b)) z u w +
        chartChristoffelBilin g.form b zB
          (fderiv ℝ (realChartChange a b) z u) (fderiv ℝ (realChartChange a b) z w)) := by
    rw [← hAconn, hloc, hU]
    exact hBconn
  have he := congrArg (realTangentCoords b p) hconn
  rw [realFrameCLM_apply a p hAr, realTangentCoords_realFrameCLM b p hBr,
    ← realChartChange_fderiv a b hz hy (chartChristoffelBilin g.form a z u w)] at he
  exact he

def realTangentChartChange (a b : M.Carrier) (q : ComplexVector n × ComplexVector n) :
    ComplexVector n × ComplexVector n :=
  (realChartChange a b q.1, fderiv ℝ (realChartChange a b) q.1 q.2)

theorem realTangentChartChange_contDiffAt (a b : M.Carrier) (q : ComplexVector n × ComplexVector n)
    (hq : q.1 ∈ chartTarget a) (hy : chartInv a q.1 ∈ (extChartAt (ComplexModel n) b).source) :
    ContDiffAt ℝ ∞ (realTangentChartChange a b) q := by
  have hψ := realChartChange_contDiffAt a b hq hy
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) q.1 := hψ.fderiv_right (by simp)
  exact (hψ.comp q contDiffAt_fst).prodMk ((hD.comp q contDiffAt_fst).clm_apply contDiffAt_snd)

theorem realTangentChartChange_inverse_apply (a b : M.Carrier) (q : ComplexVector n × ComplexVector n)
    (hq : q.1 ∈ chartTarget a) (hy : chartInv a q.1 ∈ (extChartAt (ComplexModel n) b).source) :
    realTangentChartChange b a (realTangentChartChange a b q) = q := by
  apply Prod.ext
  · exact realChartChange_inverse_apply a b hq hy
  · exact realChartChange_fderiv_inverse a b hq hy q.2

set_option maxHeartbeats 500000 in
theorem realTangentChartChange_fderiv_spray (g : SmoothMetric M) (a b : M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget a)
    (hy : chartInv a q.1 ∈ (extChartAt (ComplexModel n) b).source) :
    fderiv ℝ (realTangentChartChange a b) q (chartGeodesicSpray g.form a q) =
      chartGeodesicSpray g.form b (realTangentChartChange a b q) := by
  have hψ := realChartChange_contDiffAt a b hq hy
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) q.1 := hψ.fderiv_right (by simp)
  have hF := (hψ.differentiableAt (by simp)).hasFDerivAt.comp q (hasFDerivAt_fst (p := q))
  have hV := ((hD.differentiableAt (by simp)).hasFDerivAt.comp q
    (hasFDerivAt_fst (p := q))).clm_apply (hasFDerivAt_snd (p := q))
  have hJet := hF.prodMk hV
  change fderiv ℝ (fun p : ComplexVector n × ComplexVector n =>
    ((realChartChange a b ∘ Prod.fst) p, ((fderiv ℝ (realChartChange a b) ∘ Prod.fst) p) p.2)) q
      (chartGeodesicSpray g.form a q) = _
  rw [hJet.fderiv]
  change (fderiv ℝ (realChartChange a b) q.1 q.2,
    fderiv ℝ (realChartChange a b) q.1 (chartGeodesicAcceleration g.form a q.1 q.2) +
      fderiv ℝ (fderiv ℝ (realChartChange a b)) q.1 q.2 q.2) =
    (fderiv ℝ (realChartChange a b) q.1 q.2,
      chartGeodesicAcceleration g.form b (realChartChange a b q.1) (fderiv ℝ (realChartChange a b) q.1 q.2))
  apply Prod.ext
  · rfl
  · rw [chartGeodesicAcceleration_eq, chartGeodesicAcceleration_eq, map_neg,
      chartChristoffelBilin_change g a b hq hy q.2 q.2]
    abel



/-! Actual tangent-bundle charts and the global physical kinetic energy. -/

def realPhaseModel (n : ℕ) : ModelWithCorners ℝ (ComplexVector n × ComplexVector n)
    (ModelProd (ComplexVector n) (ComplexVector n)) := 𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)

def realPhaseChart (x : M.Carrier) (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    ComplexVector n × ComplexVector n := (chartPt x q.proj, realTangentCoords x q.proj q.2)

def realPhasePoint (x : M.Carrier) (q : ComplexVector n × ComplexVector n) :
    TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier :=
  ⟨chartInv x q.1, realFrameCLM x (chartInv x q.1) q.2⟩

theorem realPhaseChart_source (p q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    q ∈ (extChartAt (realPhaseModel n) p).source ↔ q.proj ∈ (chartAt (ComplexVector n) p.proj).source := by
  letI := manifold_realSmooth M
  simpa only [extChartAt_source] using TangentBundle.mem_chart_source_iff (I := 𝓘(ℝ, ComplexVector n)) q p

theorem realPhaseChart_eq_extChartAt (p q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hq : q.proj ∈ (chartAt (ComplexVector n) p.proj).source) :
    letI := manifold_realSmooth M
    extChartAt (realPhaseModel n) p q = realPhaseChart p.proj q := by
  letI := manifold_realSmooth M
  let e := trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) p.proj
  have hb : q.proj ∈ e.baseSet := hq
  have hqs : q ∈ e.source := e.mem_source.mpr hb
  change extChartAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) p q = _
  rw [FiberBundle.extChartAt]
  change (chartPt p.proj (e q).1, (e q).2) =
    (chartPt p.proj q.proj, e.continuousLinearMapAt ℝ q.proj q.2)
  rw [e.coe_fst hqs]
  apply Prod.ext
  · rfl
  · exact (e.continuousLinearMapAt_apply_of_mem (R := ℝ) hb q.2).symm

theorem realPhaseChart_realPhasePoint (x : M.Carrier) (q : ComplexVector n × ComplexVector n)
    (hq : q.1 ∈ chartTarget x) : realPhaseChart x (realPhasePoint x q) = q := by
  have hs : chartInv x q.1 ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hq
  apply Prod.ext
  · exact (extChartAt (ComplexModel n) x).right_inv hq
  · exact realTangentCoords_realFrameCLM x (chartInv x q.1) hs q.2

theorem realPhasePoint_eq_extChartAt_symm (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget p.proj) :
    letI := manifold_realSmooth M
    (extChartAt (realPhaseModel n) p).symm q = realPhasePoint p.proj q := by
  letI := manifold_realSmooth M
  have hs : chartInv p.proj q.1 ∈ (chartAt (ComplexVector n) p.proj).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) p.proj).map_target hq
  have hps : realPhasePoint p.proj q ∈ (extChartAt (realPhaseModel n) p).source :=
    (realPhaseChart_source p (realPhasePoint p.proj q)).mpr hs
  have hcode : extChartAt (realPhaseModel n) p (realPhasePoint p.proj q) = q :=
    (realPhaseChart_eq_extChartAt p (realPhasePoint p.proj q) hs).trans (realPhaseChart_realPhasePoint p.proj q hq)
  have he := (extChartAt (realPhaseModel n) p).left_inv hps
  rw [hcode] at he
  exact he

theorem realPhaseChart_change (pA pB : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget pA.proj)
    (hB : chartInv pA.proj q.1 ∈ (extChartAt (ComplexModel n) pB.proj).source) :
    letI := manifold_realSmooth M
    extChartAt (realPhaseModel n) pB ((extChartAt (realPhaseModel n) pA).symm q) =
      realTangentChartChange pA.proj pB.proj q := by
  letI := manifold_realSmooth M
  have hAr : chartInv pA.proj q.1 ∈ (chartAt (ComplexVector n) pA.proj).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) pA.proj).map_target hq
  have hBr : chartInv pA.proj q.1 ∈ (chartAt (ComplexVector n) pB.proj).source := by
    simpa only [extChartAt_source] using hB
  rw [realPhasePoint_eq_extChartAt_symm pA q hq,
    realPhaseChart_eq_extChartAt pB (realPhasePoint pA.proj q) hBr]
  apply Prod.ext
  · rfl
  · change realTangentCoords pB.proj (chartInv pA.proj q.1)
      (realFrameCLM pA.proj (chartInv pA.proj q.1) q.2) = _
    rw [realFrameCLM_apply pA.proj (chartInv pA.proj q.1) hAr]
    exact (realChartChange_fderiv pA.proj pB.proj hq hB q.2).symm

theorem realPhaseModel_boundaryless (n : ℕ) : ModelWithCorners.Boundaryless (realPhaseModel n) := by
  change ModelWithCorners.Boundaryless (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
  infer_instance

theorem realPhaseChart_target (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (q : ComplexVector n × ComplexVector n) :
    letI := manifold_realSmooth M
    q ∈ (extChartAt (realPhaseModel n) p).target ↔ q.1 ∈ chartTarget p.proj := by
  letI := manifold_realSmooth M
  change q ∈ (extChartAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) p).target ↔ _
  rw [FiberBundle.extChartAt_target]
  constructor
  · intro hq
    exact hq.1.1
  · intro hq
    refine ⟨⟨hq, ?_⟩, Set.mem_univ _⟩
    have hs : chartInv p.proj q.1 ∈ (chartAt (ComplexVector n) p.proj).source := by
      simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) p.proj).map_target hq
    exact hs

def realTangentEnergy (h : HermitianField M) (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : ℝ :=
  (underlyingRealRiemannianMetric h).inner q.proj q.2 q.2

theorem realTangentEnergy_nonneg (h : HermitianField M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : 0 ≤ realTangentEnergy h q := by
  by_cases hq : q.2 = 0
  · simp only [realTangentEnergy, hq, map_zero, zero_apply, le_refl]
  · exact ((underlyingRealRiemannianMetric h).pos q.proj q.2 hq).le

theorem realTangentEnergy_eq_norm_sq (h : HermitianField M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup h y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace h y
    realTangentEnergy h q = ‖q.2‖ ^ 2 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  rw [← real_inner_self_eq_norm_sq]
  rfl

theorem realTangentEnergy_contMDiff (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    ContMDiff (realPhaseModel n) 𝓘(ℝ, ℝ) ∞ (realTangentEnergy g.form) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  letI := realRiemannianBundle_contMDiff g
  have hv : ContMDiff (realPhaseModel n) (realPhaseModel n) ∞
      (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q) := contMDiff_id
  have hs := ContMDiff.inner_bundle (IB := 𝓘(ℝ, ComplexVector n))
    (b := fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q.proj)
    (v := fun q => q.2) (w := fun q => q.2) hv hv
  exact hs

theorem realTangentEnergy_realPhasePoint (h : HermitianField M) (x : M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget x) :
    realTangentEnergy h (realPhasePoint x q) = chartGeodesicEnergy h x q := by
  have hs : chartInv x q.1 ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hq
  change (underlyingRealRiemannianMetric h).inner (chartInv x q.1)
    (realFrameCLM x (chartInv x q.1) q.2) (realFrameCLM x (chartInv x q.1) q.2) = _
  rw [realFrameCLM_apply x (chartInv x q.1) hs, realCoordinateField_eq_realChartVec x q.1 q.2 hq]
  rfl


end Yau.LeafProofs.L12Aux
