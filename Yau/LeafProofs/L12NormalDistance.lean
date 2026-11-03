import Yau.LeafProofs.L12ExponentialVolume

/-! Actual normal-coordinate minimality for the original length distance.
The regularized physical radius and genuine Riemannian FTC estimate
handle the center and every hypothetical shortcut without exceptions. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

/-- Actual normal coordinates have a C1 inverse throughout an original
length-distance ball, not merely at the center. -/
theorem exists_realExponential_inverseC1_ball (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    ∃ e : OpenPartialHomeomorph (ComplexVector n) M.Carrier,
      (0 : ComplexVector n) ∈ e.source ∧ e 0 = x ∧
      Set.EqOn e (realNormalExponentialMap g x) e.source ∧
      ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e e.source ∧
      ∃ δ > (0 : ℝ), {y | inducedDistance g.form x y < δ} ⊆ e.target ∧
        ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e.symm
          {y | inducedDistance g.form x y < δ} := by
  letI := manifold_realSmooth M
  letI := inducedMetricSpace g
  obtain ⟨e, h0, hex, heq, hforward, hinverse⟩ := exists_realExponential_normalCoordinates g x
  have ht : x ∈ e.target := by
    rw [← hex]
    exact e.map_source h0
  have hC : ∀ᶠ y in 𝓝 x,
      ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e.symm y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ (∞ : ℕ∞ω))).mp hinverse
  have hN : ∀ᶠ y in 𝓝 x, y ∈ e.target ∧
      ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e.symm y := by
    filter_upwards [e.open_target.mem_nhds ht, hC] with y hy hcy
    exact ⟨hy, hcy⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hN
  have hmem {y : M.Carrier} (hy : inducedDistance g.form x y < δ) : y ∈ Metric.ball x δ := by
    change dist y x < δ
    rw [dist_comm]
    exact hy
  refine ⟨e, h0, hex, heq, hforward, δ, hδ, ?_, ?_⟩
  · intro y hy
    exact (hball (hmem hy)).1
  · intro y hy
    exact (hball (hmem hy)).2.contMDiffWithinAt

/-- A regularized physical normal radius, smooth even at the center. -/
def realSmoothNormalRadius (g : SmoothMetric M) (x : M.Carrier) (η : ℝ)
    (v : ComplexVector n) : ℝ := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  exact Real.sqrt (‖realFrameCLM x x v‖ ^ 2 + η ^ 2)

theorem realSmoothNormalRadius_pos (g : SmoothMetric M) (x : M.Carrier)
    {η : ℝ} (hη : 0 < η) (v : ComplexVector n) : 0 < realSmoothNormalRadius g x η v := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg ‖realFrameCLM x x v‖, sq_pos_of_pos hη]

theorem realSmoothNormalRadius_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    {η : ℝ} (hη : 0 < η) {a : ℝ → ComplexVector n} {a' : ComplexVector n} {t : ℝ}
    (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => realSmoothNormalRadius g x η (a s))
      (realMetricInChart g.form x (chartPt x x) (a t) a' / realSmoothNormalRadius g x η (a t)) t := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  have hv : HasDerivAt (fun s => realFrameCLM x x (a s)) (realFrameCLM x x a') t :=
    (realFrameCLM x x).hasFDerivAt.comp_hasDerivAt t ha
  have hp : 0 < ‖realFrameCLM x x (a t)‖ ^ 2 + η ^ 2 := by
    nlinarith [sq_nonneg ‖realFrameCLM x x (a t)‖, sq_pos_of_pos hη]
  have hs := (hv.norm_sq.add_const (η ^ 2)).sqrt hp.ne'
  rw [realMetricInChart_self_frame]
  convert hs using 1
  · rfl
  · change _ / realSmoothNormalRadius g x η (a t) =
      (2 * (underlyingRealRiemannianMetric g.form).inner x
        (realFrameCLM x x (a t)) (realFrameCLM x x a')) /
        (2 * realSmoothNormalRadius g x η (a t))
    field_simp [(realSmoothNormalRadius_pos g x hη (a t)).ne']
    <;> ring

theorem realSmoothNormalRadius_derivative_le_exp_speed (g : SmoothMetric M) (x : M.Carrier)
    {η : ℝ} (hη : 0 < η) (v w : ComplexVector n) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    |realMetricInChart g.form x (chartPt x x) v w / realSmoothNormalRadius g x η v| ≤
      ‖realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
        (fderiv ℝ (realExponentialEndpointCoordinates g x v) v w)‖ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hr := realSmoothNormalRadius_pos g x hη v
  have hnorm : ‖realFrameCLM x x v‖ ≤ realSmoothNormalRadius g x η v := by
    change ‖realFrameCLM x x v‖ ≤ Real.sqrt (‖realFrameCLM x x v‖ ^ 2 + η ^ 2)
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg η]
  rw [abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  have h := realExponential_gaussLemma_speed_bound g x v w
  exact h.trans (by
    nlinarith [norm_nonneg (realFrameCLM (realNormalExponentialMap g x v)
      (realNormalExponentialMap g x v) (fderiv ℝ (realExponentialEndpointCoordinates g x v) v w))])

theorem realCurveVelocity_coords_of_hasDerivAt (f : ℝ → M.Carrier) (t : ℝ) (x : M.Carrier)
    (v : ComplexVector n) (hx : f t ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) f t →
    HasDerivAt (fun s => chartPt x (f s)) v t →
    realTangentCoords x (f t) (realCurveVelocity f t) = v := by
  letI := manifold_realSmooth M
  intro hf hd
  have h := realTangentCoords_mfderiv f t x hx (1 : ℝ) hf
  change realTangentCoords x (f t) (realCurveVelocity f t) =
    fderiv ℝ (fun s => chartPt x (f s)) t 1 at h
  rw [hd.hasFDerivAt.fderiv] at h
  simpa using h

theorem realNorm_of_totalSpace_eq (g : SmoothMetric M) {x y : M.Carrier}
    {u : TangentSpace 𝓘(ℝ, ComplexVector n) x} {v : TangentSpace 𝓘(ℝ, ComplexVector n) y}
    (h : (⟨x, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨y, v⟩) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    ‖u‖ = ‖v‖ := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  have hp := realMetric_pairing_of_totalSpace_eq g.form h h
  change ⟪u, u⟫_ℝ = ⟪v, v⟫_ℝ at hp
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hp
  nlinarith [norm_nonneg u, norm_nonneg v]

theorem realSmoothNormalRadius_contDiff (g : SmoothMetric M) (x : M.Carrier)
    {η : ℝ} (hη : 0 < η) : ContDiff ℝ 1 (realSmoothNormalRadius g x η) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  have h : ContDiff ℝ 1 (fun v : ComplexVector n => ‖realFrameCLM x x v‖ ^ 2 + η ^ 2) :=
    ((realFrameCLM x x).contDiff.norm_sq ℝ).add contDiff_const
  change ContDiff ℝ 1 (fun v : ComplexVector n => Real.sqrt (‖realFrameCLM x x v‖ ^ 2 + η ^ 2))
  apply h.sqrt
  intro v
  have hp : 0 < ‖realFrameCLM x x v‖ ^ 2 + η ^ 2 := by
    nlinarith [sq_nonneg ‖realFrameCLM x x v‖, sq_pos_of_pos hη]
  exact hp.ne'

/-- A curve expressed in actual normal coordinates has the expected
actual velocity, as an equality in the genuine tangent bundle. -/
theorem realCurveVelocity_of_normalCoordinates (g : SmoothMetric M) (x : M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : Set.EqOn e (realNormalExponentialMap g x) e.source)
    (β : ℝ → M.Carrier) (t : ℝ) (hy : β t ∈ e.target) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β t →
    ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e.symm (β t) →
    let a := fun s => e.symm (β s)
    (⟨β t, realCurveVelocity β t⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) =
      ⟨realNormalExponentialMap g x (a t),
        realFrameCLM (realNormalExponentialMap g x (a t)) (realNormalExponentialMap g x (a t))
          (fderiv ℝ (realExponentialEndpointCoordinates g x (a t)) (a t) (deriv a t))⟩ := by
  letI := manifold_realSmooth M
  intro hβ hi a
  have haM : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 a t := hi.comp t hβ
  have ha : HasDerivAt a (deriv a t) t :=
    (haM.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hpoint (s : ℝ) (hs : β s ∈ e.target) : realNormalExponentialMap g x (a s) = β s :=
    (he (e.map_target hs)).symm.trans (e.right_inv hs)
  let y := realNormalExponentialMap g x (a t)
  have hN : ∀ᶠ s in 𝓝 t, β s ∈ e.target :=
    hβ.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hy)
  have hcoord : HasDerivAt (fun s => chartPt y (β s))
      (fderiv ℝ (realExponentialEndpointCoordinates g x (a t)) (a t) (deriv a t)) t := by
    have h := (realExponentialEndpointCoordinates_contDiffAt g x (a t)).differentiableAt (by simp)
    have hc := h.hasFDerivAt.comp_hasDerivAt t ha
    apply hc.congr_of_eventuallyEq
    filter_upwards [hN] with s hs
    change chartPt y (β s) = chartPt y (realNormalExponentialMap g x (a s))
    rw [hpoint s hs]
  have hsrc : β t ∈ (chartAt (ComplexVector n) y).source := by
    rw [← hpoint t hy]
    exact mem_chart_source _ _
  apply realTangentPoint_eq_of_coords (hpoint t hy).symm hsrc
  rw [realCurveVelocity_coords_of_hasDerivAt β t y _ hsrc (hβ.mdifferentiableAt (by simp)) hcoord,
    realTangentCoords_realFrameCLM y y (mem_chart_source _ _)]

theorem realSmoothNormalRadius_inverse_curve_bound (g : SmoothMetric M) (x : M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : Set.EqOn e (realNormalExponentialMap g x) e.source)
    {η : ℝ} (hη : 0 < η) (β : ℝ → M.Carrier) (t : ℝ) (hy : β t ∈ e.target) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β t →
    ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e.symm (β t) →
    let a := fun s => e.symm (β s)
    HasDerivAt (fun s => realSmoothNormalRadius g x η (a s))
      (realMetricInChart g.form x (chartPt x x) (a t) (deriv a t) /
        realSmoothNormalRadius g x η (a t)) t ∧
      |realMetricInChart g.form x (chartPt x x) (a t) (deriv a t) /
        realSmoothNormalRadius g x η (a t)| ≤ ‖realCurveVelocity β t‖ := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hβ hi a
  have ha : HasDerivAt a (deriv a t) t :=
    ((hi.comp t hβ).contDiffAt.differentiableAt (by simp)).hasDerivAt
  refine ⟨realSmoothNormalRadius_hasDerivAt g x hη ha, ?_⟩
  have hv := realCurveVelocity_of_normalCoordinates g x e he β t hy hβ hi
  have hn := realNorm_of_totalSpace_eq g hv
  rw [hn]
  exact realSmoothNormalRadius_derivative_le_exp_speed g x hη (a t) (deriv a t)

/-- The regularized normal radius satisfies the genuine Riemannian
path-length inequality for every C1 curve staying in valid normal coordinates. -/
theorem realSmoothNormalRadius_sub_le_pathELength (g : SmoothMetric M) (x : M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : Set.EqOn e (realNormalExponentialMap g x) e.source)
    {η : ℝ} (hη : 0 < η) (β : ℝ → M.Carrier) (a b : ℝ) (hab : a ≤ b) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β →
    (∀ t ∈ Set.Icc a b, β t ∈ e.target) →
    (∀ t ∈ Set.Icc a b, ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e.symm (β t)) →
    ENNReal.ofReal (realSmoothNormalRadius g x η (e.symm (β b)) -
      realSmoothNormalRadius g x η (e.symm (β a))) ≤
        Manifold.pathELength 𝓘(ℝ, ComplexVector n) β a b := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  intro hβ htarget hi
  let H := fun t => realSmoothNormalRadius g x η (e.symm (β t))
  have hHC : ContDiffOn ℝ 1 H (Set.Icc a b) := by
    intro t ht
    have hlocal := ((hi t ht).comp t hβ.contMDiffAt).contDiffAt
    exact ((realSmoothNormalRadius_contDiff g x hη).contDiffAt.comp t hlocal).contDiffWithinAt
  have hFTC := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hHC hab
  have hbound : (∫⁻ t in Set.Icc a b, ‖deriv H t‖ₑ) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) β a b := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    obtain ⟨hd, hb⟩ := realSmoothNormalRadius_inverse_curve_bound g x e he hη β t
      (htarget t ht) hβ.contMDiffAt (hi t ht)
    rw [← hd.deriv] at hb
    change ‖deriv H t‖ₑ ≤ ‖realCurveVelocity β t‖ₑ
    simpa only [← ofReal_norm, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal hb
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    (by simpa only [← ofReal_norm, Real.norm_eq_abs, H] using hFTC.trans hbound)

/-- Original length distance equals the physical normal radius on a
ball where the actual inverse exponential chart is C1. -/
theorem realExponential_normalCoordinates_distance (g : SmoothMetric M) (x : M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (h0 : (0 : ComplexVector n) ∈ e.source) (hex : e 0 = x)
    (he : Set.EqOn e (realNormalExponentialMap g x) e.source) {δ : ℝ} (hδ : 0 < δ)
    (htarget : {y | inducedDistance g.form x y < δ} ⊆ e.target) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e.symm
      {y | inducedDistance g.form x y < δ} →
    ∀ y : M.Carrier, inducedDistance g.form x y < δ →
      inducedDistance g.form x y = ‖realFrameCLM x x (e.symm y)‖ := by
  letI := manifold_realSmooth M
  letI := inducedMetricSpace g
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hi y hy
  have hpoint : realNormalExponentialMap g x (e.symm y) = y :=
    (he (e.map_target (htarget hy))).symm.trans (e.right_inv (htarget hy))
  have hupper : inducedDistance g.form x y ≤ ‖realFrameCLM x x (e.symm y)‖ := by
    have h := inducedDistance_realExponentialMap_le g x (realFrameCLM x x (e.symm y))
    change inducedDistance g.form x (realNormalExponentialMap g x (e.symm y)) ≤ _ at h
    rwa [hpoint] at h
  apply le_antisymm hupper
  by_contra! hsmall
  let r := ‖realFrameCLM x x (e.symm y)‖
  obtain ⟨a, hda, harδ⟩ := exists_between (lt_min hsmall hy)
  have har : a < r := harδ.trans_le (min_le_left _ _)
  have haδ : a < δ := harδ.trans_le (min_le_right _ _)
  have hdnonneg : 0 ≤ inducedDistance g.form x y := by
    change 0 ≤ dist x y
    exact dist_nonneg
  have ha : 0 < a := hdnonneg.trans_lt hda
  have hnear : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y < ENNReal.ofReal a := by
    rw [← inducedDistance_eq_riemannianEDist g]
    exact (ENNReal.ofReal_lt_ofReal_iff ha).mpr hda
  obtain ⟨β, hβ0, hβ1, hβ, hlen, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hnear zero_lt_one
  have hinside (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : inducedDistance g.form x (β t) < δ := by
    have hD : ENNReal.ofReal (inducedDistance g.form x (β t)) ≤
        Manifold.pathELength 𝓘(ℝ, ComplexVector n) β 0 t := by
      rw [inducedDistance_eq_riemannianEDist g]
      exact Manifold.riemannianEDist_le_pathELength hβ.contMDiffOn hβ0 rfl ht.1
    have hmon : Manifold.pathELength 𝓘(ℝ, ComplexVector n) β 0 t ≤
        Manifold.pathELength 𝓘(ℝ, ComplexVector n) β 0 1 :=
      Manifold.pathELength_mono le_rfl ht.2
    exact ((ENNReal.ofReal_lt_ofReal_iff ha).mp ((hD.trans hmon).trans_lt hlen)).trans haδ
  have hopen : IsOpen {z | inducedDistance g.form x z < δ} :=
    isOpen_lt (continuous_const.dist continuous_id) continuous_const
  let η := (r - a) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hFTC := realSmoothNormalRadius_sub_le_pathELength g x e he hη β 0 1 zero_le_one
    hβ (fun t ht => htarget (hinside t ht))
    (fun t ht => (hi (β t) (hinside t ht)).contMDiffAt (hopen.mem_nhds (hinside t ht)))
  have hxinv : e.symm x = 0 := by rw [← hex, e.left_inv h0]
  have hR0 : realSmoothNormalRadius g x η (e.symm (β 0)) = η := by
    rw [hβ0, hxinv]
    simp only [realSmoothNormalRadius, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
    exact Real.sqrt_sq hη.le
  have hR1 : r ≤ realSmoothNormalRadius g x η (e.symm (β 1)) := by
    rw [hβ1]
    change r ≤ Real.sqrt (r ^ 2 + η ^ 2)
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg η]
  have hR : a < realSmoothNormalRadius g x η (e.symm (β 1)) -
      realSmoothNormalRadius g x η (e.symm (β 0)) := by
    rw [hR0]
    dsimp only [η] at hη ⊢
    linarith
  have hLT := (ENNReal.ofReal_lt_ofReal_iff (ha.trans hR)).mpr hR
  exact (not_lt_of_ge hFTC) (hlen.trans hLT)

/-- Every sufficiently close point is reached by a genuine radial
geodesic whose physical initial norm equals the original length distance. -/
theorem exists_local_minimizing_realExponential (g : SmoothMetric M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    ∃ ρ > (0 : ℝ), ∀ y : M.Carrier, inducedDistance g.form x y < ρ →
      ∃ v : TangentSpace 𝓘(ℝ, ComplexVector n) x,
        realExponentialMap g x v = y ∧ ‖v‖ = inducedDistance g.form x y := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  obtain ⟨e, h0, hex, heq, hforward, ρ, hρ, htarget, hi⟩ := exists_realExponential_inverseC1_ball g x
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  refine ⟨realFrameCLM x x (e.symm y), ?_, ?_⟩
  · exact (heq (e.map_target (htarget hy))).symm.trans (e.right_inv (htarget hy))
  · exact (realExponential_normalCoordinates_distance g x e h0 hex heq hρ htarget hi y hy).symm

end Yau.LeafProofs.L12Aux
