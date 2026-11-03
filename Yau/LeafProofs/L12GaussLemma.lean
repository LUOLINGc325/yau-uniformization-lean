import Yau.LeafProofs.L12JacobiCurvature

/-! Gauss's lemma for the actual exponential, derived from genuine
initial-velocity variations, curvature symmetry, and metric compatibility. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

theorem chartCurvatureVector_self (h : HermitianField M) (x : M.Carrier)
    (z u w : ComplexVector n) : chartCurvatureVector h x z u u w = 0 := by
  simp only [chartCurvatureVector, sub_self, zero_add]

theorem chartCurvaturePairing_velocity_zero (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (T u : ComplexVector n) :
    realMetricInChart g.form x z T (chartCurvatureVector g.form x z u T T) = 0 := by
  rw [realMetricInChart_symm, chartJacobiCurvature_pairing_symm g x z hz T u T,
    chartCurvatureVector_self, map_zero, ContinuousLinearMap.zero_apply]

/-- Pairing of the actual radial velocity with the actual initial-velocity
Jacobi field, in their genuine common tangent fiber. -/
def realRadialJacobiPairing (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) : ℝ :=
  (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g p t).proj
    (realGeodesicFlow g p t).2 (realGeodesicJacobiField g p w t)

def realRadialJacobiPairingFirstTerm (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) : ℝ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let q := realGeodesicFlow g p t
  let z := extChartAt (realPhaseModel n) q q
  let a := fderiv ℝ (realVelocityPhaseCoordinates g p t) p.2 w
  exact realMetricInChart g.form q.proj z.1 z.2
    (a.2 + chartChristoffelBilin g.form q.proj z.1 z.2 a.1)

theorem realRadialJacobiPairing_in_chart (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (x : M.Carrier) (t : ℝ)
    (hx : (realGeodesicFlow g p t).proj ∈ (chartAt (ComplexVector n) x).source) :
    realRadialJacobiPairing g p w t =
      realMetricInChart g.form x (chartPt x (realGeodesicFlow g p t).proj)
        (realTangentCoords x (realGeodesicFlow g p t).proj (realGeodesicFlow g p t).2)
        (realTangentCoords x (realGeodesicFlow g p t).proj (realGeodesicJacobiField g p w t)) :=
  (realMetricInChart_tangentCoords g.form x (realGeodesicFlow g p t).proj hx _ _).symm

/-- The first radial variation has locally constant derivative, by the
actual Jacobi equation and curvature skew symmetry. -/
theorem exists_realRadialJacobiPairing_local_derivative (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t₀ : ℝ) :
    letI := manifold_realSmooth M
    ∃ ε > (0 : ℝ), ∃ D : ℝ → ℝ,
      D 0 = realRadialJacobiPairingFirstTerm g p w t₀ ∧
      ∀ τ ∈ Set.Ioo (-ε) ε,
        HasDerivAt (realRadialJacobiPairing g p w) (D τ) (t₀ + τ) ∧ HasDerivAt D 0 τ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let p₀ := realGeodesicFlow g p t₀
  let x := p₀.proj
  let z₀ := extChartAt (realPhaseModel n) p₀ p₀
  let B := fderiv ℝ (realVelocityPhaseCoordinates g p t₀) p.2
  obtain ⟨ε, hε, V, hV₀, hmodel⟩ := exists_realGeodesicJacobi_shifted_model g p t₀
  let η := realGeodesicChartFlow g p₀ z₀
  let a := B w
  let W := fun τ => V τ a
  let b := fun τ => (η τ).2
  let D := fun τ => realMetricInChart g.form x (η τ).1 (b τ)
    (chartVariationCovDeriv g.form x η W τ)
  have hcode (τ : ℝ) (hτ : τ ∈ Set.Ioo (-ε) ε) :
      η τ = realPhaseChart x (realGeodesicFlow g p (t₀ + τ)) :=
    realGeodesicChartFlow_shifted_eq_realPhaseChart g p t₀ τ (hmodel τ hτ).2.2.2.1
  have hbase (τ : ℝ) (hτ : τ ∈ Set.Ioo (-ε) ε) :
      (realGeodesicFlow g p (t₀ + τ)).proj ∈ (chartAt (ComplexVector n) x).source :=
    (realPhaseChart_source p₀ _).mp (hmodel τ hτ).2.2.2.1
  have hscalar (τ : ℝ) (hτ : τ ∈ Set.Ioo (-ε) ε) :
      realRadialJacobiPairing g p w (t₀ + τ) =
        realMetricInChart g.form x (η τ).1 (b τ) (W τ).1 := by
    rw [realRadialJacobiPairing_in_chart g p w x _ (hbase τ hτ),
      (hmodel τ hτ).2.2.2.2.2 w, hcode τ hτ]
    dsimp only [b]
    rw [hcode τ hτ]
    rfl
  have hη₀ : η 0 = z₀ := by
    dsimp only [η]
    rw [realGeodesicChartFlow_at_center, realGeodesicFlow_zero]
  have hW₀ : W 0 = a := by
    dsimp only [W]
    rw [hV₀, ContinuousLinearMap.id_apply]
  have hD₀ : D 0 = realRadialJacobiPairingFirstTerm g p w t₀ := by
    dsimp only [D, chartVariationCovDeriv, b]
    rw [hη₀, hW₀]
    rfl
  refine ⟨ε, hε, D, hD₀, ?_⟩
  intro τ hτ
  rcases hmodel τ hτ with ⟨hη, hV, hpos, hsrc, hphase, hcoords⟩
  have hW : HasDerivAt W ((fderiv ℝ (chartGeodesicSpray g.form x) (η τ)) (W τ)) τ :=
    chartGeodesicVariation_column_hasDerivAt g x η V a hV
  have hb : HasDerivAt b (-chartChristoffelBilin g.form x (η τ).1 (η τ).2 (b τ)) τ := by
    have h := (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt τ hη
    have h' : HasDerivAt (fun s => (η s).2)
        (chartGeodesicAcceleration g.form x (η τ).1 (η τ).2) τ := h
    simpa only [chartGeodesicAcceleration_eq] using h'
  have hpair := chartVariation_parallelPair_hasDerivAt g x η W b hpos hη hW hb
  have hactualShift : HasDerivAt (fun s => realRadialJacobiPairing g p w (t₀ + s)) (D τ) τ := by
    apply hpair.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs
    exact hscalar s hs
  have hsecond := chartVariation_covParallelPair_hasDerivAt g x η W b hpos hη hW hb
  have hcurv : realMetricInChart g.form x (η τ).1 (b τ)
      (chartCurvatureVector g.form x (η τ).1 (W τ).1 (η τ).2 (η τ).2) = 0 :=
    chartCurvaturePairing_velocity_zero g x (η τ).1 hpos (η τ).2 (W τ).1
  rw [hcurv, neg_zero] at hsecond
  exact ⟨hasDerivAt_of_comp_const_add t₀ τ hactualShift, hsecond⟩

theorem realRadialJacobiPairing_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    HasDerivAt (realRadialJacobiPairing g p w) (realRadialJacobiPairingFirstTerm g p w t) t := by
  letI := manifold_realSmooth M
  obtain ⟨ε, hε, D, hD₀, hD⟩ := exists_realRadialJacobiPairing_local_derivative g p w t
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  simpa only [add_zero, hD₀] using (hD 0 h0).1

theorem realRadialJacobiPairingFirstTerm_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    HasDerivAt (realRadialJacobiPairingFirstTerm g p w) 0 t := by
  letI := manifold_realSmooth M
  obtain ⟨ε, hε, D, hD₀, hD⟩ := exists_realRadialJacobiPairing_local_derivative g p w t
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have heq : (fun τ => realRadialJacobiPairingFirstTerm g p w (t + τ)) =ᶠ[𝓝 0] D := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with τ hτ
    exact (realRadialJacobiPairing_hasDerivAt g p w (t + τ)).unique (hD τ hτ).1
  have hs := heq.hasDerivAt_iff.mpr (hD 0 h0).2
  have hglobal : HasDerivAt (realRadialJacobiPairingFirstTerm g p w) 0 (t + 0) :=
    hasDerivAt_of_comp_const_add t 0 hs
  simpa only [add_zero] using hglobal

theorem realRadialJacobiPairingFirstTerm_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    realRadialJacobiPairingFirstTerm g p w 0 =
      (underlyingRealRiemannianMetric g.form).inner p.proj p.2 w := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  dsimp only [realRadialJacobiPairingFirstTerm]
  rw [realVelocityPhaseCoordinates_zero_fderiv_apply g p w]
  simp only [map_zero, add_zero]
  rw [realGeodesicFlow_zero, realPhaseChart_eq_extChartAt p p (mem_chart_source _ _)]
  exact realMetricInChart_tangentCoords g.form p.proj p.proj (mem_chart_source _ _) p.2 w

theorem realRadialJacobiPairingFirstTerm_eq_initial (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    realRadialJacobiPairingFirstTerm g p w t =
      (underlyingRealRiemannianMetric g.form).inner p.proj p.2 w := by
  have heq := is_const_of_deriv_eq_zero
    (fun s => (realRadialJacobiPairingFirstTerm_hasDerivAt g p w s).differentiableAt)
    (fun s => (realRadialJacobiPairingFirstTerm_hasDerivAt g p w s).deriv) t 0
  exact heq.trans (realRadialJacobiPairingFirstTerm_zero g p w)

/-- First variation along the actual geodesic: the radial/Jacobi pairing
is exactly linear in time, with its genuine initial physical inner product. -/
theorem realRadialJacobiPairing_eq (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    realRadialJacobiPairing g p w t =
      t * (underlyingRealRiemannianMetric g.form).inner p.proj p.2 w := by
  let c := (underlyingRealRiemannianMetric g.form).inner p.proj p.2 w
  have hD (s : ℝ) : HasDerivAt (realRadialJacobiPairing g p w) c s := by
    simpa only [realRadialJacobiPairingFirstTerm_eq_initial] using
      realRadialJacobiPairing_hasDerivAt g p w s
  have hF (s : ℝ) : HasDerivAt (fun r => realRadialJacobiPairing g p w r - r * c) 0 s := by
    convert (hD s).sub ((hasDerivAt_id s).mul_const c) using 1 <;> simp <;> rfl
  have heq := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => (hF s).deriv) t 0
  have h0 : realRadialJacobiPairing g p w 0 = 0 := by
    simp only [realRadialJacobiPairing, realGeodesicJacobiField_zero, map_zero]
  rw [h0, zero_mul, sub_zero] at heq
  exact sub_eq_zero.mp heq

/-- The actual initial-velocity Jacobi differential at time one is the
spatial differential of the actual exponential in its endpoint chart. -/
theorem realGeodesicJacobiField_one_endpoint_coords (g : SmoothMetric M)
    (x : M.Carrier) (v w : ComplexVector n) :
    realTangentCoords (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
      (realGeodesicJacobiField g (⟨x, realFrameCLM x x v⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (realFrameCLM x x w) 1) =
      fderiv ℝ (realExponentialEndpointCoordinates g x v) v w := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  let y := realNormalExponentialMap g x v
  let F : TangentSpace 𝓘(ℝ, ComplexVector n) x → ComplexVector n :=
    fun a => chartPt y (realExponentialMap g x a)
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt y) y :=
    contMDiffAt_extChartAt (I := 𝓘(ℝ, ComplexVector n))
  have hF : DifferentiableAt ℝ F (realFrameCLM x x v) :=
    (hchart.comp _ ((realExponentialMap_contMDiff g x).contMDiffAt)).contDiffAt.differentiableAt (by simp)
  have hcomp : HasFDerivAt (F ∘ realFrameCLM x x)
      ((fderiv ℝ F (realFrameCLM x x v)).comp (realFrameCLM x x)) v :=
    hF.hasFDerivAt.comp v (realFrameCLM x x).hasFDerivAt
  have hc := realTangentCoords_mfderiv (realExponentialMap g x) (realFrameCLM x x v)
    y (mem_chart_source _ _) (realFrameCLM x x w)
    ((realExponentialMap_contMDiff g x).mdifferentiableAt (by simp))
  change realTangentCoords y y
      (realGeodesicJacobiField g (⟨x, realFrameCLM x x v⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (realFrameCLM x x w) 1) =
      fderiv ℝ F (realFrameCLM x x v) (realFrameCLM x x w) at hc
  rw [hc]
  change _ = fderiv ℝ (F ∘ realFrameCLM x x) v w
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]

theorem realExponentialEndpointDifferential_eq_JacobiField (g : SmoothMetric M)
    (x : M.Carrier) (v w : ComplexVector n) :
    realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v w) =
        realGeodesicJacobiField g (⟨x, realFrameCLM x x v⟩ :
          TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (realFrameCLM x x w) 1 := by
  rw [← realGeodesicJacobiField_one_endpoint_coords]
  exact realFrameCLM_realTangentCoords _ _ (mem_chart_source _ _) _

/-- Gauss's lemma for the genuine globally constructed Riemannian
exponential and the genuine metric, with no supplied orthogonality law. -/
theorem realExponential_gaussLemma (g : SmoothMetric M) (x : M.Carrier)
    (v w : ComplexVector n) :
    (underlyingRealRiemannianMetric g.form).inner (realNormalExponentialMap g x v)
      (realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
        (fderiv ℝ (realExponentialEndpointCoordinates g x v) v v))
      (realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
        (fderiv ℝ (realExponentialEndpointCoordinates g x v) v w)) =
      (underlyingRealRiemannianMetric g.form).inner x (realFrameCLM x x v) (realFrameCLM x x w) := by
  rw [realExponential_radialDifferential_eq_velocity, realExponentialEndpointDifferential_eq_JacobiField]
  exact (realRadialJacobiPairing_eq g
    (⟨x, realFrameCLM x x v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (realFrameCLM x x w) 1).trans (one_mul _)

theorem realMetricInChart_self_frame (h : HermitianField M) (x : M.Carrier)
    (u v : ComplexVector n) : realMetricInChart h x (chartPt x x) u v =
      (underlyingRealRiemannianMetric h).inner x (realFrameCLM x x u) (realFrameCLM x x v) := by
  rw [← realMetricInChart_tangentCoords h x x (mem_chart_source _ _),
    realTangentCoords_realFrameCLM x x (mem_chart_source _ _),
    realTangentCoords_realFrameCLM x x (mem_chart_source _ _)]

/-- The genuine Gauss identity in the actual endpoint coordinate chart. -/
theorem realExponential_gaussLemma_in_chart (g : SmoothMetric M) (x : M.Carrier)
    (v w : ComplexVector n) :
    realMetricInChart g.form (realNormalExponentialMap g x v)
      (chartPt (realNormalExponentialMap g x v) (realNormalExponentialMap g x v))
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v v)
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v w) =
        realMetricInChart g.form x (chartPt x x) v w := by
  rw [realMetricInChart_self_frame, realMetricInChart_self_frame]
  exact realExponential_gaussLemma g x v w

theorem realExponential_gaussLemma_orthogonal (g : SmoothMetric M) (x : M.Carrier)
    (v w : ComplexVector n) (hvw : realMetricInChart g.form x (chartPt x x) v w = 0) :
    realMetricInChart g.form (realNormalExponentialMap g x v)
      (chartPt (realNormalExponentialMap g x v) (realNormalExponentialMap g x v))
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v v)
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v w) = 0 := by
  rw [realExponential_gaussLemma_in_chart, hvw]

/-- The radial coordinate derivative is bounded by the actual physical
speed of the exponential image; this is the pointwise Gauss length estimate. -/
theorem realExponential_gaussLemma_speed_bound (g : SmoothMetric M) (x : M.Carrier)
    (v w : ComplexVector n) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    |realMetricInChart g.form x (chartPt x x) v w| ≤
      ‖realFrameCLM x x v‖ *
        ‖realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
          (fderiv ℝ (realExponentialEndpointCoordinates g x v) v w)‖ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  rw [realMetricInChart_self_frame, ← realExponential_gaussLemma g x v w]
  have h := abs_real_inner_le_norm
    (realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v v))
    (realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v w))
  rwa [realExponential_radialDifferential_norm g x v] at h

end Yau.LeafProofs.L12Aux
