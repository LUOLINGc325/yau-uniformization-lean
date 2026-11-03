import Yau.LeafProofs.L12JacobiMatrix

/-! Actual initial-velocity Jacobi matrix derivatives in the genuine parallel frame.
The second derivative is expressed using the actual coordinate curvature tensor;
this module does not assume a matrix Jacobi equation or a volume comparison. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

theorem realGlobalParallelFrame_in_chart_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (i : Fin (2 * n))
    (x : M.Carrier) {t : ℝ}
    (hx : (realGeodesicFlow g p t).proj ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    HasDerivAt (fun s => realTangentCoords x (realGeodesicFlow g p s).proj
        (realGlobalParallelFrame g p s i))
      (-chartChristoffelBilin g.form x (chartPt x (realGeodesicFlow g p t).proj)
        (realTangentCoords x (realGeodesicFlow g p t).proj (realGeodesicFlow g p t).2)
        (realTangentCoords x (realGeodesicFlow g p t).proj (realGlobalParallelFrame g p t i))) t := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have heq (s : ℝ) : realGlobalParallelFrame g p s i =
      realParallelField g p (realInitialOrthonormalFrame g p.proj i) s :=
    realParallelFrame_apply g p (realInitialOrthonormalFrame g p.proj) s i
  simp_rw [heq]
  exact realParallelField_in_chart_hasDerivAt g p (realInitialOrthonormalFrame g p.proj i) x hx

theorem realGeodesicChartFlow_at_center (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (τ : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    realGeodesicChartFlow g p (extChartAt (realPhaseModel n) p p) τ =
      extChartAt (realPhaseModel n) p (realGeodesicFlow g p τ) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  unfold realGeodesicChartFlow
  rw [(extChartAt (realPhaseModel n) p).left_inv (mem_extChartAt_source p)]

theorem realGeodesicChartFlow_shifted_eq_realPhaseChart (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ τ : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    realGeodesicFlow g p (t₀ + τ) ∈
        (extChartAt (realPhaseModel n) (realGeodesicFlow g p t₀)).source →
      realGeodesicChartFlow g (realGeodesicFlow g p t₀)
        (extChartAt (realPhaseModel n) (realGeodesicFlow g p t₀) (realGeodesicFlow g p t₀)) τ =
        realPhaseChart (realGeodesicFlow g p t₀).proj (realGeodesicFlow g p (t₀ + τ)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hs
  rw [realGeodesicChartFlow_at_center, ← realGeodesicFlow_add]
  exact realPhaseChart_eq_extChartAt _ _ ((realPhaseChart_source _ _).mp hs)

theorem realGeodesicJacobiMatrix_in_chart (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (i j : Fin (2 * n))
    (x : M.Carrier) {t : ℝ}
    (hx : (realGeodesicFlow g p t).proj ∈ (chartAt (ComplexVector n) x).source) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    realGeodesicJacobiMatrix g p t i j =
      realMetricInChart g.form x (chartPt x (realGeodesicFlow g p t).proj)
        (realTangentCoords x (realGeodesicFlow g p t).proj (realGlobalParallelFrame g p t i))
        (realTangentCoords x (realGeodesicFlow g p t).proj
          (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t)) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact (realMetricInChart_tangentCoords g.form x (realGeodesicFlow g p t).proj hx
    (realGlobalParallelFrame g p t i)
    (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t)).symm

/-- Pairing a genuine linearized geodesic with a coordinate-parallel
vector differentiates to pairing with its covariant first variation. -/
theorem chartVariation_parallelPair_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    (η W : ℝ → ComplexVector n × ComplexVector n) (a : ℝ → ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray g.form x (η t)) t)
    (hW : HasDerivAt W ((fderiv ℝ (chartGeodesicSpray g.form x) (η t)) (W t)) t)
    (ha : HasDerivAt a (-chartChristoffelBilin g.form x (η t).1 (η t).2 (a t)) t) :
    HasDerivAt (fun s => realMetricInChart g.form x (η s).1 (a s) (W s).1)
      (realMetricInChart g.form x (η t).1 (a t) (chartVariationCovDeriv g.form x η W t)) t := by
  have hzu : HasDerivAt (fun s => (η s).1) (η t).2 t :=
    (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt t hη
  have hJ := (chartGeodesicVariation_hasDerivAt g x η W hz hW).1
  have hpair := realMetricInChart_pairing_hasDerivAt g x hz hzu ha hJ
  simpa only [neg_add_cancel, map_zero, ContinuousLinearMap.zero_apply, zero_add,
    chartVariationCovDeriv] using hpair

/-- A second metric-compatible derivative gives the genuine coordinate
curvature term, with the Jacobi sign. -/
theorem chartVariation_covParallelPair_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    (η W : ℝ → ComplexVector n × ComplexVector n) (a : ℝ → ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray g.form x (η t)) t)
    (hW : HasDerivAt W ((fderiv ℝ (chartGeodesicSpray g.form x) (η t)) (W t)) t)
    (ha : HasDerivAt a (-chartChristoffelBilin g.form x (η t).1 (η t).2 (a t)) t) :
    HasDerivAt (fun s => realMetricInChart g.form x (η s).1 (a s)
        (chartVariationCovDeriv g.form x η W s))
      (-realMetricInChart g.form x (η t).1 (a t)
        (chartCurvatureVector g.form x (η t).1 (W t).1 (η t).2 (η t).2)) t := by
  have hzu : HasDerivAt (fun s => (η s).1) (η t).2 t :=
    (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt t hη
  have hL := chartVariationCovDeriv_hasDerivAt g x η W hz hη hW
  have hpair := realMetricInChart_pairing_hasDerivAt g x hz hzu ha hL
  have hcancel : (-chartChristoffelBilin g.form x (η t).1 (η t).2
        (chartVariationCovDeriv g.form x η W t) -
      chartCurvatureVector g.form x (η t).1 (W t).1 (η t).2 (η t).2) +
      chartChristoffelBilin g.form x (η t).1 (η t).2
        (chartVariationCovDeriv g.form x η W t) =
      -chartCurvatureVector g.form x (η t).1 (W t).1 (η t).2 (η t).2 := by abel
  simpa only [neg_add_cancel, map_zero, ContinuousLinearMap.zero_apply, zero_add,
    hcancel, map_neg] using hpair

/-- Recovering a derivative after a translation of the time variable. -/
theorem hasDerivAt_of_comp_const_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} (a x : ℝ)
    (h : HasDerivAt (fun y => f (a + y)) f' x) : HasDerivAt f f' (a + x) := by
  have h' : HasDerivAt (fun y => f (a + y)) f' (-a + (a + x)) := by simpa using h
  simpa using h'.comp_const_add (-a) (a + x)

/-- Actual curvature acting on the genuine Jacobi field, paired with a
physical parallel-frame vector, expressed in one fixed valid chart. -/
def realJacobiCurvatureTermInChart (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (x : M.Carrier)
    (t : ℝ) (i j : Fin (2 * n)) : ℝ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let q := realGeodesicFlow g p t
  exact realMetricInChart g.form x (chartPt x q.proj)
    (realTangentCoords x q.proj (realGlobalParallelFrame g p t i))
    (chartCurvatureVector g.form x (chartPt x q.proj)
      (realTangentCoords x q.proj
        (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t))
      (realTangentCoords x q.proj q.2) (realTangentCoords x q.proj q.2))

/-- The actual initial-velocity phase differential determines the
covariant derivative of each genuine Jacobi-matrix entry at that time. -/
def realJacobiMatrixFirstDerivativeTerm (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (i j : Fin (2 * n)) : ℝ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let q := realGeodesicFlow g p t
  let z := extChartAt (realPhaseModel n) q q
  let B := fderiv ℝ (realVelocityPhaseCoordinates g p t) p.2
  let a := B (realInitialOrthonormalFrame g p.proj j)
  exact realMetricInChart g.form q.proj z.1
    (realTangentCoords q.proj q.proj (realGlobalParallelFrame g p t i))
    (a.2 + chartChristoffelBilin g.form q.proj z.1 z.2 a.1)

/-- A genuine local first-derivative representative of each actual
Jacobi-matrix entry, together with its actual curvature derivative. -/
theorem exists_realJacobiMatrix_local_derivative (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ : ℝ) (i j : Fin (2 * n)) :
    letI := manifold_realSmooth M
    ∃ ε > (0 : ℝ), ∃ D : ℝ → ℝ,
      D 0 = realJacobiMatrixFirstDerivativeTerm g p t₀ i j ∧
      ∀ τ ∈ Set.Ioo (-ε) ε,
      HasDerivAt (fun s => realGeodesicJacobiMatrix g p s i j) (D τ) (t₀ + τ) ∧
      HasDerivAt D
        (-realJacobiCurvatureTermInChart g p (realGeodesicFlow g p t₀).proj (t₀ + τ) i j) τ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let p₀ := realGeodesicFlow g p t₀
  let x := p₀.proj
  let z₀ := extChartAt (realPhaseModel n) p₀ p₀
  let B := fderiv ℝ (realVelocityPhaseCoordinates g p t₀) p.2
  obtain ⟨ε, hε, V, hV₀, hmodel⟩ := exists_realGeodesicJacobi_shifted_model g p t₀
  let η := realGeodesicChartFlow g p₀ z₀
  let a := B (realInitialOrthonormalFrame g p.proj j)
  let W := fun τ => V τ a
  let b := fun τ => realTangentCoords x (realGeodesicFlow g p (t₀ + τ)).proj
    (realGlobalParallelFrame g p (t₀ + τ) i)
  let D := fun τ => realMetricInChart g.form x (η τ).1 (b τ)
    (chartVariationCovDeriv g.form x η W τ)
  have hcode (τ : ℝ) (hτ : τ ∈ Set.Ioo (-ε) ε) :
      η τ = realPhaseChart x (realGeodesicFlow g p (t₀ + τ)) :=
    realGeodesicChartFlow_shifted_eq_realPhaseChart g p t₀ τ (hmodel τ hτ).2.2.2.1
  have hbase (τ : ℝ) (hτ : τ ∈ Set.Ioo (-ε) ε) :
      (realGeodesicFlow g p (t₀ + τ)).proj ∈ (chartAt (ComplexVector n) x).source :=
    (realPhaseChart_source p₀ _).mp (hmodel τ hτ).2.2.2.1
  have hscalar (τ : ℝ) (hτ : τ ∈ Set.Ioo (-ε) ε) :
      realGeodesicJacobiMatrix g p (t₀ + τ) i j =
        realMetricInChart g.form x (η τ).1 (b τ) (W τ).1 := by
    rw [realGeodesicJacobiMatrix_in_chart g p i j x (hbase τ hτ),
      (hmodel τ hτ).2.2.2.2.2 (realInitialOrthonormalFrame g p.proj j), hcode τ hτ]
    rfl
  have hη₀ : η 0 = z₀ := by
    dsimp only [η]
    rw [realGeodesicChartFlow_at_center, realGeodesicFlow_zero]
  have hW₀ : W 0 = a := by
    dsimp only [W]
    rw [hV₀, ContinuousLinearMap.id_apply]
  have hb₀ : b 0 = realTangentCoords x p₀.proj (realGlobalParallelFrame g p t₀ i) := by
    dsimp only [b]
    rw [add_zero]
  have hD₀ : D 0 = realJacobiMatrixFirstDerivativeTerm g p t₀ i j := by
    dsimp only [D, chartVariationCovDeriv]
    rw [hη₀, hW₀, hb₀]
    rfl
  refine ⟨ε, hε, D, hD₀, ?_⟩
  intro τ hτ
  rcases hmodel τ hτ with ⟨hη, hV, hpos, hsrc, hphase, hcoords⟩
  have hW : HasDerivAt W ((fderiv ℝ (chartGeodesicSpray g.form x) (η τ)) (W τ)) τ :=
    chartGeodesicVariation_column_hasDerivAt g x η V a hV
  have hb : HasDerivAt b (-chartChristoffelBilin g.form x (η τ).1 (η τ).2 (b τ)) τ := by
    have h := (realGlobalParallelFrame_in_chart_hasDerivAt g p i x (hbase τ hτ)).comp_const_add t₀ τ
    rw [hcode τ hτ]
    exact h
  have hpair := chartVariation_parallelPair_hasDerivAt g x η W b hpos hη hW hb
  have hactualShift : HasDerivAt (fun s => realGeodesicJacobiMatrix g p (t₀ + s) i j) (D τ) τ := by
    apply hpair.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs
    exact hscalar s hs
  have hsecond := chartVariation_covParallelPair_hasDerivAt g x η W b hpos hη hW hb
  have hcurv : realMetricInChart g.form x (η τ).1 (b τ)
      (chartCurvatureVector g.form x (η τ).1 (W τ).1 (η τ).2 (η τ).2) =
      realJacobiCurvatureTermInChart g p x (t₀ + τ) i j := by
    dsimp only [realJacobiCurvatureTermInChart]
    rw [hcode τ hτ, hcoords (realInitialOrthonormalFrame g p.proj j)]
    rfl
  rw [hcurv] at hsecond
  exact ⟨hasDerivAt_of_comp_const_add t₀ τ hactualShift, hsecond⟩

theorem realGeodesicJacobiMatrix_hasDerivAt_firstTerm (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (i j : Fin (2 * n)) :
    letI := manifold_realSmooth M
    HasDerivAt (fun s => realGeodesicJacobiMatrix g p s i j)
      (realJacobiMatrixFirstDerivativeTerm g p t i j) t := by
  letI := manifold_realSmooth M
  obtain ⟨ε, hε, D, hD₀, hD⟩ := exists_realJacobiMatrix_local_derivative g p t i j
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have h := (hD 0 h0).1
  simpa only [add_zero, hD₀] using h

def realGeodesicJacobiMatrixDeriv (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun i j => deriv (fun s => realGeodesicJacobiMatrix g p s i j) t

theorem realGeodesicJacobiMatrix_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (i j : Fin (2 * n)) :
    HasDerivAt (fun s => realGeodesicJacobiMatrix g p s i j)
      (realGeodesicJacobiMatrixDeriv g p t i j) t := by
  letI := manifold_realSmooth M
  exact (realGeodesicJacobiMatrix_hasDerivAt_firstTerm g p t i j).differentiableAt.hasDerivAt

theorem realGeodesicJacobiMatrixDeriv_eq_firstTerm (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (i j : Fin (2 * n)) :
    realGeodesicJacobiMatrixDeriv g p t i j = realJacobiMatrixFirstDerivativeTerm g p t i j := by
  letI := manifold_realSmooth M
  exact (realGeodesicJacobiMatrix_hasDerivAt_firstTerm g p t i j).deriv

set_option backward.isDefEq.respectTransparency false in
/-- The actual global first derivative has the genuine curvature
second derivative, evaluated in the valid chart at the actual base point. -/
theorem realGeodesicJacobiMatrixDeriv_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (i j : Fin (2 * n)) :
    HasDerivAt (fun s => realGeodesicJacobiMatrixDeriv g p s i j)
      (-realJacobiCurvatureTermInChart g p (realGeodesicFlow g p t).proj t i j) t := by
  letI := manifold_realSmooth M
  obtain ⟨ε, hε, D, hD₀, hD⟩ := exists_realJacobiMatrix_local_derivative g p t i j
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have heq : (fun τ => realGeodesicJacobiMatrixDeriv g p (t + τ) i j) =ᶠ[𝓝 0] D := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with τ hτ
    exact (hD τ hτ).1.deriv
  have hD0 := (hD 0 h0).2
  rw [add_zero] at hD0
  have hshift := heq.hasDerivAt_iff.mpr hD0
  have hglobal : HasDerivAt (fun s => realGeodesicJacobiMatrixDeriv g p s i j)
      (-realJacobiCurvatureTermInChart g p (realGeodesicFlow g p t).proj t i j) (t + 0) :=
    hasDerivAt_of_comp_const_add t 0 hshift
  simpa only [add_zero] using hglobal

theorem realGeodesicJacobiMatrixDeriv_continuousAt_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    ContinuousAt (realGeodesicJacobiMatrixDeriv g p) 0 := by
  exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
    (realGeodesicJacobiMatrixDeriv_hasDerivAt g p 0 i j).continuousAt

theorem realVelocityPhaseCoordinates_zero_apply (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    realVelocityPhaseCoordinates g p 0 w =
      (chartPt p.proj p.proj, realTangentCoords p.proj p.proj w) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  unfold realVelocityPhaseCoordinates
  rw [realGeodesicFlow_zero, realGeodesicFlow_zero]
  exact realPhaseChart_eq_extChartAt p ⟨p.proj, w⟩ (mem_chart_source _ _)

set_option backward.isDefEq.respectTransparency false in
theorem realVelocityPhaseCoordinates_zero_fderiv_apply (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    fderiv ℝ (realVelocityPhaseCoordinates g p 0) p.2 w =
      (0, realTangentCoords p.proj p.proj w) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have hfun : realVelocityPhaseCoordinates g p 0 =
      (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
        (chartPt p.proj p.proj, realTangentCoords p.proj p.proj a)) :=
    funext fun a => realVelocityPhaseCoordinates_zero_apply g p a
  have hD : HasFDerivAt
      (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
        (chartPt p.proj p.proj, realTangentCoords p.proj p.proj a))
      ((0 : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →L[ℝ] ComplexVector n).prod
        (realTangentCoords p.proj p.proj)) p.2 :=
    (hasFDerivAt_const (chartPt p.proj p.proj) p.2).prodMk
      (realTangentCoords p.proj p.proj).hasFDerivAt
  rw [hfun, hD.fderiv]
  rfl

theorem realGlobalParallelFrame_zero_preferred_coords (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (i : Fin (2 * n)) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    realTangentCoords (realGeodesicFlow g p 0).proj (realGeodesicFlow g p 0).proj
      (realGlobalParallelFrame g p 0 i) =
      realTangentCoords p.proj p.proj (realInitialOrthonormalFrame g p.proj i) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hpt : (⟨(realGeodesicFlow g p 0).proj, realGlobalParallelFrame g p 0 i⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) =
      ⟨p.proj, realInitialOrthonormalFrame g p.proj i⟩ :=
    (congrFun (realGlobalParallelFrame_lift g p i) 0).trans
      (realParallelLift_zero g p (realInitialOrthonormalFrame g p.proj i))
  have hcoords := congrArg (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
    (realPhaseChart (realGeodesicFlow g p 0).proj q).2) hpt
  have hbase : (realGeodesicFlow g p 0).proj = p.proj :=
    congrArg Bundle.TotalSpace.proj (realGeodesicFlow_zero g p)
  have hright : (realPhaseChart (realGeodesicFlow g p 0).proj
      (⟨p.proj, realInitialOrthonormalFrame g p.proj i⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)).2 =
      realTangentCoords p.proj p.proj (realInitialOrthonormalFrame g p.proj i) := by
    rw [hbase]
    rfl
  exact hcoords.trans hright

/-- The actual initial Jacobi derivative is the identity, in the
physical initial/parallel orthonormal bases. -/
theorem realJacobiMatrixFirstDerivativeTerm_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (i j : Fin (2 * n)) :
    realJacobiMatrixFirstDerivativeTerm g p 0 i j =
      (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) i j := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  dsimp only [realJacobiMatrixFirstDerivativeTerm]
  rw [realVelocityPhaseCoordinates_zero_fderiv_apply g p (realInitialOrthonormalFrame g p.proj j),
    realGlobalParallelFrame_zero_preferred_coords g p i]
  simp only [map_zero, add_zero]
  rw [realGeodesicFlow_zero,
    realPhaseChart_eq_extChartAt p p (mem_chart_source _ _)]
  change realMetricInChart g.form p.proj (chartPt p.proj p.proj)
    (realTangentCoords p.proj p.proj (realInitialOrthonormalFrame g p.proj i))
    (realTangentCoords p.proj p.proj (realInitialOrthonormalFrame g p.proj j)) =
      if i = j then (1 : ℝ) else 0
  rw [realMetricInChart_tangentCoords g.form p.proj p.proj (mem_chart_source _ _)]
  exact (realInitialOrthonormalFrame g p.proj).inner_eq_ite i j

theorem realGeodesicJacobiMatrixDeriv_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : realGeodesicJacobiMatrixDeriv g p 0 = 1 := by
  ext i j
  rw [realGeodesicJacobiMatrixDeriv_eq_firstTerm, realJacobiMatrixFirstDerivativeTerm_zero]

end Yau.LeafProofs.L12Aux
