import Yau.LeafProofs.L12ParallelTransport
import Yau.LeafProofs.L12GeodesicVariation

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

theorem chartGeodesicSpray_fderiv_apply (g : SmoothMetric M) (x : M.Carrier)
    (q h : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget x) :
    fderiv ℝ (chartGeodesicSpray g.form x) q h =
      (h.2, -((fderiv ℝ (chartChristoffelBilin g.form x) q.1 h.1) q.2 q.2 +
        chartChristoffelBilin g.form x q.1 h.2 q.2 +
        chartChristoffelBilin g.form x q.1 q.2 h.2)) := by
  have hΓ := ((chartChristoffelBilin_contDiffOn g x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hq)).differentiableAt (by simp)
  have hcoef := hΓ.hasFDerivAt.comp q (hasFDerivAt_fst (p := q))
  have hv := hasFDerivAt_snd (𝕜 := ℝ) (p := q)
  have hA := (hcoef.clm_apply hv).clm_apply hv
  have hF := hv.prodMk hA.neg
  have heq : chartGeodesicSpray g.form x =
      (fun p : ComplexVector n × ComplexVector n =>
        (p.2, -chartChristoffelBilin g.form x p.1 p.2 p.2)) := by
    funext p
    exact Prod.ext rfl (chartGeodesicAcceleration_eq g.form x p.1 p.2)
  simp only [Pi.neg_apply, Function.comp_apply] at hF
  rw [heq, hF.fderiv]
  change (h.2, -(chartChristoffelBilin g.form x q.1 q.2 h.2 +
    (chartChristoffelBilin g.form x q.1 h.2 +
      (fderiv ℝ (chartChristoffelBilin g.form x) q.1 h.1) q.2) q.2)) = _
  simp only [ContinuousLinearMap.add_apply]
  apply Prod.ext
  · rfl
  · abel

/-- Actual coordinate first variations satisfy the linearized geodesic
system, with the genuine differentiated Christoffel bilinear map. -/
theorem chartGeodesicVariation_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    (η W : ℝ → ComplexVector n × ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hW : HasDerivAt W
      ((fderiv ℝ (chartGeodesicSpray g.form x) (η t)) (W t)) t) :
    HasDerivAt (fun s => (W s).1) (W t).2 t ∧
      HasDerivAt (fun s => (W s).2)
        (-((fderiv ℝ (chartChristoffelBilin g.form x) (η t).1 (W t).1) (η t).2 (η t).2 +
          chartChristoffelBilin g.form x (η t).1 (W t).2 (η t).2 +
          chartChristoffelBilin g.form x (η t).1 (η t).2 (W t).2)) t := by
  rw [chartGeodesicSpray_fderiv_apply g x (η t) (W t) hz] at hW
  exact ⟨(ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt
      t hW,
    (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt
      t hW⟩

/-- Evaluation of the genuine variational operator on one initial
phase-space tangent vector gives an actual linearized spray solution. -/
theorem chartGeodesicVariation_column_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n)
    (V : ℝ → (ComplexVector n × ComplexVector n) →L[ℝ]
      (ComplexVector n × ComplexVector n)) (a : ComplexVector n × ComplexVector n) {t : ℝ}
    (hV : HasDerivAt V ((fderiv ℝ (chartGeodesicSpray g.form x) (η t)).comp (V t)) t) :
    HasDerivAt (fun s => V s a)
      ((fderiv ℝ (chartGeodesicSpray g.form x) (η t)) (V t a)) t := by
  exact (ContinuousLinearMap.apply ℝ (ComplexVector n × ComplexVector n) a).hasFDerivAt.comp_hasDerivAt
    t hV

theorem fderiv_vectorBilin_apply_const {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : D → E →L[ℝ] E →L[ℝ] F} {z : D}
    (hB : DifferentiableAt ℝ B z) (u : D) (v w : E) :
    fderiv ℝ (fun y => B y v w) z u = fderiv ℝ B z u v w := by
  have h := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const v z)).clm_apply
    (hasFDerivAt_const w z)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply, map_zero, zero_add, add_zero]

theorem chartChristoffelBilin_fderiv_symm (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (u v w : ComplexVector n) :
    (fderiv ℝ (chartChristoffelBilin g.form x) z u) v w =
      (fderiv ℝ (chartChristoffelBilin g.form x) z u) w v := by
  have hB := ((chartChristoffelBilin_contDiffOn g x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun y => chartChristoffelBilin g.form x y v w) =
      (fun y => chartChristoffelBilin g.form x y w v) :=
    funext fun y => chartChristoffelBilin_symm g.form x y v w
  rw [← fderiv_vectorBilin_apply_const hB u v w, heq,
    fderiv_vectorBilin_apply_const hB u w v]

/-- The curvature expression of the actual Levi--Civita Christoffel
bilinear map in one genuine coordinate chart. -/
def chartCurvatureVector (h : HermitianField M) (x : M.Carrier)
    (z u v w : ComplexVector n) : ComplexVector n :=
  (fderiv ℝ (chartChristoffelBilin h x) z u) v w -
    (fderiv ℝ (chartChristoffelBilin h x) z v) u w +
    chartChristoffelBilin h x z u (chartChristoffelBilin h x z v w) -
    chartChristoffelBilin h x z v (chartChristoffelBilin h x z u w)

def chartVariationCovDeriv (h : HermitianField M) (x : M.Carrier)
    (η W : ℝ → ComplexVector n × ComplexVector n) (t : ℝ) : ComplexVector n :=
  (W t).2 + chartChristoffelBilin h x (η t).1 (η t).2 (W t).1

/-- The genuine linearized geodesic system obeys the coordinate form of
the covariant Jacobi equation. -/
theorem chartVariationCovDeriv_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    (η W : ℝ → ComplexVector n × ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray g.form x (η t)) t)
    (hW : HasDerivAt W ((fderiv ℝ (chartGeodesicSpray g.form x) (η t)) (W t)) t) :
    HasDerivAt (chartVariationCovDeriv g.form x η W)
      (-chartChristoffelBilin g.form x (η t).1 (η t).2
          (chartVariationCovDeriv g.form x η W t) -
        chartCurvatureVector g.form x (η t).1 (W t).1 (η t).2 (η t).2) t := by
  have hB := ((chartChristoffelBilin_contDiffOn g x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hzu : HasDerivAt (fun s => (η s).1) (η t).2 t :=
    (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt t hη
  have hvu : HasDerivAt (fun s => (η s).2)
      (-chartChristoffelBilin g.form x (η t).1 (η t).2 (η t).2) t := by
    have h : HasDerivAt (fun s => (η s).2)
        (chartGeodesicAcceleration g.form x (η t).1 (η t).2) t :=
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt t hη
    rwa [chartGeodesicAcceleration_eq] at h
  have hΓt : HasDerivAt (fun s => chartChristoffelBilin g.form x (η s).1)
      (fderiv ℝ (chartChristoffelBilin g.form x) (η t).1 (η t).2) t :=
    by simpa only [Function.comp_def] using hB.hasFDerivAt.comp_hasDerivAt t hzu
  have hJ := chartGeodesicVariation_hasDerivAt g x η W hz hW
  have hL := hJ.2.add ((hΓt.clm_apply hvu).clm_apply hJ.1)
  convert hL using 1
  · rfl
  · simp only [chartVariationCovDeriv, chartCurvatureVector, map_add, map_neg,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
    rw [chartChristoffelBilin_fderiv_symm g x (η t).1 hz (η t).2 (W t).1 (η t).2,
      chartChristoffelBilin_symm g.form x (η t).1 (W t).1 (η t).2,
      chartChristoffelBilin_symm g.form x (η t).1 (W t).2 (η t).2,
      chartChristoffelBilin_symm g.form x (η t).1 (W t).1
        (chartChristoffelBilin g.form x (η t).1 (η t).2 (η t).2)]
    abel

theorem chartChristoffelBilin_fderiv_basis (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    (fderiv ℝ (chartChristoffelBilin g.form x) z (realVec a)) (realVec b) (realVec c) =
      ∑ l, rDeriv (fun y => christoffel g.form x y l b c) z a • realVec l := by
  have hB := ((chartChristoffelBilin_contDiffOn g x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hd (l : RIdx n) := ((christoffel_contDiffOn g x l b c).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hsum := HasFDerivAt.sum (u := Finset.univ)
    (fun l _ => (hd l).hasFDerivAt.smul_const (realVec l))
  have heq : (fun y => chartChristoffelBilin g.form x y (realVec b) (realVec c)) =
      (fun y => ∑ l, christoffel g.form x y l b c • realVec l) :=
    funext fun y => chartChristoffelBilin_basis g.form x y b c
  have hSumFun : (fun y => ∑ l, christoffel g.form x y l b c • realVec l) =
      ∑ l, (fun y => christoffel g.form x y l b c • realVec l) := by
    funext y
    simp only [Finset.sum_apply]
  rw [← fderiv_vectorBilin_apply_const hB (realVec a) (realVec b) (realVec c), heq,
    hSumFun, hsum.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, rDeriv]

/-- The differentiated bilinear-map curvature expression has exactly the
project's genuine Levi--Civita coordinate curvature coefficients. -/
theorem chartCurvatureVector_basis (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    chartCurvatureVector g.form x z (realVec a) (realVec b) (realVec c) =
      ∑ l, riemannCoeff g.form x z a b c l • realVec l := by
  have hcomp (i j k : RIdx n) :
      chartChristoffelBilin g.form x z (realVec i)
        (chartChristoffelBilin g.form x z (realVec j) (realVec k)) =
      ∑ l, (∑ d, christoffel g.form x z d j k * christoffel g.form x z l i d) • realVec l := by
    rw [chartChristoffelBilin_basis g.form x z j k, map_sum]
    simp only [map_smul, chartChristoffelBilin_basis, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]
  unfold chartCurvatureVector
  rw [chartChristoffelBilin_fderiv_basis g x z hz a b c,
    chartChristoffelBilin_fderiv_basis g x z hz b a c, hcomp a b c, hcomp b a c]
  simp only [riemannCoeff, add_smul, sub_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_smul]
  abel

/-- The coordinate curvature expression is realized by the actual
Levi--Civita curvature action on genuine coordinate vector fields. -/
theorem realFrameCLM_chartCurvatureVector_basis (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    realFrameCLM x (chartInv x z)
      (chartCurvatureVector g.form x z (realVec a) (realVec b) (realVec c)) =
        realCurvatureFrame g x a b c (chartInv x z) := by
  have hs : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  rw [chartCurvatureVector_basis g x z hz a b c,
    realCurvatureFrame_eq_riemannCoeff g x z hz a b c, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro l _
  rw [realFrameCLM_apply x (chartInv x z) hs]

/-- A genuine parallel-transport trajectory satisfies the full triple
ODE in every fixed base chart containing its current base point. -/
theorem realParallelTransport_in_chart_hasDerivAt (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) (x : M.Carrier) {t : ℝ}
    (hx : (γ t).proj ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurveAt γ (realParallelTransportSpray g) t →
      HasDerivAt (realTransportChart x ∘ γ)
        (chartParallelTransportField g.form x (realTransportChart x (γ t))) t := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  intro hγ
  let p := γ t
  let pX : realTransportBundle M := ⟨x, (0, 0)⟩
  let η := extChartAt (realTransportModel n) p ∘ γ
  let q := η t
  have hlocal := (realParallelTransport_chart_eventually g γ hγ).self_of_nhds
  have hη : HasDerivAt η (chartParallelTransportField g.form p.proj q) t := hlocal.2
  have hA : q.1 ∈ chartTarget p.proj := hlocal.1
  have hq : q = realTransportChart p.proj p :=
    realTransportChart_eq_extChartAt _ _ (mem_chart_source _ _)
  have hB : chartInv p.proj q.1 ∈ (extChartAt (ComplexModel n) x).source := by
    rw [hq]
    change chartInv p.proj (chartPt p.proj p.proj) ∈ _
    have hinv : chartInv p.proj (chartPt p.proj p.proj) = p.proj :=
      (extChartAt (ComplexModel n) p.proj).left_inv (mem_extChartAt_source _)
    rw [hinv]
    simpa only [extChartAt_source] using hx
  have hκ := (realTransportChartChange_contDiffAt p.proj x q hA hB).differentiableAt (by simp)
  have hd := hκ.hasFDerivAt.comp_hasDerivAt t hη
  rw [realTransportChartChange_fderiv_field g p.proj x q hA hB] at hd
  have hc := (realTransportChart_change_eventually p pX q hA hB).comp_tendsto hη.continuousAt
  have hpX : γ t ∈ (extChartAt (realTransportModel n) pX).source :=
    (realTransportChart_source pX (γ t)).mpr hx
  have heq : (realTransportChartChange p.proj x ∘ η) =ᶠ[𝓝 t] (realTransportChart x ∘ γ) := by
    filter_upwards [hc, hγ.continuousAt.preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := realTransportModel n) p),
      hγ.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := realTransportModel n) pX).mem_nhds hpX)] with s hs hsp hsX
    change extChartAt (realTransportModel n) pX
      ((extChartAt (realTransportModel n) p).symm (extChartAt (realTransportModel n) p (γ s))) =
      realTransportChartChange p.proj x (η s) at hs
    rw [(extChartAt (realTransportModel n) p).left_inv hsp] at hs
    exact hs.symm.trans (realTransportChart_eq_extChartAt pX (γ s)
      ((realTransportChart_source pX (γ s)).mp hsX))
  have heq0 : realTransportChartChange p.proj x q = realTransportChart x (γ t) :=
    heq.self_of_nhds
  rw [heq0] at hd
  exact heq.hasDerivAt_iff.mp hd

/-- Genuine parallel-field coordinates satisfy the parallel-vector ODE
in every fixed chart, allowing subsequent Jacobi coefficient calculus. -/
theorem realParallelField_in_chart_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (x : M.Carrier) {t : ℝ}
    (hx : (realGeodesicFlow g p t).proj ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    HasDerivAt (fun s => realTangentCoords x (realGeodesicFlow g p s).proj
        (realParallelField g p w s))
      (-chartChristoffelBilin g.form x (chartPt x (realGeodesicFlow g p t).proj)
        (realTangentCoords x (realGeodesicFlow g p t).proj (realGeodesicFlow g p t).2)
        (realTangentCoords x (realGeodesicFlow g p t).proj (realParallelField g p w t))) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  let γ := realParallelTransportFlow g (⟨p.proj, (p.2, w)⟩ : realTransportBundle M)
  have hv (s : ℝ) : realTransportVelocity (γ s) = realGeodesicFlow g p s :=
    realParallelTransportFlow_velocity g _ s
  have hw (s : ℝ) : realTransportVector (γ s) =
      (⟨(realGeodesicFlow g p s).proj, realParallelField g p w s⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :=
    (realParallelField_totalSpace g p w s).symm
  have hbase : (γ t).proj = (realGeodesicFlow g p t).proj :=
    congrArg Bundle.TotalSpace.proj (hv t)
  have hx' : (γ t).proj ∈ (chartAt (ComplexVector n) x).source := by rwa [hbase]
  have hη := realParallelTransport_in_chart_hasDerivAt g γ x hx'
    ((realParallelTransportFlow_integral g _).isMIntegralCurveAt t)
  let L := (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).comp
    (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n × ComplexVector n))
  have hd : HasDerivAt
      (fun s => (realPhaseChart x (realTransportVector (γ s))).2)
      (-chartChristoffelBilin g.form x (realPhaseChart x (realTransportVelocity (γ t))).1
        (realPhaseChart x (realTransportVelocity (γ t))).2
        (realPhaseChart x (realTransportVector (γ t))).2) t :=
    L.hasFDerivAt.comp_hasDerivAt t hη
  simp_rw [hv, hw] at hd
  exact hd

/-- The actual global geodesic flow has a local family of genuine initial
variations satisfying the covariant Jacobi equation in fixed coordinates.
The variational operator is the actual initial-state differential. -/
theorem exists_realGeodesic_local_coordinateJacobi (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ V : (ComplexVector n × ComplexVector n) → ℝ →
        (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × ComplexVector n),
      (∀ z ∈ Metric.ball (extChartAt (realPhaseModel n) p p) r,
        V z 0 = ContinuousLinearMap.id ℝ (ComplexVector n × ComplexVector n)) ∧
      ∀ z ∈ Metric.ball (extChartAt (realPhaseModel n) p p) r, ∀ t ∈ Set.Ioo (-ε) ε,
        HasFDerivAt (fun z' => realGeodesicChartFlow g p z' t) (V z t) z ∧
        ∀ a : ComplexVector n × ComplexVector n,
          HasDerivAt (fun s => (V z s a).1) (V z t a).2 t ∧
          HasDerivAt (chartVariationCovDeriv g.form p.proj
            (realGeodesicChartFlow g p z) (fun s => V z s a))
            (-chartChristoffelBilin g.form p.proj (realGeodesicChartFlow g p z t).1
                (realGeodesicChartFlow g p z t).2
                (chartVariationCovDeriv g.form p.proj
                  (realGeodesicChartFlow g p z) (fun s => V z s a) t) -
              chartCurvatureVector g.form p.proj (realGeodesicChartFlow g p z t).1
                (V z t a).1 (realGeodesicChartFlow g p z t).2
                  (realGeodesicChartFlow g p z t).2) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  obtain ⟨r, hr, ε, hε, V, hc, hVc, hinit, hsol, hball⟩ := realGeodesicChartFlow_local_C1 g p
  refine ⟨r, hr, ε, hε, V, hinit, ?_⟩
  intro z hz t ht
  have hs := hsol z hz t ht
  have htarget : realGeodesicChartFlow g p z t ∈ (extChartAt (realPhaseModel n) p).target :=
    (extChartAt (realPhaseModel n) p).map_source hs.1
  have hpos := (realPhaseChart_target p _).mp htarget
  refine ⟨hs.2.2.2, ?_⟩
  intro a
  have hW := chartGeodesicVariation_column_hasDerivAt g p.proj
    (realGeodesicChartFlow g p z) (V z) a hs.2.2.1
  exact ⟨(chartGeodesicVariation_hasDerivAt g p.proj
      (realGeodesicChartFlow g p z) (fun s => V z s a) hpos hW).1,
    chartVariationCovDeriv_hasDerivAt g p.proj
      (realGeodesicChartFlow g p z) (fun s => V z s a) hpos hs.2.1 hW⟩

end Yau.LeafProofs.L12Aux
