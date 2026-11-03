import Yau.LeafProofs.L12JacobiGeometry
import Yau.LeafProofs.L12ExponentialDifferential

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- Coordinate components of an actual manifold differential are the
ordinary differential of the same genuine coordinate expression. -/
theorem realTangentCoords_mfderiv {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (F : D → M.Carrier) (v : D) (x : M.Carrier)
    (hx : F v ∈ (chartAt (ComplexVector n) x).source) (w : D) :
    letI := manifold_realSmooth M
    MDifferentiableAt 𝓘(ℝ, D) 𝓘(ℝ, ComplexVector n) F v →
      realTangentCoords x (F v)
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, ComplexVector n) F v
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) v).symm w)) =
        fderiv ℝ (fun a => chartPt x (F a)) v w := by
  letI := manifold_realSmooth M
  intro hF
  have hchart : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
      (chartPt x) (F v) := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, ComplexVector n)) hx
  rw [realTangentCoords_eq_mvfderiv x (F v) hx,
    ← mvfderiv_comp_apply v hchart hF ((NormedSpace.fromTangentSpace (𝕜 := ℝ) v).symm w),
    mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
  change (fderiv ℝ (chartPt x ∘ F) v)
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) v)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) v).symm w)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The metric product rule with arbitrary covariant coordinate
velocities, directly derived from actual Levi--Civita metric compatibility. -/
theorem realMetricInChart_pairing_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    {z a b : ℝ → ComplexVector n} {t : ℝ} {u a' b' : ComplexVector n}
    (hz : z t ∈ chartTarget x) (hzu : HasDerivAt z u t)
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => realMetricInChart g.form x (z s) (a s) (b s))
      (realMetricInChart g.form x (z t)
          (a' + chartChristoffelBilin g.form x (z t) u (a t)) (b t) +
        realMetricInChart g.form x (z t) (a t)
          (b' + chartChristoffelBilin g.form x (z t) u (b t))) t := by
  have hB := ((realMetricInChart_smooth g x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hDB : HasDerivAt (fun s => realMetricInChart g.form x (z s))
      (fderiv ℝ (realMetricInChart g.form x) (z t) u) t := by
    simpa only [Function.comp_def] using hB.hasFDerivAt.comp_hasDerivAt t hzu
  have hpair := (hDB.clm_apply ha).clm_apply hb
  convert hpair using 1
  simp only [ContinuousLinearMap.add_apply, map_add]
  rw [realMetricInChart_connection_compatibility g x (z t) hz u (a t) (b t)]
  ring

/-- Genuine C1 dependence of the phase flow at an arbitrary fixed time
on the actual initial tangent vector in its physical norm. -/
theorem realVelocityFlow_contMDiff (g : SmoothMetric M) (x : M.Carrier) (t : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) (realPhaseModel n) 1
      (fun w : TangentSpace 𝓘(ℝ, ComplexVector n) x =>
        realGeodesicFlow g (⟨x, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  have hIn : ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x)
      ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) 1
      (fun w : TangentSpace 𝓘(ℝ, ComplexVector n) x =>
        ((⟨x, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier), t)) :=
    ((realTangentFiber_contMDiff g x).of_le (by simp)).prodMk contMDiff_const
  exact (realGeodesicFlow_joint_contMDiff g).comp hIn

def realVelocityBaseFlow (g : SmoothMetric M) (x : M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) x) (t : ℝ) : M.Carrier :=
  (realGeodesicFlow g (⟨x, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t).proj

theorem realVelocityBaseFlow_contMDiff (g : SmoothMetric M) (x : M.Carrier) (t : ℝ) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n) 1
      (fun w => realVelocityBaseFlow g x w t) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  exact (Bundle.contMDiff_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := 1)
    (TangentSpace 𝓘(ℝ, ComplexVector n))).comp (realVelocityFlow_contMDiff g x t)

/-- The genuine initial-velocity Jacobi field is the actual differential
of the globally constructed geodesic's base flow. -/
def realGeodesicJacobiField (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  exact mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) 𝓘(ℝ, ComplexVector n)
    (fun a => realVelocityBaseFlow g p.proj a t) p.2
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.2).symm w)

theorem realGeodesicJacobiField_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) : realGeodesicJacobiField g p w 0 = 0 := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have hfun : (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
      realVelocityBaseFlow g p.proj a 0) = (fun _ => p.proj) := by
    funext a
    change (realGeodesicFlow g (⟨p.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) 0).proj = _
    rw [realGeodesicFlow_zero]
  unfold realGeodesicJacobiField
  rw [hfun, mfderiv_const]
  rfl

def realVelocityPhaseCoordinates (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ : ℝ)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    ComplexVector n × ComplexVector n := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact extChartAt (realPhaseModel n) (realGeodesicFlow g p t₀)
    (realGeodesicFlow g (⟨p.proj, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t₀)

theorem realVelocityPhaseCoordinates_contDiffAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContDiffAt ℝ 1 (realVelocityPhaseCoordinates g p t₀) p.2 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have hchart : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) 1
      (extChartAt (realPhaseModel n) (realGeodesicFlow g p t₀)) (realGeodesicFlow g p t₀) :=
    contMDiffAt_extChartAt
  have hflow : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
      (realPhaseModel n) 1
      (fun w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
        realGeodesicFlow g (⟨p.proj, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t₀) p.2 :=
    (realVelocityFlow_contMDiff g p.proj t₀).contMDiffAt
  exact (hchart.comp p.2 hflow).contDiffAt

/-- Near the actual initial velocity, the global flow at a shifted time
factors exactly through the fixed chart at the intermediate actual state. -/
theorem realVelocityPhaseCoordinates_flow_add_eventually (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ τ : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    (fun w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
      extChartAt (realPhaseModel n) (realGeodesicFlow g p t₀)
        (realGeodesicFlow g (⟨p.proj, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ + τ)))
      =ᶠ[𝓝 p.2] (fun w => realGeodesicChartFlow g (realGeodesicFlow g p t₀)
        (realVelocityPhaseCoordinates g p t₀ w) τ) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have hcont := (realVelocityFlow_contMDiff g p.proj t₀).continuous.continuousAt (x := p.2)
  have hn := hcont.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := realPhaseModel n) (realGeodesicFlow g p t₀))
  filter_upwards [hn] with w hw
  unfold realGeodesicChartFlow realVelocityPhaseCoordinates
  rw [(extChartAt (realPhaseModel n) (realGeodesicFlow g p t₀)).left_inv hw,
    ← realGeodesicFlow_add]

/-- Actual Jacobi coefficients in the globally constructed physical
parallel orthonormal frame. -/
def realGeodesicJacobiMatrix (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact fun i j => (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g p t).proj
    (realGlobalParallelFrame g p t i)
    (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t)

theorem realGeodesicJacobiMatrix_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : realGeodesicJacobiMatrix g p 0 = 0 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  ext i j
  change (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g p 0).proj
    (realGlobalParallelFrame g p 0 i)
    (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) 0) = 0
  rw [realGeodesicJacobiField_zero, map_zero]

/-- The first component of an actual phase-flow derivative is exactly the
coordinate representation of the genuine Jacobi field. -/
theorem realGeodesicJacobiField_coords_of_phase_deriv (g : SmoothMetric M)
    (p q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ)
    (B : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →L[ℝ]
      (ComplexVector n × ComplexVector n))
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    realGeodesicFlow g p s ∈ (extChartAt (realPhaseModel n) q).source →
      HasFDerivAt (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
        extChartAt (realPhaseModel n) q
          (realGeodesicFlow g (⟨p.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s)) B p.2 →
      realTangentCoords q.proj (realGeodesicFlow g p s).proj
        (realGeodesicJacobiField g p w s) = (B w).1 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hsource hB
  have hf := (realVelocityFlow_contMDiff g p.proj s).continuous.continuousAt (x := p.2)
  have hn := hf.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := realPhaseModel n) q).mem_nhds hsource)
  have heq : (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
      (extChartAt (realPhaseModel n) q
        (realGeodesicFlow g (⟨p.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s)).1)
      =ᶠ[𝓝 p.2] (fun a => chartPt q.proj (realVelocityBaseFlow g p.proj a s)) := by
    filter_upwards [hn] with a ha
    rw [realPhaseChart_eq_extChartAt q _ ((realPhaseChart_source q _).mp ha)]
    rfl
  have hfirst : HasFDerivAt
      (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
        (extChartAt (realPhaseModel n) q
          (realGeodesicFlow g (⟨p.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s)).1)
      ((ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).comp B) p.2 :=
    (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp p.2 hB
  have hbase := heq.hasFDerivAt_iff.mp hfirst
  have hmd := (realVelocityBaseFlow_contMDiff g p.proj s p.2).mdifferentiableAt (by simp)
  have hcoords := realTangentCoords_mfderiv (fun a => realVelocityBaseFlow g p.proj a s) p.2
    q.proj ((realPhaseChart_source q _).mp hsource) w hmd
  rw [hbase.fderiv] at hcoords
  exact hcoords

/-- At every global time, one proved local variational operator models
the actual initial differential after a fixed intermediate chart map.
This derives time-regularity of genuine global Jacobi fields from the
local variational ODE and the exact flow-addition identity. -/
theorem exists_realGeodesicJacobi_shifted_model (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    let p₀ := realGeodesicFlow g p t₀
    let z₀ := extChartAt (realPhaseModel n) p₀ p₀
    let B := fderiv ℝ (realVelocityPhaseCoordinates g p t₀) p.2
    ∃ ε > (0 : ℝ), ∃ V : ℝ →
        (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × ComplexVector n),
      V 0 = ContinuousLinearMap.id ℝ (ComplexVector n × ComplexVector n) ∧
      ∀ τ ∈ Set.Ioo (-ε) ε,
        HasDerivAt (realGeodesicChartFlow g p₀ z₀)
          (chartGeodesicSpray g.form p₀.proj (realGeodesicChartFlow g p₀ z₀ τ)) τ ∧
        HasDerivAt V ((fderiv ℝ (chartGeodesicSpray g.form p₀.proj)
          (realGeodesicChartFlow g p₀ z₀ τ)).comp (V τ)) τ ∧
        (realGeodesicChartFlow g p₀ z₀ τ).1 ∈ chartTarget p₀.proj ∧
        realGeodesicFlow g p (t₀ + τ) ∈ (extChartAt (realPhaseModel n) p₀).source ∧
        HasFDerivAt (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
          extChartAt (realPhaseModel n) p₀
            (realGeodesicFlow g (⟨p.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ + τ)))
          ((V τ).comp B) p.2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj,
          realTangentCoords p₀.proj (realGeodesicFlow g p (t₀ + τ)).proj
            (realGeodesicJacobiField g p w (t₀ + τ)) = (V τ (B w)).1 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let p₀ := realGeodesicFlow g p t₀
  let z₀ := extChartAt (realPhaseModel n) p₀ p₀
  let U := realVelocityPhaseCoordinates g p t₀
  let B := fderiv ℝ U p.2
  obtain ⟨r, hr, ε, hε, V, hc, hVc, hinit, hsol, hball⟩ := realGeodesicChartFlow_local_C1 g p₀
  have hz₀ : z₀ ∈ Metric.ball (extChartAt (realPhaseModel n) p₀ p₀) r := Metric.mem_ball_self hr
  have hU : HasFDerivAt U B p.2 :=
    (realVelocityPhaseCoordinates_contDiffAt g p t₀).differentiableAt (by simp) |>.hasFDerivAt
  have hU₀ : U p.2 = z₀ := rfl
  refine ⟨ε, hε, V z₀, (hinit z₀ hz₀), ?_⟩
  intro τ hτ
  have hs := hsol z₀ hz₀ τ hτ
  have hlocal : HasFDerivAt (fun z => realGeodesicChartFlow g p₀ z τ) (V z₀ τ) (U p.2) := by
    rw [hU₀]
    exact hs.2.2.2
  have hcomp : HasFDerivAt (fun a => realGeodesicChartFlow g p₀ (U a) τ)
      ((V z₀ τ).comp B) p.2 := by
    simpa only [Function.comp_def] using hlocal.comp p.2 hU
  have hfactor := realVelocityPhaseCoordinates_flow_add_eventually g p t₀ τ
  have hactual := hfactor.hasFDerivAt_iff.mpr hcomp
  have hsrc : realGeodesicFlow g p (t₀ + τ) ∈ (extChartAt (realPhaseModel n) p₀).source := by
    have h := hs.1
    change realGeodesicFlow g ((extChartAt (realPhaseModel n) p₀).symm z₀) τ ∈ _ at h
    rw [(extChartAt (realPhaseModel n) p₀).left_inv (mem_extChartAt_source p₀)] at h
    rwa [← realGeodesicFlow_add] at h
  have hpos : (realGeodesicChartFlow g p₀ z₀ τ).1 ∈ chartTarget p₀.proj :=
    (realPhaseChart_target p₀ _).mp ((extChartAt (realPhaseModel n) p₀).map_source hs.1)
  refine ⟨hs.2.1, hs.2.2.1, hpos, hsrc, hactual, ?_⟩
  intro w
  exact realGeodesicJacobiField_coords_of_phase_deriv g p p₀ (t₀ + τ)
    ((V z₀ τ).comp B) w hsrc hactual

end Yau.LeafProofs.L12Aux
