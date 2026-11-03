import Yau.LeafProofs.L12Transport

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

def realParallelTransportFlow (g : SmoothMetric M) (p : realTransportBundle M) :
    ℝ → realTransportBundle M := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  exact (exists_global_realParallelTransport g p).choose

theorem realParallelTransportFlow_zero (g : SmoothMetric M) (p : realTransportBundle M) :
    realParallelTransportFlow g p 0 = p := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  exact (exists_global_realParallelTransport g p).choose_spec.1

theorem realParallelTransportFlow_integral (g : SmoothMetric M) (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurve (realParallelTransportFlow g p) (realParallelTransportSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  exact (exists_global_realParallelTransport g p).choose_spec.2

theorem realTransportVelocity_isMIntegralCurve (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    IsMIntegralCurve γ (realParallelTransportSpray g) →
      IsMIntegralCurve (realTransportVelocity ∘ γ) (realGeodesicSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  intro hγ
  exact isMIntegralCurve_iff_isMIntegralCurveOn.mpr
    (realTransportVelocity_isMIntegralCurveOn g γ (hγ.isMIntegralCurveOn Set.univ))

theorem realParallelTransportFlow_velocity (g : SmoothMetric M) (p : realTransportBundle M)
    (t : ℝ) : realTransportVelocity (realParallelTransportFlow g p t) =
      realGeodesicFlow g (realTransportVelocity p) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  have hγ := realTransportVelocity_isMIntegralCurve g (realParallelTransportFlow g p)
    (realParallelTransportFlow_integral g p)
  have heq := realGeodesicFlow_unique g (realTransportVelocity p)
    (realTransportVelocity ∘ realParallelTransportFlow g p)
    (by rw [Function.comp_apply, realParallelTransportFlow_zero]) hγ
  exact congrFun heq t

theorem realParallelTransportFlow_energy (g : SmoothMetric M) (p : realTransportBundle M)
    (t : ℝ) : realTransportedEnergy g.form (realParallelTransportFlow g p t) =
      realTransportedEnergy g.form p := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  let A := |t| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have h0 : (0 : ℝ) ∈ Set.Ioo (-A) A := ⟨by linarith, hA⟩
  have ht : t ∈ Set.Ioo (-A) A := abs_lt.mp (lt_add_one |t|)
  have h := realTransportedEnergy_constant g (realParallelTransportFlow g p)
    ((realParallelTransportFlow_integral g p).isMIntegralCurveOn _) ht h0
  rwa [realParallelTransportFlow_zero] at h

theorem realParallelTransportFlow_unique (g : SmoothMetric M) (p : realTransportBundle M)
    (γ : ℝ → realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    γ 0 = p → IsMIntegralCurve γ (realParallelTransportSpray g) →
      γ = realParallelTransportFlow g p := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransport_t2Space M
  letI := realTransportModel_boundaryless n
  intro hγ0 hγ
  apply isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    ((realParallelTransportSpray_contMDiff g).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp))
    hγ (realParallelTransportFlow_integral g p)
  exact hγ0.trans (realParallelTransportFlow_zero g p).symm

theorem realParallelTransport_chart_eventually (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) {t₀ : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurveAt γ (realParallelTransportSpray g) t₀ →
      ∀ᶠ t in 𝓝 t₀,
        (extChartAt (realTransportModel n) (γ t₀) (γ t)).1 ∈ chartTarget (γ t₀).proj ∧
        HasDerivAt (extChartAt (realTransportModel n) (γ t₀) ∘ γ)
          (chartParallelTransportField g.form (γ t₀).proj
            (extChartAt (realTransportModel n) (γ t₀) (γ t))) t := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro hγ
  filter_upwards [hγ.eventually_hasDerivAt,
    hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := realTransportModel n) (γ t₀))] with t ht hsource
  refine ⟨(realTransportChart_target (γ t₀) _).mp
    ((extChartAt (realTransportModel n) (γ t₀)).map_source hsource), ?_⟩
  rwa [tangentCoordChange_realParallelTransportSpray g (γ t₀) (γ t) hsource] at ht

theorem chartParallelTransport_contDiffOn_Icc (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × (ComplexVector n × ComplexVector n)) {a b : ℝ}
    (hη : ∀ r ∈ Set.Icc a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartParallelTransportField g.form x (η r)) r) :
    ContDiffOn ℝ ∞ η (Set.Icc a b) := by
  have hf := (chartParallelTransportField_contDiffOn g x).comp contDiffOn_snd
    (show Set.MapsTo Prod.snd (Set.Icc a b ×ˢ (chartTarget x ×ˢ Set.univ))
      (chartTarget x ×ˢ Set.univ) from fun _ hq => hq.2)
  exact ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := (⊤ : ℕ∞))
    (f := fun (_r : ℝ) (q : ComplexVector n × (ComplexVector n × ComplexVector n)) =>
      chartParallelTransportField g.form x q)
    (u := chartTarget x ×ˢ Set.univ) (α := η) hf
    (fun r hr => (hη r hr).2.hasDerivWithinAt)
    (fun r hr => ⟨(hη r hr).1, Set.mem_univ _⟩)

theorem realParallelTransport_contMDiffAt (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) {t₀ : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurveAt γ (realParallelTransportSpray g) t₀ →
      ContMDiffAt 𝓘(ℝ, ℝ) (realTransportModel n) ∞ γ t₀ := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  intro hγ
  let p := γ t₀
  let η := extChartAt (realTransportModel n) p ∘ γ
  obtain ⟨δ, hδ, hδsol⟩ := Metric.mem_nhds_iff.mp (realParallelTransport_chart_eventually g γ hγ)
  have hcc : Set.Icc (t₀ - δ / 2) (t₀ + δ / 2) ⊆ Metric.ball t₀ δ := by
    intro t ht
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hηsmooth : ContDiffOn ℝ ∞ η (Set.Icc (t₀ - δ / 2) (t₀ + δ / 2)) :=
    chartParallelTransport_contDiffOn_Icc g p.proj η (fun t ht => hδsol (hcc ht))
  have hηat : ContDiffAt ℝ ∞ η t₀ :=
    hηsmooth.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
  have hi := contMDiffWithinAt_extChartAt_symm_range
    (I := realTransportModel n) (n := ∞) p (mem_extChartAt_target p)
  rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hi
  have hcom := hi.comp t₀ hηat.contMDiffAt
  apply hcom.congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := realTransportModel n) p)] with t ht
  exact ((extChartAt (realTransportModel n) p).left_inv ht).symm

theorem realParallelTransportFlow_contMDiff (g : SmoothMetric M) (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiff 𝓘(ℝ, ℝ) (realTransportModel n) ∞ (realParallelTransportFlow g p) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro t
  exact realParallelTransport_contMDiffAt g (realParallelTransportFlow g p)
    ((realParallelTransportFlow_integral g p).isMIntegralCurveAt t)

set_option backward.isDefEq.respectTransparency false in
theorem realTransportVector_contMDiff :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    ContMDiff (realTransportModel n) (realPhaseModel n) ∞
      (realTransportVector (M := M)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  intro q
  apply Bundle.contMDiffAt_totalSpace.mpr
  have hid : ContMDiffAt (realTransportModel n) (realTransportModel n) ∞
      (id : realTransportBundle M → realTransportBundle M) q := contMDiffAt_id
  have hp := Bundle.contMDiffAt_totalSpace.mp hid
  exact ⟨hp.1, (ContinuousLinearMap.snd ℝ (ComplexVector n)
    (ComplexVector n)).contMDiff.contMDiffAt.comp q hp.2⟩

/-- A genuine globally parallel tangent lift over the already constructed
actual geodesic, selected from the genuine Whitney-sum ODE. -/
def realParallelLift (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier :=
  fun t => realTransportVector (realParallelTransportFlow g ⟨p.proj, (p.2, w)⟩ t)

theorem realParallelLift_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) : realParallelLift g p w 0 = ⟨p.proj, w⟩ := by
  unfold realParallelLift
  rw [realParallelTransportFlow_zero]
  rfl

theorem realParallelLift_proj (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    (realParallelLift g p w t).proj = (realGeodesicFlow g p t).proj := by
  have h := congrArg Bundle.TotalSpace.proj
    (realParallelTransportFlow_velocity g ⟨p.proj, (p.2, w)⟩ t)
  exact h

theorem realParallelLift_contMDiff (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff 𝓘(ℝ, ℝ) (realPhaseModel n) ∞ (realParallelLift g p w) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  exact realTransportVector_contMDiff.comp
    (realParallelTransportFlow_contMDiff g ⟨p.proj, (p.2, w)⟩)

theorem realParallelLift_energy (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    realTangentEnergy g.form (realParallelLift g p w t) =
      realTangentEnergy g.form (⟨p.proj, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :=
  realParallelTransportFlow_energy g ⟨p.proj, (p.2, w)⟩ t

theorem realParallelTransport_vectorCoords_hasDerivAt (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) {t₀ : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurveAt γ (realParallelTransportSpray g) t₀ →
      HasDerivAt (fun t => realTangentCoords (γ t₀).proj (γ t).proj (γ t).2.2)
        (-chartChristoffelBilin g.form (γ t₀).proj (chartPt (γ t₀).proj (γ t₀).proj)
          (realTangentCoords (γ t₀).proj (γ t₀).proj (γ t₀).2.1)
          (realTangentCoords (γ t₀).proj (γ t₀).proj (γ t₀).2.2)) t₀ := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro hγ
  let e := extChartAt (realTransportModel n) (γ t₀)
  have hη := (realParallelTransport_chart_eventually g γ hγ).self_of_nhds
  let L := (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).comp
    (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n × ComplexVector n))
  have hd : HasDerivAt (fun t => (e (γ t)).2.2)
      (-chartChristoffelBilin g.form (γ t₀).proj (e (γ t₀)).1
        (e (γ t₀)).2.1 (e (γ t₀)).2.2) t₀ :=
    L.hasFDerivAt.comp_hasDerivAt t₀ hη.2
  have hself : e (γ t₀) = realTransportChart (γ t₀).proj (γ t₀) :=
    realTransportChart_eq_extChartAt _ _ (mem_chart_source _ _)
  rw [hself] at hd
  have heq : (fun t => (e (γ t)).2.2) =ᶠ[𝓝 t₀]
      (fun t => realTangentCoords (γ t₀).proj (γ t).proj (γ t).2.2) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := realTransportModel n) (γ t₀))] with t ht
    rw [realTransportChart_eq_extChartAt _ _ ((realTransportChart_source _ _).mp ht)]
    rfl
  exact heq.hasDerivAt_iff.mp hd

theorem realLeviCivitaConnection_ownFrame (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) (w : ComplexVector n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection g (realCoordinateField x w) x v =
      realFrameCLM x x (chartChristoffelBilin g.form x (chartPt x x)
        (realTangentCoords x x v) w) := by
  letI := manifold_realSmooth M
  have hinv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hc := realLeviCivitaConnection_constFrame g x (chartPt x x)
    (mem_extChartAt_target x) (realTangentCoords x x v) w
  rw [hinv] at hc
  have hv : realCoordinateField x (realTangentCoords x x v) x = v := by
    rw [← realFrameCLM_apply x x (mem_chart_source _ _)]
    exact realFrameCLM_realTangentCoords x x (mem_chart_source _ _) v
  rwa [hv] at hc

/-- Parallelism is expressed directly through the actual Levi--Civita
connection on a frozen ambient coordinate field and the actual base
curve velocity. No parallelism hypothesis is added. -/
theorem realParallelTransport_connection_derivative_zero (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) (t : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    IsMIntegralCurve γ (realParallelTransportSpray g) →
      realFrameCLM (γ t).proj (γ t).proj
          (deriv (fun s => realTangentCoords (γ t).proj (γ s).proj (γ s).2.2) t) +
        realLeviCivitaConnection g
          (realCoordinateField (γ t).proj
            (realTangentCoords (γ t).proj (γ t).proj (γ t).2.2)) (γ t).proj
          (realCurveVelocity (fun s => (γ s).proj) t) = 0 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  intro hγ
  have hcoords := realParallelTransport_vectorCoords_hasDerivAt g γ
    (hγ.isMIntegralCurveAt t)
  have hγv := realTransportVelocity_isMIntegralCurve g γ hγ
  have hv := realCurveVelocity_realGeodesic g (realTransportVelocity ∘ γ)
    (hγv.isMIntegralCurveAt t)
  change realCurveVelocity (fun s => (γ s).proj) t = (γ t).2.1 at hv
  rw [hv, hcoords.deriv, realLeviCivitaConnection_ownFrame]
  rw [map_neg]
  exact neg_add_cancel _

theorem realParallelLift_connection_derivative_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    letI := manifold_realSmooth M
    let x := (realParallelLift g p w t).proj
    realFrameCLM x x
        (deriv (fun s => realTangentCoords x (realParallelLift g p w s).proj
          (realParallelLift g p w s).2) t) +
      realLeviCivitaConnection g
        (realCoordinateField x (realTangentCoords x x (realParallelLift g p w t).2)) x
        (realCurveVelocity (fun s => (realParallelLift g p w s).proj) t) = 0 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  exact realParallelTransport_connection_derivative_zero g
    (realParallelTransportFlow g ⟨p.proj, (p.2, w)⟩) t
    (realParallelTransportFlow_integral g ⟨p.proj, (p.2, w)⟩)

/-- The transported vector in the exact fiber of the chosen global
geodesic. The cast is justified by the proved equality of base points. -/
def realParallelField (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj :=
  cast (congrArg (TangentSpace 𝓘(ℝ, ComplexVector n)) (realParallelLift_proj g p w t))
    (realParallelLift g p w t).2

theorem realParallelField_totalSpace (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    (⟨(realGeodesicFlow g p t).proj, realParallelField g p w t⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = realParallelLift g p w t :=
  Bundle.TotalSpace.mk_cast (realParallelLift_proj g p w t) _

theorem realParallelField_coords_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    letI := manifold_realSmooth M
    let x := (realGeodesicFlow g p t).proj
    HasDerivAt (fun s => realTangentCoords x (realGeodesicFlow g p s).proj
        (realParallelField g p w s))
      (-chartChristoffelBilin g.form x (chartPt x x)
        (realTangentCoords x x (realGeodesicFlow g p t).2)
        (realTangentCoords x x (realParallelField g p w t))) t := by
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
  have hraw : HasDerivAt
      (fun s => (realPhaseChart (γ t).proj (realTransportVector (γ s))).2)
      (-chartChristoffelBilin g.form (γ t).proj (chartPt (γ t).proj (γ t).proj)
        (realPhaseChart (γ t).proj (realTransportVelocity (γ t))).2
        (realPhaseChart (γ t).proj (realTransportVector (γ t))).2) t :=
    realParallelTransport_vectorCoords_hasDerivAt g γ
      ((realParallelTransportFlow_integral g _).isMIntegralCurveAt t)
  rw [hbase] at hraw
  simp_rw [hv, hw] at hraw
  exact hraw

theorem realGeodesicFlow_baseCoords_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    letI := manifold_realSmooth M
    let x := (realGeodesicFlow g p t).proj
    HasDerivAt (fun s => chartPt x (realGeodesicFlow g p s).proj)
      (realTangentCoords x x (realGeodesicFlow g p t).2) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let γ := realGeodesicFlow g p
  let e := extChartAt (realPhaseModel n) (γ t)
  have hγ := (realGeodesicFlow_integral g p).isMIntegralCurveAt t
  have hη := (realGeodesic_chart_eventually g γ hγ).self_of_nhds
  have hd : HasDerivAt (fun s => (e (γ s)).1) (e (γ t)).2 t :=
    (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt
      t hη.2
  have hself : e (γ t) = realPhaseChart (γ t).proj (γ t) :=
    realPhaseChart_eq_extChartAt _ _ (mem_chart_source _ _)
  rw [hself] at hd
  have heq : (fun s => (e (γ s)).1) =ᶠ[𝓝 t]
      (fun s => chartPt (γ t).proj (γ s).proj) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := realPhaseModel n) (γ t))] with s hs
    rw [realPhaseChart_eq_extChartAt _ _ ((realPhaseChart_source _ _).mp hs)]
    rfl
  exact heq.hasDerivAt_iff.mp hd

theorem realMetricInChart_tangentCoords (h : HermitianField M) (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source)
    (u v : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    realMetricInChart h x (chartPt x y) (realTangentCoords x y u) (realTangentCoords x y v) =
      (underlyingRealRiemannianMetric h).inner y u v := by
  have hz : chartPt x y ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (by simpa only [extChartAt_source] using hy)
  have hinv : chartInv x (chartPt x y) = y :=
    (extChartAt (ComplexModel n) x).left_inv (by simpa only [extChartAt_source] using hy)
  rw [realMetricInChart_apply,
    ← realCoordinateField_eq_realChartVec x (chartPt x y) (realTangentCoords x y u) hz,
    ← realCoordinateField_eq_realChartVec x (chartPt x y) (realTangentCoords x y v) hz,
    hinv, ← realFrameCLM_apply x y hy, realFrameCLM_realTangentCoords x y hy u,
    ← realFrameCLM_apply x y hy, realFrameCLM_realTangentCoords x y hy v]

/-- The actual physical pairing of two transported vectors has zero
derivative, although the two lifts were constructed independently. -/
theorem realParallelField_pairing_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (u v : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    letI := manifold_realSmooth M
    HasDerivAt (fun s => (underlyingRealRiemannianMetric g.form).inner
      (realGeodesicFlow g p s).proj (realParallelField g p u s) (realParallelField g p v s)) 0 t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let x := (realGeodesicFlow g p t).proj
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hzu := realGeodesicFlow_baseCoords_hasDerivAt g p t
  have hu := realParallelField_coords_hasDerivAt g p u t
  have hv := realParallelField_coords_hasDerivAt g p v t
  have hpair := realMetricInChart_parallelPair_hasDerivAt g x hz hzu hu hv
  have hcont := ((FiberBundle.continuous_proj (ComplexVector n)
    (TangentSpace 𝓘(ℝ, ComplexVector n))).comp (realGeodesicFlow_contMDiff g p).continuous).continuousAt
      (x := t)
  have hn := hcont.preimage_mem_nhds
    ((chartAt (ComplexVector n) x).open_source.mem_nhds (mem_chart_source _ _))
  apply hpair.congr_of_eventuallyEq
  filter_upwards [hn] with s hs
  exact (realMetricInChart_tangentCoords g.form x (realGeodesicFlow g p s).proj hs
    (realParallelField g p u s) (realParallelField g p v s)).symm

theorem realMetric_pairing_of_totalSpace_eq (h : HermitianField M) {x y : M.Carrier}
    {u v : TangentSpace 𝓘(ℝ, ComplexVector n) x}
    {u' v' : TangentSpace 𝓘(ℝ, ComplexVector n) y}
    (hu : (⟨x, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨y, u'⟩)
    (hv : (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨y, v'⟩) :
    (underlyingRealRiemannianMetric h).inner x u v =
      (underlyingRealRiemannianMetric h).inner y u' v' := by
  have hxy : x = y := congrArg Bundle.TotalSpace.proj hu
  subst y
  have hu' := Bundle.TotalSpace.mk_inj.mp hu
  have hv' := Bundle.TotalSpace.mk_inj.mp hv
  subst u'
  subst v'
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Gram pairings of the genuine global parallel fields are preserved. -/
theorem realParallelField_pairing (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (u v : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    letI := manifold_realSmooth M
    (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g p t).proj
      (realParallelField g p u t) (realParallelField g p v t) =
        (underlyingRealRiemannianMetric g.form).inner p.proj u v := by
  letI := manifold_realSmooth M
  let G := fun s => (underlyingRealRiemannianMetric g.form).inner
    (realGeodesicFlow g p s).proj (realParallelField g p u s) (realParallelField g p v s)
  let A := |t| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have h0 : (0 : ℝ) ∈ Set.Ioo (-A) A := ⟨by linarith, hA⟩
  have ht : t ∈ Set.Ioo (-A) A := abs_lt.mp (lt_add_one |t|)
  have heq : G t = G 0 := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero
      (f := G) (convex_Ioo (-A) A).isPreconnected
    · intro r hr
      exact (realParallelField_pairing_hasDerivAt g p u v r).differentiableAt.differentiableWithinAt
    · intro r hr
      exact (realParallelField_pairing_hasDerivAt g p u v r).deriv
    · exact ht
    · exact h0
  change G t = _
  rw [heq]
  have hu₀ : (⟨(realGeodesicFlow g p 0).proj, realParallelField g p u 0⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨p.proj, u⟩ :=
    (realParallelField_totalSpace g p u 0).trans (realParallelLift_zero g p u)
  have hv₀ : (⟨(realGeodesicFlow g p 0).proj, realParallelField g p v 0⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨p.proj, v⟩ :=
    (realParallelField_totalSpace g p v 0).trans (realParallelLift_zero g p v)
  exact realMetric_pairing_of_totalSpace_eq g.form hu₀ hv₀

theorem realParallelField_orthonormal (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {ι : Type*} [Fintype ι] :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ∀ (e₀ : OrthonormalBasis ι ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)) (t : ℝ),
      Orthonormal ℝ (fun i => realParallelField g p (e₀ i) t) := by
  classical
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro e₀ t
  rw [orthonormal_iff_ite]
  intro i j
  change (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g p t).proj
    (realParallelField g p (e₀ i) t) (realParallelField g p (e₀ j) t) = _
  rw [realParallelField_pairing g p (e₀ i) (e₀ j) t]
  exact orthonormal_iff_ite.mp e₀.orthonormal i j

/-- Parallel transport of any actual initial orthonormal basis gives an
actual orthonormal basis in every tangent fiber along the geodesic. -/
def realParallelFrame (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {ι : Type*} [Fintype ι] :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    OrthonormalBasis ι ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) →
      (t : ℝ) → OrthonormalBasis ι ℝ
        (TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro e₀ t
  have hon := realParallelField_orthonormal g p e₀ t
  have hcard : Fintype.card ι = Module.finrank ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj) := by
    calc
      Fintype.card ι = Module.finrank ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :=
        (Module.finrank_eq_card_basis e₀.toBasis).symm
      _ = _ := (realTangent_finrank p.proj).trans
        (realTangent_finrank (realGeodesicFlow g p t).proj).symm
  exact OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge

theorem realParallelFrame_apply (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {ι : Type*} [Fintype ι] :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ∀ (e₀ : OrthonormalBasis ι ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)) (t : ℝ) (i : ι),
      realParallelFrame g p e₀ t i = realParallelField g p (e₀ i) t := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro e₀ t i
  simp only [realParallelFrame, OrthonormalBasis.coe_mk]

/-- An actual physical orthonormal basis in the initial tangent fiber. -/
def realInitialOrthonormalFrame (g : SmoothMetric M) (x : M.Carrier) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)).reindex
    (finCongr (realTangent_finrank x))

/-- A genuine global physical orthonormal frame along each complete
geodesic, constructed by actual Levi--Civita parallel transport. -/
def realGlobalParallelFrame (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    (t : ℝ) → OrthonormalBasis (Fin (2 * n)) ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact realParallelFrame g p (realInitialOrthonormalFrame g p.proj)

theorem realGlobalParallelFrame_lift (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (i : Fin (2 * n)) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    (fun t => (⟨(realGeodesicFlow g p t).proj, realGlobalParallelFrame g p t i⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) =
        realParallelLift g p (realInitialOrthonormalFrame g p.proj i) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  funext t
  change (⟨(realGeodesicFlow g p t).proj,
    realParallelFrame g p (realInitialOrthonormalFrame g p.proj) t i⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = _
  rw [realParallelFrame_apply]
  exact realParallelField_totalSpace g p (realInitialOrthonormalFrame g p.proj i) t

theorem realGlobalParallelFrame_contMDiff (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (i : Fin (2 * n)) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ContMDiff 𝓘(ℝ, ℝ) (realPhaseModel n) ∞
      (fun t => (⟨(realGeodesicFlow g p t).proj, realGlobalParallelFrame g p t i⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  rw [realGlobalParallelFrame_lift]
  exact realParallelLift_contMDiff g p (realInitialOrthonormalFrame g p.proj i)

theorem realGlobalParallelFrame_connection_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (i : Fin (2 * n)) (t : ℝ) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    let W := fun s => (⟨(realGeodesicFlow g p s).proj, realGlobalParallelFrame g p s i⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    let x := (W t).proj
    realFrameCLM x x (deriv (fun s => realTangentCoords x (W s).proj (W s).2) t) +
      realLeviCivitaConnection g
        (realCoordinateField x (realTangentCoords x x (W t).2)) x
        (realCurveVelocity (fun s => (W s).proj) t) = 0 := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let P : (ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) → Prop := fun W =>
    let x := (W t).proj
    realFrameCLM x x (deriv (fun s => realTangentCoords x (W s).proj (W s).2) t) +
      realLeviCivitaConnection g
        (realCoordinateField x (realTangentCoords x x (W t).2)) x
        (realCurveVelocity (fun s => (W s).proj) t) = 0
  have h : P (realParallelLift g p (realInitialOrthonormalFrame g p.proj i)) :=
    realParallelLift_connection_derivative_zero g p (realInitialOrthonormalFrame g p.proj i) t
  exact (congrArg P (realGlobalParallelFrame_lift g p i)).mpr h

end Yau.LeafProofs.L12Aux
