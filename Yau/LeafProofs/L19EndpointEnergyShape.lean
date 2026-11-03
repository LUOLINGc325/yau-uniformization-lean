import Yau.LeafProofs.L19EndpointEnergyJacobi

/-! The first phase differential of an actual endpoint branch gives its
covariant terminal velocity derivative and hence the actual energy trace. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- Differentiation of the actual terminal velocity uses the first phase
differential once. The Christoffel correction is its already proved Jacobi
covariant time derivative. -/
theorem realEndpointVelocityBranch_covariant_fderiv
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (W : ComplexVector n → TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (z : ComplexVector n) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    DifferentiableAt ℝ W z → W z = p.2 →
    ((fun y => chartPt (realGeodesicFlow g p d).proj
      (realVelocityBaseFlow g p.proj (W y) d)) =ᶠ[𝓝 z] id) →
    ∀ u : ComplexVector n,
    let q := realGeodesicFlow g p d
    let V := fun y => realChartVelocity q.proj
      (realGeodesicFlow g (⟨p.proj, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) d)
    fderiv ℝ V z u + chartChristoffelBilin g.form q.proj
      (chartPt q.proj q.proj) u (V z) =
        realJacobiCovariantPhaseDifferential g p d (fderiv ℝ W z u) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hW hWz hends u
  let q := realGeodesicFlow g p d
  let Q := fun y => realGeodesicFlow g
    (⟨p.proj, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) d
  have hp : (⟨p.proj, p.2⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = p := by
    cases p
    rfl
  have hQz : Q z = q := by dsimp only [Q, q]; rw [hWz, hp]
  have hfull := (realVelocityPhaseCoordinates_contDiffAt g p d).differentiableAt (by simp)
  have hfull' : HasFDerivAt (realVelocityPhaseCoordinates g p d)
      (fderiv ℝ (realVelocityPhaseCoordinates g p d) p.2) (W z) := by
    rw [hWz]
    exact hfull.hasFDerivAt
  have hcomp := hfull'.comp z hW.hasFDerivAt
  have hVcomp := (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp z hcomp
  have hQcont : ContinuousAt Q z :=
    ((realVelocityFlow_contMDiff g p.proj d).continuous.continuousAt).comp hW.continuousAt
  have hN : ∀ᶠ y in 𝓝 z, Q y ∈ (extChartAt (realPhaseModel n) q).source :=
    hQcont.preimage_mem_nhds (by rw [hQz]; exact extChartAt_source_mem_nhds q)
  have heqV : (fun y => realChartVelocity q.proj (Q y)) =ᶠ[𝓝 z]
      (fun y => (realVelocityPhaseCoordinates g p d (W y)).2) := by
    filter_upwards [hN] with y hy
    have h := realPhaseChart_eq_extChartAt q (Q y) ((realPhaseChart_source q _).mp hy)
    exact congrArg Prod.snd h.symm
  have hDV := (heqV.hasFDerivAt_iff.mpr hVcomp).fderiv
  have hJ := realEndpointVelocityBranch_jacobi_rightInverse g p d W z hW hWz hends u
  have hfirst := realGeodesicJacobiField_coords_of_phase_deriv g p q d
    (fderiv ℝ (realVelocityPhaseCoordinates g p d) p.2) (fderiv ℝ W z u)
    (mem_extChartAt_source q) hfull.hasFDerivAt
  rw [hJ, realTangentCoords_realFrameCLM q.proj q.proj (mem_chart_source _ _)] at hfirst
  have hcenter := realPhaseChart_eq_extChartAt q q (mem_chart_source _ _)
  change fderiv ℝ (fun y => realChartVelocity q.proj (Q y)) z u +
    chartChristoffelBilin g.form q.proj (chartPt q.proj q.proj) u
      (realChartVelocity q.proj (Q z)) = _
  rw [hDV, hQz]
  dsimp only [realJacobiCovariantPhaseDifferential]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  change _ + chartChristoffelBilin g.form q.proj (chartPt q.proj q.proj) u
    (realChartVelocity q.proj q) =
    _ + chartChristoffelBilin g.form q.proj
      (extChartAt (realPhaseModel n) q q).1
      (extChartAt (realPhaseModel n) q q).2
      ((fderiv ℝ (realVelocityPhaseCoordinates g p d) p.2 (fderiv ℝ W z u)).1)
  rw [hcenter]
  change _ + chartChristoffelBilin g.form q.proj (chartPt q.proj q.proj) u
    (realChartVelocity q.proj q) =
    _ + chartChristoffelBilin g.form q.proj (chartPt q.proj q.proj)
      (realChartVelocity q.proj q)
      ((fderiv ℝ (realVelocityPhaseCoordinates g p d) p.2 (fderiv ℝ W z u)).1)
  rw [← hfirst, chartChristoffelBilin_symm]

/-- The actual covariant derivative of the terminal branch velocity has
the shape matrix `A' A⁻¹` in the actual parallel orthonormal frame. -/
theorem realEndpointVelocityBranch_covariant_shape
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (W : ComplexVector n → TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (z : ComplexVector n) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    DifferentiableAt ℝ W z → W z = p.2 →
    ((fun y => chartPt (realGeodesicFlow g p d).proj
      (realVelocityBaseFlow g p.proj (W y) d)) =ᶠ[𝓝 z] id) →
    ∀ i j,
    let q := realGeodesicFlow g p d
    let U := fun k => realTangentCoords q.proj q.proj (realGlobalParallelFrame g p d k)
    let V := fun y => realChartVelocity q.proj
      (realGeodesicFlow g (⟨p.proj, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) d)
    realMetricInChart g.form q.proj (chartPt q.proj q.proj) (U i)
      (fderiv ℝ V z (U j) + chartChristoffelBilin g.form q.proj
        (chartPt q.proj q.proj) (U j) (V z)) =
      (realGeodesicJacobiMatrixDeriv g p d * (realGeodesicJacobiMatrix g p d)⁻¹) i j := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hW hWz hends i j
  dsimp only
  rw [realEndpointVelocityBranch_covariant_fderiv g p d W z hW hWz hends]
  exact realEndpoint_shapeMatrix g p d (fderiv ℝ W z)
    (realEndpointVelocityBranch_jacobi_rightInverse g p d W z hW hWz hends) i j

/-- E3: the actual endpoint energy Hessian has trace equal to the trace
of the genuine Jacobi shape operator. The only branch hypotheses describe
the true initial velocity, its C1 regularity and its true endpoint. -/
theorem realSegmentEnergy_velocityBranch_hessian_trace
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d s : ℝ)
    (W : ComplexVector n → TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (z : ComplexVector n)
    (hz : z ∈ O) (hb : z ∈ chartTarget (realGeodesicFlow g p d).proj) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ContDiffOn ℝ 1 W O → W z = p.2 →
    (∀ y ∈ O, realVelocityBaseFlow g p.proj (W y) d =
      chartInv (realGeodesicFlow g p d).proj y) →
    let q := realGeodesicFlow g p d
    let U := fun i => realTangentCoords q.proj q.proj (realGlobalParallelFrame g p d i)
    let f := fun y => s * realSegmentEnergy g d
      (⟨p.proj, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    ∑ i, (fderiv ℝ (fderiv ℝ f) z (U i) (U i) -
      fderiv ℝ f z (chartChristoffelBilin g.form q.proj z (U i) (U i))) =
      s * Matrix.trace (realGeodesicJacobiMatrixDeriv g p d * (realGeodesicJacobiMatrix g p d)⁻¹) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hW hWz hends
  let q := realGeodesicFlow g p d
  let Q := fun y => (⟨p.proj, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
  have hp : (⟨p.proj, p.2⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = p := by
    cases p
    rfl
  have hQ : ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O :=
    ((realTangentFiber_contMDiff g p.proj).of_le (by simp)).comp_contMDiffOn hW.contMDiffOn
  have hQends : ∀ y ∈ O, (Q y).proj = p.proj ∧
      (realGeodesicFlow g (Q y) d).proj = chartInv q.proj y := by
    intro y hy
    exact ⟨rfl, hends y hy⟩
  have hE := realSegmentEnergy_endpoint_covariantHessian g d s p.proj q.proj Q O hO z hz hb hQ hQends
  have hends' : (fun y => chartPt q.proj (realVelocityBaseFlow g p.proj (W y) d)) =ᶠ[𝓝 z] id := by
    filter_upwards [hO.mem_nhds hz,
      (isOpen_extChartAt_target (I := ComplexModel n) q.proj).mem_nhds hb] with y hy hby
    rw [hends y hy]
    exact (extChartAt (ComplexModel n) q.proj).right_inv hby
  have hcenter : chartPt q.proj q.proj = z := by
    have h := hends'.eq_of_nhds
    change chartPt q.proj (realVelocityBaseFlow g p.proj (W z) d) = z at h
    simpa only [realVelocityBaseFlow, hWz, hp] using h
  have hWdiff := (hW.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  dsimp only
  rw [Matrix.trace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hE, realMetricInChart_symm]
  congr 1
  have hs := realEndpointVelocityBranch_covariant_shape g p d W z hWdiff hWz hends' i i
  simpa only [hcenter, Q, q, Matrix.diag_apply] using hs

/-- E3 directly for any genuine fixed-base C1 phase branch. Its Hessian
trace is computed in the physical parallel orthonormal frame. -/
theorem realSegmentEnergy_endpoint_hessian_trace
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d s : ℝ)
    (Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (z : ComplexVector n)
    (hz : z ∈ O) (hb : z ∈ chartTarget (realGeodesicFlow g p d).proj) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O → Q z = p →
    (∀ y ∈ O, (Q y).proj = p.proj ∧ (realGeodesicFlow g (Q y) d).proj =
      chartInv (realGeodesicFlow g p d).proj y) →
    let q := realGeodesicFlow g p d
    let U := fun i => realTangentCoords q.proj q.proj (realGlobalParallelFrame g p d i)
    let f := fun y => s * realSegmentEnergy g d (Q y)
    ∑ i, (fderiv ℝ (fderiv ℝ f) z (U i) (U i) -
      fderiv ℝ f z (chartChristoffelBilin g.form q.proj z (U i) (U i))) =
      s * Matrix.trace (realGeodesicJacobiMatrixDeriv g p d * (realGeodesicJacobiMatrix g p d)⁻¹) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hQ hQz hends
  obtain ⟨W, hW, hWz, hWQ⟩ := realFixedBaseBranch_exists_velocityBranch g p Q O hO z hz hQ
    (fun y hy => (hends y hy).1) hQz
  have heq : (fun y => s * realSegmentEnergy g d (Q y)) =ᶠ[𝓝 z]
      (fun y => s * realSegmentEnergy g d
        (⟨p.proj, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    rw [hWQ y hy]
  have hdeq : fderiv ℝ (fun y => s * realSegmentEnergy g d (Q y)) =ᶠ[𝓝 z]
      fderiv ℝ (fun y => s * realSegmentEnergy g d
        (⟨p.proj, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) :=
    heq.eventuallyEq_nhds.mono (fun _ hy => hy.fderiv_eq)
  dsimp only
  rw [hdeq.fderiv_eq, heq.fderiv_eq]
  exact realSegmentEnergy_velocityBranch_hessian_trace g p d s W O hO z hz hb hW hWz
    (fun y hy => by
      change (realGeodesicFlow g _ d).proj = _
      rw [hWQ y hy]
      exact (hends y hy).2)

end Yau.LeafProofs.L19Aux
