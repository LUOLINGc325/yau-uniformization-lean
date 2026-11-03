import Yau.LeafProofs.L19EndpointEnergyComparison

/-! Actual branch energy values, first derivative norms, path bounds and
covariant Hessian trace bounds in physical orthonormal frames. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def endpointFrameGradientSq (q : M.Carrier)
    (b : Fin (2 * n) → TangentSpace 𝓘(ℝ, ComplexVector n) q)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  ∑ i, (fderiv ℝ f z (realTangentCoords q q (b i))) ^ 2

def endpointFrameHessianTrace (g : SmoothMetric M) (q : M.Carrier)
    (b : Fin (2 * n) → TangentSpace 𝓘(ℝ, ComplexVector n) q)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  ∑ i, (fderiv ℝ (fderiv ℝ f) z (realTangentCoords q q (b i))
      (realTangentCoords q q (b i)) -
    fderiv ℝ f z (chartChristoffelBilin g.form q z
      (realTangentCoords q q (b i)) (realTangentCoords q q (b i))))

/-- Every actual geodesic segment bounds the original distance square. -/
theorem realSegmentEnergy_distance_sq_le
    (g : SmoothMetric M) (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    {d : ℝ} (hd : 0 ≤ d) :
    inducedDistance g.form p.proj (realGeodesicFlow g p d).proj ^ 2 ≤
      2 * d * realSegmentEnergy g d p := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have h := realGeodesicFlow_distFrom_le g p d
  rw [realTangentEnergy_eq_norm_sq, Real.sqrt_sq (norm_nonneg p.2), abs_of_nonneg hd] at h
  have hs := (sq_le_sq₀ (g.induced_distance_nonneg _ _)
    (mul_nonneg (norm_nonneg p.2) hd)).mpr h
  rw [realSegmentEnergy, realTangentEnergy_eq_norm_sq]
  convert hs using 1 <;> ring

/-- The norm of the actual momentum covector is the physical phase energy. -/
theorem realChartMomentum_sum_sq
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ∀ b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj),
      ∑ i, (realChartMomentum g p.proj p (realTangentCoords p.proj p.proj (b i))) ^ 2 =
        realTangentEnergy g.form p := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro b
  simp only [realChartMomentum, realMetricInChart_tangentCoords g.form p.proj p.proj
    (mem_chart_source _ _)]
  change ∑ i, ⟪p.2, b i⟫_ℝ ^ 2 = _
  rw [b.sum_sq_inner_left, realTangentEnergy_eq_norm_sq]

/-- The existence of a true C1 endpoint branch proves nonsingularity
of the true forward Jacobi matrix at its terminal time. -/
theorem realEndpointBranch_jacobi_det_ne_zero
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (z : ComplexVector n)
    (hz : z ∈ O) (hb : z ∈ chartTarget (realGeodesicFlow g p d).proj) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O → Q z = p →
    (∀ y ∈ O, (Q y).proj = p.proj ∧ (realGeodesicFlow g (Q y) d).proj =
      chartInv (realGeodesicFlow g p d).proj y) →
    (realGeodesicJacobiMatrix g p d).det ≠ 0 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hQ hQz hends
  obtain ⟨W, hW, hWz, hWQ⟩ := realFixedBaseBranch_exists_velocityBranch g p Q O hO z hz hQ
    (fun y hy => (hends y hy).1) hQz
  have he : (fun y => chartPt (realGeodesicFlow g p d).proj
      (realVelocityBaseFlow g p.proj (W y) d)) =ᶠ[𝓝 z] id := by
    filter_upwards [hO.mem_nhds hz,
      (isOpen_extChartAt_target (I := ComplexModel n) (realGeodesicFlow g p d).proj).mem_nhds hb]
      with y hy hby
    change chartPt _ (realGeodesicFlow g _ d).proj = _
    rw [hWQ y hy, (hends y hy).2]
    exact (extChartAt (ComplexModel n) (realGeodesicFlow g p d).proj).right_inv hby
  apply realEndpointInverseJacobiMatrix_det_ne_zero g p d (fderiv ℝ W z)
  exact realEndpointVelocityBranch_jacobi_rightInverse g p d W z
    ((hW.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) hWz he

/-- Actual first variation gives the exact gradient norm of the squared
branch energy in any physical endpoint orthonormal frame. -/
theorem realEndpointEnergy_frameGradientSq
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
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
    ∀ b : OrthonormalBasis (Fin (2 * n)) ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p d).proj),
    endpointFrameGradientSq (realGeodesicFlow g p d).proj b
      (fun y => 2 * d * realSegmentEnergy g d (Q y)) z =
        4 * d ^ 2 * realTangentEnergy g.form p := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hQ hQz hends b
  have hD := (realSegmentEnergy_endpoint_hasFDerivAt g d p.proj
    (realGeodesicFlow g p d).proj Q O hO z hz hb hQ hends).const_mul (2 * d)
  rw [hQz] at hD
  simp only [Function.comp_apply] at hD
  rw [endpointFrameGradientSq, hD.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, realChartMomentum_sum_sq, realGeodesicFlow_energy]
  ring

/-- The Hessian trace of the actual squared branch energy is bounded by
twice the real dimension on an actual minimizing nonsingular branch. -/
theorem realEndpointEnergy_frameHessianTrace_le
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ x, (ricci g.form x).PosSemidef)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {d : ℝ} (hd : 0 < d)
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
    inducedDistance g.form p.proj (realGeodesicFlow g p d).proj = d * ‖p.2‖ →
    endpointFrameHessianTrace g (realGeodesicFlow g p d).proj (realGlobalParallelFrame g p d)
      (fun y => 2 * d * realSegmentEnergy g d (Q y)) z ≤ 2 * (2 * n : ℕ) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hQ hQz hends hmin
  have hdet := realEndpointBranch_jacobi_det_ne_zero g p d Q O hO z hz hb hQ hQz hends
  have hcomp := realMinimizingGeodesic_shapeTrace_le_terminal g hK hR p hd hdet hmin
  have htrace := realSegmentEnergy_endpoint_hessian_trace g p d (2 * d) Q O hO z hz hb hQ hQz hends
  change _ ≤ _
  rw [show endpointFrameHessianTrace g (realGeodesicFlow g p d).proj (realGlobalParallelFrame g p d)
      (fun y => 2 * d * realSegmentEnergy g d (Q y)) z =
      (2 * d) * Matrix.trace (realGeodesicJacobiMatrixDeriv g p d * (realGeodesicJacobiMatrix g p d)⁻¹)
    from htrace]
  have h := mul_le_mul_of_nonneg_left hcomp (by positivity : 0 ≤ 2 * d)
  convert h using 1 <;> field_simp <;> ring

end Yau.LeafProofs.L19Aux
