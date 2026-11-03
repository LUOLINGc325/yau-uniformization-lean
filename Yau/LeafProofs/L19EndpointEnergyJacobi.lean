import Yau.LeafProofs.L19EndpointEnergy

/-! Differentiating the genuine endpoint identity once gives the inverse
Jacobi matrix. No second parameter derivative of the flow is used. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- The differential of an actual initial-velocity endpoint branch is a
right inverse of the actual Jacobi differential. -/
theorem realEndpointVelocityBranch_jacobi_rightInverse
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (W : ComplexVector n → TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (z : ComplexVector n) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    DifferentiableAt ℝ W z → W z = p.2 →
    ((fun y => chartPt (realGeodesicFlow g p d).proj
      (realVelocityBaseFlow g p.proj (W y) d)) =ᶠ[𝓝 z] id) →
    ∀ u : ComplexVector n,
      realGeodesicJacobiField g p (fderiv ℝ W z u) d =
        realFrameCLM (realGeodesicFlow g p d).proj
          (realGeodesicFlow g p d).proj u := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hW hWz hends u
  let q := (realGeodesicFlow g p d).proj
  let F := fun w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
    chartPt q (realVelocityBaseFlow g p.proj w d)
  have hc : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (chartPt q) (realVelocityBaseFlow g p.proj p.2 d) :=
    contMDiffAt_extChartAt' (mem_chart_source _ _)
  have hF : DifferentiableAt ℝ F p.2 :=
    ((hc.comp p.2 (realVelocityBaseFlow_contMDiff g p.proj d p.2)).contDiffAt).differentiableAt (by simp)
  have hcomp' : HasFDerivAt (fun y => F (W y))
      ((fderiv ℝ F p.2).comp (fderiv ℝ W z)) z := by
    have hF' : HasFDerivAt F (fderiv ℝ F p.2) (W z) := by rw [hWz]; exact hF.hasFDerivAt
    exact hF'.comp z hW.hasFDerivAt
  have hId := hends.hasFDerivAt_iff.mpr (hasFDerivAt_id (𝕜 := ℝ) z)
  have hlin := hcomp'.unique hId
  have hcoords := realGeodesicJacobiField_in_chart g p (fderiv ℝ W z u) d q
    (mem_chart_source _ _)
  have hu := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L u) hlin
  change fderiv ℝ F p.2 (fderiv ℝ W z u) = u at hu
  rw [hu] at hcoords
  have ht := congrArg (realFrameCLM q q) hcoords
  rw [realFrameCLM_realTangentCoords q q (mem_chart_source _ _)] at ht
  exact ht

/-- Initial-velocity differential in the actual initial and parallel terminal
orthonormal frames. -/
def realEndpointInverseJacobiMatrix
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let q := (realGeodesicFlow g p d).proj
  exact fun i j => (realInitialOrthonormalFrame g p.proj).repr
    (L (realTangentCoords q q (realGlobalParallelFrame g p d j))) i

/-- E2: the genuine endpoint identity gives `A B = I` in the physical frames. -/
theorem realEndpointInverseJacobiMatrix_mul
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (hL : ∀ u, realGeodesicJacobiField g p (L u) d =
      realFrameCLM (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj u) :
    realGeodesicJacobiMatrix g p d * realEndpointInverseJacobiMatrix g p d L = 1 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  ext i j
  let q := (realGeodesicFlow g p d).proj
  have h := realGeodesicJacobiField_coefficients g p d
    (L (realTangentCoords q q (realGlobalParallelFrame g p d j))) i
  rw [hL, realFrameCLM_realTangentCoords q q (mem_chart_source _ _)] at h
  simpa [realEndpointInverseJacobiMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, q] using h.symm

/-- E2 identifies the actual branch differential with the actual inverse,
without postulating Jacobi nonsingularity. -/
theorem realEndpointInverseJacobiMatrix_eq_inv
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (hL : ∀ u, realGeodesicJacobiField g p (L u) d =
      realFrameCLM (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj u) :
    realEndpointInverseJacobiMatrix g p d L = (realGeodesicJacobiMatrix g p d)⁻¹ :=
  (Matrix.inv_eq_right_inv (realEndpointInverseJacobiMatrix_mul g p d L hL)).symm

/-- The actual endpoint right inverse also proves actual Jacobi
nonsingularity, including the terminal time. -/
theorem realEndpointInverseJacobiMatrix_det_ne_zero
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (hL : ∀ u, realGeodesicJacobiField g p (L u) d =
      realFrameCLM (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj u) :
    (realGeodesicJacobiMatrix g p d).det ≠ 0 := by
  have h := congrArg Matrix.det (realEndpointInverseJacobiMatrix_mul g p d L hL)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- The covariant velocity component of the actual first phase differential.
This is linear in the genuine initial tangent variation. -/
def realJacobiCovariantPhaseDifferential
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ) :
    TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →L[ℝ] ComplexVector n := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let q := realGeodesicFlow g p d
  let z := extChartAt (realPhaseModel n) q q
  let D := fderiv ℝ (realVelocityPhaseCoordinates g p d) p.2
  exact (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).comp D +
    (chartChristoffelBilin g.form q.proj z.1 z.2).comp
      ((ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).comp D)

/-- The proved time derivative of the Jacobi matrix is the covariant
component of its actual first phase differential. -/
theorem realJacobiCovariantPhaseDifferential_basis
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ) (i j : Fin (2 * n)) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    realMetricInChart g.form (realGeodesicFlow g p d).proj
      (chartPt (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj)
      (realTangentCoords (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj
        (realGlobalParallelFrame g p d i))
      (realJacobiCovariantPhaseDifferential g p d (realInitialOrthonormalFrame g p.proj j)) =
      realGeodesicJacobiMatrixDeriv g p d i j := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  rw [realGeodesicJacobiMatrixDeriv_eq_firstTerm]
  rfl

/-- Extension from actual initial orthonormal vectors to every genuine
initial variation uses linearity, not an exchange of flow derivatives. -/
theorem realJacobiCovariantPhaseDifferential_coefficients
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (i : Fin (2 * n)) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    realMetricInChart g.form (realGeodesicFlow g p d).proj
      (chartPt (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj)
      (realTangentCoords (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj
        (realGlobalParallelFrame g p d i))
      (realJacobiCovariantPhaseDifferential g p d w) =
      ∑ j, realGeodesicJacobiMatrixDeriv g p d i j *
        (realInitialOrthonormalFrame g p.proj).repr w j := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  conv_lhs => arg 2; rw [← (realInitialOrthonormalFrame g p.proj).sum_repr' w]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [realJacobiCovariantPhaseDifferential_basis]
  rw [OrthonormalBasis.repr_apply_apply]
  ring

/-- E3's matrix identity, expressed through the genuine covariant phase
differential and genuine endpoint inverse. -/
theorem realEndpoint_shapeMatrix
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (hL : ∀ u, realGeodesicJacobiField g p (L u) d =
      realFrameCLM (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj u) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ∀ i j,
    realMetricInChart g.form (realGeodesicFlow g p d).proj
      (chartPt (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj)
      (realTangentCoords (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj
        (realGlobalParallelFrame g p d i))
      (realJacobiCovariantPhaseDifferential g p d
        (L (realTangentCoords (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj
          (realGlobalParallelFrame g p d j)))) =
      (realGeodesicJacobiMatrixDeriv g p d * (realGeodesicJacobiMatrix g p d)⁻¹) i j := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro i j
  rw [← realEndpointInverseJacobiMatrix_eq_inv g p d L hL]
  exact realJacobiCovariantPhaseDifferential_coefficients g p d _ i

end Yau.LeafProofs.L19Aux
