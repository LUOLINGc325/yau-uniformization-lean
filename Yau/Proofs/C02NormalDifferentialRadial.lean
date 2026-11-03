import Yau.Proofs.C02NormalDifferentialSmooth
import Yau.Proofs.C02GeodesicVelocityParallel
import Yau.Proofs.C02RadialFieldOrigin

/-! The actual normal differential fixes the radial vector. Smoothness then
identifies its value at the origin with the identity operator. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalDifferential_radial (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    normalDifferential g p U hU x x = x := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let phase : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨p, normalInitialLinearMap p U x⟩
  let c := (realGeodesicFlow g phase 1).proj
  let y := normalCoordinateMap g p U c
  have hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hx)
  have hy := ((normalCoordinateMap_smooth g p U hU c).contDiffAt hO).differentiableAt (by simp)
  have hline : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hyAt : HasFDerivAt y (fderiv ℝ y x) ((1 : ℝ) • x) := by
    simpa only [one_smul] using hy.hasFDerivAt
  have hyCurve : HasDerivAt (fun s : ℝ => y (s • x)) (fderiv ℝ y x x) 1 := by
    simpa only [Function.comp_def] using hyAt.comp_hasDerivAt 1 hline
  have heqy : (fun s : ℝ => y (s • x)) =
      (fun s => chartPt c (realGeodesicFlow g phase s).proj) := by
    funext s
    exact congrArg (chartPt c) (normalRealMap_radial g p U x s)
  have hvel : fderiv ℝ y x x = realTangentCoords c c (realGeodesicFlow g phase 1).2 := by
    rw [heqy] at hyCurve
    exact hyCurve.unique (realGeodesicFlow_baseCoords_hasDerivAt g phase 1)
  have hRaw := realTangentCoords_mfderiv (normalRealMap g p U) x c hx x
    ((normalRealMap_smooth g p U hU).mdifferentiable (by simp) x)
  change realTangentCoords c c (rawNormalDifferential g p U x x) = fderiv ℝ y x x at hRaw
  rw [hvel] at hRaw
  have hPphase : normalParallelTotalSpace g p U hU (x, x) = realGeodesicFlow g phase 1 := by
    rw [normalParallelTotalSpace_eq_endpointVector]
    change realTransportVector (realParallelTransportFlow g (phaseDuplicate phase) 1) = _
    rw [parallelTransportFlow_velocity_diagonal]
    rfl
  have hPcoords := congrArg (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
    (realPhaseChart c q).2) hPphase
  change realTangentCoords c c (normalParallelIsometry g p U hU x x) =
    realTangentCoords c c (realGeodesicFlow g phase 1).2 at hPcoords
  have hTC : Function.Injective (realTangentCoords c c) := by
    intro v w hvw
    have he := congrArg (realFrameCLM c c) hvw
    simpa only [realFrameCLM_realTangentCoords c c (mem_chart_source _ _)] using he
  apply (normalParallelIsometry g p U hU x).injective
  rw [normalDifferential_reconstruct]
  exact hTC (hRaw.trans hPcoords.symm)

theorem normalDifferential_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    normalDifferential g p U hU 0 = ContinuousLinearMap.id ℝ (ComplexVector n) := by
  exact linearField_origin_eq_identity (normalDifferential g p U hU)
    (normalDifferential_smooth g p U hU).continuous (normalDifferential_radial g p U hU)

end Yau.Blueprint.C02Proof
