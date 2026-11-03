import Yau.Proofs.C02NormalConnection
import Yau.Proofs.C02RadialFrameFlow

/-! Radial parallelism for the genuine smooth gauge connection. The proof
identifies the two derivatives with the native parallel/geodesic equations. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalConnection_radial_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    normalConnection g p U hU x x = 0 := by
  letI := manifold_realSmooth M
  let phase : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨p, normalInitialLinearMap p U x⟩
  let c := (realGeodesicFlow g phase 1).proj
  let Q := normalParallelCoefficients g p U hU c
  let y := normalCoordinateMap g p U c
  have hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hx)
  have hQ : DifferentiableAt ℝ Q x :=
    ((normalParallelCoefficients_smooth g p U hU c).contDiffAt hO).differentiableAt (by simp)
  have hy : DifferentiableAt ℝ y x :=
    ((normalCoordinateMap_smooth g p U hU c).contDiffAt hO).differentiableAt (by simp)
  have hline : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hyAt : HasFDerivAt y (fderiv ℝ y x) ((1 : ℝ) • x) := by
    simpa only [one_smul] using hy.hasFDerivAt
  have hyCurve : HasDerivAt (fun s : ℝ => y (s • x)) (fderiv ℝ y x x) 1 := by
    simpa only [Function.comp_def] using hyAt.comp_hasDerivAt 1 hline
  have hbase := realGeodesicFlow_baseCoords_hasDerivAt g phase 1
  have heqy : (fun s : ℝ => y (s • x)) =
      (fun s => chartPt c (realGeodesicFlow g phase s).proj) := by
    funext s
    exact congrArg (chartPt c) (normalRealMap_radial g p U x s)
  have hvel : fderiv ℝ y x x = realTangentCoords c c (realGeodesicFlow g phase 1).2 := by
    rw [heqy] at hyCurve
    exact hyCurve.unique hbase
  rw [normalConnection_eq_chart g p U hU c x hx]
  apply ContinuousLinearMap.ext
  intro z
  have hQAt : HasFDerivAt Q (fderiv ℝ Q x) ((1 : ℝ) • x) := by
    simpa only [one_smul] using hQ.hasFDerivAt
  have hQCurve : HasDerivAt (fun s : ℝ => Q (s • x)) (fderiv ℝ Q x x) 1 := by
    simpa only [Function.comp_def] using hQAt.comp_hasDerivAt 1 hline
  have hEval : HasDerivAt (fun s : ℝ => Q (s • x) z) (fderiv ℝ Q x x z) 1 :=
    (ContinuousLinearMap.apply ℝ (ComplexVector n) z).hasFDerivAt.comp_hasDerivAt 1 hQCurve
  have hpar := realParallelField_coords_hasDerivAt g phase (normalInitialLinearMap p U z) 1
  have heqQ : (fun s : ℝ => Q (s • x) z) =
      (fun s => realTangentCoords c (realGeodesicFlow g phase s).proj
        (realParallelField g phase (normalInitialLinearMap p U z) s)) := by
    funext s
    exact normalParallelCoefficients_radial g p U hU c x z s
  have hQ0 : Q x z = realTangentCoords c c (realParallelField g phase (normalInitialLinearMap p U z) 1) := by
    simpa only [one_smul] using congrFun heqQ 1
  have hDQ : fderiv ℝ Q x x z =
      -chartChristoffelBilin g.form c (chartPt c c)
        (realTangentCoords c c (realGeodesicFlow g phase 1).2) (Q x z) := by
    rw [heqQ] at hEval
    have he := hEval.unique hpar
    rw [← hQ0] at he
    exact he
  apply (normalParallelCoefficients_isInvertible g p U hU c x hx).bijective.injective
  rw [ContinuousLinearMap.zero_apply, map_zero,
    normalConnectionInChart_reconstruct g p U hU c x x z hx]
  change fderiv ℝ Q x x z + chartChristoffelBilin g.form c (y x) (fderiv ℝ y x x) (Q x z) = 0
  rw [hDQ, hvel]
  exact neg_add_cancel _

end Yau.Blueprint.C02Proof
