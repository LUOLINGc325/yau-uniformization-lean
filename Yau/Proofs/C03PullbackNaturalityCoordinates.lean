import Yau.Geometry.Flat
import Yau.LeafProofs.L23FieldMetricConnection

/-! Actual complex and real coordinate descriptions of a holomorphic
differential pullback. The source chart is the canonical Euclidean chart. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

set_option backward.isDefEq.respectTransparency false

open Yau Yau.LeafProofs.L12Aux
open scoped Topology ContDiff Manifold

variable {n : ℕ} {M : ComplexManifold n}

theorem source_chartTarget (hn : 1 ≤ n) :
    chartTarget (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n) = Set.univ := by
  change (extChartAt (ComplexModel n) (0 : ComplexVector n)).target = Set.univ
  rw [extChartAt_model_space_eq_id]
  rfl

theorem source_chartInv (hn : 1 ≤ n) (z : ComplexVector n) :
    chartInv (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n) z = z := by
  change (extChartAt (ComplexModel n) (0 : ComplexVector n)).symm z = z
  rw [extChartAt_model_space_eq_id]
  rfl

theorem source_realMetric (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (z : (ComplexEuclideanManifold n hn).Carrier) (u v : ComplexVector n) :
    realMetricInChart k (0 : ComplexVector n) z u v = 2 * ((k z).toFun u v).re := by
  have hz : z ∈ chartTarget (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n) := by
    rw [source_chartTarget hn]
    exact Set.mem_univ z
  rw [realMetricInChart_apply, underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec _ _ _ hz, realTangentEquiv_realChartVec _ _ _ hz,
    source_chartInv hn, chartVec_euclidean, chartVec_euclidean]

theorem target_realMetric_pair (h : HermitianField M) (c y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) c).source) (U V : TangentVector M y) :
    realMetricInChart h c (chartPt c y) (tangentCoords c y U) (tangentCoords c y V) =
      2 * ((h y).toFun U V).re := by
  have hz : chartPt c y ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hy
  have hinv : chartInv c (chartPt c y) = y := (extChartAt (ComplexModel n) c).left_inv hy
  have hy' : y ∈ (chartAt (ComplexVector n) c).source := by simpa only [extChartAt_source] using hy
  rw [realMetricInChart_apply, underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec _ _ _ hz, realTangentEquiv_realChartVec _ _ _ hz, hinv,
    chartVec_tangentCoords c y hy, chartVec_tangentCoords c y hy]

theorem coordinate_fderiv_complex
    {Φ : ComplexVector n → M.Carrier} {z : ComplexVector n} (c : M.Carrier)
    (hΦ : MDifferentiableAt (ComplexModel n) (ComplexModel n) Φ z)
    (hy : Φ z ∈ (extChartAt (ComplexModel n) c).source) (u : ComplexVector n) :
    fderiv ℂ (fun w => chartPt c (Φ w)) z u =
      tangentCoords c (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z u) := by
  have h := congrArg (fun L => L u)
    (mfderiv_comp (I := ComplexModel n) (I' := ComplexModel n) (I'' := ComplexModel n)
      z (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hy)) hΦ)
  rw [mfderiv_eq_fderiv] at h
  exact h

end Yau.Proofs.C03Aux.PullbackNaturality

