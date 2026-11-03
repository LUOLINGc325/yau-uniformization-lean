import Yau.Proofs.C03SourceSpeed
import Yau.Proofs.E01Matrix

/-! The frozen matrix quadratic and the actual source real metric have
their exact factor two, in the unchanged global source coordinates. -/

noncomputable section
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
open Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem ellipsoidQuadratic_source (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (z V : ComplexVector n) : ellipsoidQuadratic (gMat k z) V = hermitianNormSq (k z) V := by
  have H := L18Aux.hMat_quadratic k z (chartPt (M := ComplexEuclideanManifold n hn) z z) (WithLp.ofLp V)
  have hInv : chartInv (M := ComplexEuclideanManifold n hn) z (chartPt (M := ComplexEuclideanManifold n hn) z z) = z :=
    (extChartAt (ComplexModel n) z).left_inv (mem_extChartAt_source z)
  rw [hInv] at H
  simp only [chartVec_euclidean] at H
  have hsum : (∑ i, WithLp.ofLp V i • stdVec i) = V := sum_stdVec_coordinates V
  rw [hsum] at H
  exact congrArg Complex.re H

theorem source_realMetric_quadratic (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (z V : ComplexVector n) :
    realMetricInChart k (0 : ComplexVector n) z V V =
      2 * ellipsoidQuadratic (gMat k z) V := by
  have hz : z ∈ chartTarget (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n) := by
    rw [euclidean_chartTarget hn]
    trivial
  have hInv : chartInv (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n) z = z := by
    change (extChartAt (ComplexModel n) (0 : ComplexVector n)).symm z = z
    rw [extChartAt_model_space_eq_id]
    rfl
  rw [realMetricInChart_apply, underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec (0 : ComplexVector n) z V hz,
    chartVec_euclidean, hInv, ellipsoidQuadratic_source hn k z V]
  rfl

end Yau.Proofs.C03Aux
