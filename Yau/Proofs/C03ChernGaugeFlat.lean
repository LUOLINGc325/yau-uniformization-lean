import Yau.Geometry.Flat
import Yau.LeafProofs.L17ChartNaturality
import Yau.Proofs.C03ChernGaugeRaising

/-! On the Euclidean source the actual metric matrix is the same in every
canonical chart, and its quadratic values are intrinsic Hermitian norms. -/

noncomputable section
open scoped Manifold Matrix ComplexOrder

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.LeafProofs L12Aux L17Aux Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem flat_chartPt (hn : 1 ≤ n)
    (x z : (ComplexEuclideanManifold n hn).Carrier) : chartPt x z = z := by
  change (extChartAt (ComplexModel n) (x : ComplexVector n)) z = z
  rw [extChartAt_model_space_eq_id]
  rfl

theorem flat_chartInv (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier) (z : ComplexVector n) : chartInv x z = z := by
  change (extChartAt (ComplexModel n) (x : ComplexVector n)).symm z = z
  rw [extChartAt_model_space_eq_id]
  rfl

theorem flat_hMat_apply (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (x z : (ComplexEuclideanManifold n hn).Carrier) (i j : Fin n) :
    hMat k x z i j = (k z).toFun (stdVec i) (stdVec j) := by
  unfold hMat
  rw [flat_chartInv hn, chartVec_euclidean, chartVec_euclidean]

theorem flat_hMat_eq_gMat (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (x z : (ComplexEuclideanManifold n hn).Carrier) : hMat k x z = gMat k z := by
  unfold gMat
  rw [flat_chartPt hn]
  ext i j
  rw [flat_hMat_apply hn, flat_hMat_apply hn]

theorem flat_norm_quadratic (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (z : (ComplexEuclideanManifold n hn).Carrier) (v : ComplexVector n) :
    ellipsoidQuadratic (gMat k z) v = hermitianNormSq (k z) v := by
  have he := hMat_quadratic_chartVec k z z (by
    simpa only [extChartAt_source] using mem_chart_source (ComplexVector n) z) v
  rw [chartVec_euclidean] at he
  exact congrArg Complex.re he

theorem flat_raised_norm (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (z : (ComplexEuclideanManifold n hn).Carrier) (ξ : ComplexVector n) :
    hermitianNormSq (k z)
        (WithLp.toLp 2 (star (WithLp.ofLp (matrixFiberMap (gMat k z)⁻¹ᵀ ξ)))) =
      dualNormMat (gMat k z) ξ := by
  rw [← flat_norm_quadratic hn]
  exact raised_quadratic_eq_dualNormMat (gMat k z) (L12Aux.hMat_isHermitian k z (chartPt z z))
    ((L12Aux.hMat_posDef k z (chartPt z z) (mem_extChartAt_target z)).isUnit.map Matrix.detMonoidHom) ξ

end Yau.Proofs.C03Aux.ChernGauge
