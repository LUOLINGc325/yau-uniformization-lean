import Yau.Proofs.P03InducedMetricMatrices
import Yau.Proofs.P03CurvatureGerms

open scoped Manifold Topology ContDiff ComplexOrder Matrix
open Filter Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

theorem antiCanonical_curvature_matrix (g : HermitianField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    curvature (r := 1) (AntiCanonicalFiber M) (antiCanonicalMetric g) a z =
      curvatureMatrix (antiCanonicalMetricMatrix g a) z := by
  apply curvatureMatrix_congr_germ
  filter_upwards [(isOpen_extChartAt_target a).mem_nhds hz] with w hw
  exact antiCanonical_metricMatrix g a hw

theorem tangentAntiCanonical_curvature_matrix (g : HermitianField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    curvature (r := n) (TangentAntiCanonicalFiber M) (tangentAntiCanonicalMetric g) a z =
      curvatureMatrix (fun w => (hMat g a w).det • hMat g a w) z := by
  apply curvatureMatrix_congr_germ
  filter_upwards [(isOpen_extChartAt_target a).mem_nhds hz] with w hw
  exact tangentAntiCanonical_metricMatrix g a hw

/-- The curvature of the descended metric on the actual tensor fibre is the
computed determinant-tensor curvature, with no tangent Nakano assumption. -/
theorem tangentAntiCanonical_curvature (g : Yau.SmoothMetric M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (i j : Fin n) :
    curvature (r := n) (TangentAntiCanonicalFiber M) (tangentAntiCanonicalMetric g.form)
        a z i j =
      (hMat g.form a z).det •
        (curvatureMatrix (hMat g.form a) z i j +
          Matrix.trace ((hMat g.form a z)⁻¹ * curvatureMatrix (hMat g.form a) z i j) •
            hMat g.form a z) := by
  rw [tangentAntiCanonical_curvature_matrix g.form a hz]
  exact L07Aux.curvatureMatrix_tensorDet (isOpen_extChartAt_target a) (hMat g.form a)
    (contDiffOn_pi.mpr fun α => contDiffOn_pi.mpr fun β => L18Aux.hMat_contDiffOn g a α β)
    (fun w hw => ne_of_gt (hMat_posDef g.form a w hw).det_pos) z hz i j

end Yau.NodeProofs.P03Aux
