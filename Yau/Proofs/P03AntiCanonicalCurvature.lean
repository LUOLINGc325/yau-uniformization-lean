import Yau.Proofs.P03InducedCurvature
import Yau.Proofs.P03DeterminantLineCurvature

open scoped Manifold Topology ContDiff ComplexOrder Matrix
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

theorem antiCanonical_curvature (g : Yau.SmoothMetric M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (i j : Fin n) (α β : Fin 1) :
    curvature (r := 1) (AntiCanonicalFiber M) (antiCanonicalMetric g.form) a z i j α β =
      (hMat g.form a z).det *
        Matrix.trace ((hMat g.form a z)⁻¹ * curvatureMatrix (hMat g.form a) z i j) := by
  rw [antiCanonical_curvature_matrix g.form a hz]
  exact curvatureMatrix_determinantLine (isOpen_extChartAt_target a) (hMat g.form a)
    (contDiffOn_pi.mpr fun k => contDiffOn_pi.mpr fun l => L18Aux.hMat_contDiffOn g a k l)
    (fun w hw => ne_of_gt (hMat_posDef g.form a w hw).det_pos) z hz i j α β

end Yau.NodeProofs.P03Aux
