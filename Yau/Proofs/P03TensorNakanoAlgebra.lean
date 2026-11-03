import Yau.Proofs.P03InducedCurvature

open scoped Manifold Topology ContDiff ComplexOrder Matrix
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

/-- Pointwise Demailly--Skoda applied to the actual descended tensor metric.
The input is Griffiths nonnegativity of the computed tangent curvature. -/
theorem tangentAntiCanonical_nakano_nonnegative_at
    (g : Yau.SmoothMetric M) (a : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a)
    (hG : ∀ ξ v : ComplexVector n,
      0 ≤ griffithsQuadratic (curvatureMatrix (hMat g.form a) z) ξ v)
    (U : Fin n → Fin n → ℂ) :
    0 ≤ nakanoQuadratic
      (curvature (r := n) (TangentAntiCanonicalFiber M) (tangentAntiCanonicalMetric g.form) a z) U := by
  let x := chartInv a z
  have hx : x ∈ (extChartAt (ComplexModel n) a).source :=
    (extChartAt (ComplexModel n) a).map_target hz
  let b := determinantFrameBasis a x hx
  have hGram : hMat g.form a z = hermitianGram (g.form x) b := by
    have hi : chartPt a x = z := (extChartAt (ComplexModel n) a).right_inv hz
    rw [← hi]
    exact hMat_chartFrameGram g.form a x hx
  have hcurv : curvature (r := n) (TangentAntiCanonicalFiber M)
      (tangentAntiCanonicalMetric g.form) a z = fun i j =>
        (hMat g.form a z).det • (curvatureMatrix (hMat g.form a) z i j +
          Matrix.trace ((hMat g.form a z)⁻¹ * curvatureMatrix (hMat g.form a) z i j) •
            hMat g.form a z) := by
    funext i j
    exact tangentAntiCanonical_curvature g a hz i j
  rw [hcurv, L07Aux.nakanoQuadratic_smul_real _ (hMat g.form a z).det
    (by rw [hGram]; exact L07Aux.hermitianGram_det_im _ _) U]
  apply mul_nonneg
  · exact (Complex.nonneg_iff.mp (hMat_posDef g.form a z hz).posSemidef.det_nonneg).1
  · rw [hGram]
    exact L07Aux.skoda_hermitianGram_nonneg (g.form x) b
      (curvatureMatrix (hMat g.form a) z) hG U

end Yau.NodeProofs.P03Aux
