import Yau.Proofs.C03ChernGaugeContraction
import Yau.Proofs.G01ChernCurvature

/-! The computed metric-lowered matrix is exactly the project's Chern tensor,
with its original conjugate-linear-first fibre convention. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.LeafProofs Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem curvatureMatrix_chernInChart
    (h : HermitianField M) (hs : MetricSmooth h) (c : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget c) (i j k l : Fin n) :
    BundleDbar.curvatureMatrix (hMat h c) z k l j i = chernInChart h c z i j k l := by
  calc
    BundleDbar.curvatureMatrix (hMat h c) z k l j i =
        (hMat h c z * chernF h c z k l) j i := by
      unfold BundleDbar.curvatureMatrix chernF chernA
      rw [Matrix.mul_neg]
      rfl
    _ = _ := chernF_lower h hs c z hz i j k l

theorem bisectionalForm_eq_matrixCurvatureQuadratic
    (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier)
    (u a : ComplexVector n) :
    bisectionalForm h x u a =
      (matrixCurvatureQuadratic (BundleDbar.curvatureMatrix (hMat h x) (chartPt x x))
        (WithLp.ofLp u) (WithLp.ofLp a)).re := by
  unfold bisectionalForm
  apply congrArg Complex.re
  rw [matrixCurvatureQuadratic_fourfold]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have H := curvatureMatrix_chernInChart h hs x (chartPt x x)
    (mem_extChartAt_target x) i j k l
  change BundleDbar.curvatureMatrix (hMat h x) (chartPt x x) k l j i =
    chernCurvature h x i j k l at H
  exact congrArg (fun c => c * u i * star (u j) * a k * star (a l)) H.symm

end Yau.Proofs.C03Aux.ChernGauge
