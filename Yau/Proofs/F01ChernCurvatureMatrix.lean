import Yau.Proofs.F01CurvatureMatrixJets
import Yau.Proofs.F01ChartGramSmooth

/-! The native scalar Chern components and the metric-lowered curvature
matrix have exactly the same index and sign conventions. -/
noncomputable section
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem curvatureMatrix_native_chern (g : HermitianField M) (hg : MetricSmooth g)
    (x : M.Carrier) (i j a b : Fin n) :
    BundleDbar.curvatureMatrix (hMat g x) (chartPt x x) i j a b =
      chernCurvature g x b a i j := by
  have hH := L17Aux.hMat_contDiffOn_of_metricSmooth g hg x
  have hdet : ∀ w ∈ chartTarget x, (hMat g x w).det ≠ 0 := by
    intro w hw
    exact ((L12Aux.hMat_posDef g x w hw).isUnit.map Matrix.detMonoidHom).ne_zero
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [curvatureMatrix_eq_actual_jets (hMat g x) (isOpen_extChartAt_target x) hH hdet hz i j]
  change (matrixBarJet (hMat g x) (chartPt x x) (stdVec j) *
      (gMat g x)⁻¹ * matrixUnbarJet (hMat g x) (chartPt x x) (stdVec i)) a b -
      wirtBar (fun w => wirt (fun y => hMat g x y a b) w (stdVec i))
        (chartPt x x) (stdVec j) = _
  have htwice : ContDiffAt ℝ 2 (fun w => hMat g x w a b) (chartPt x x) :=
    ((hH a b).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp)
  rw [← L14Aux.wirt_wirtBar_comm _ (chartPt x x) htwice (stdVec j) (stdVec i)]
  unfold chernCurvature
  have hquad : (matrixBarJet (hMat g x) (chartPt x x) (stdVec j) *
      (gMat g x)⁻¹ * matrixUnbarJet (hMat g x) (chartPt x x) (stdVec i)) a b =
      ∑ p, ∑ q, (gMat g x)⁻¹ p q *
        wirt (fun y => hMat g x y q b) (chartPt x x) (stdVec i) *
        wirtBar (fun y => hMat g x y a p) (chartPt x x) (stdVec j) := by
    simp only [Matrix.mul_apply, matrixBarJet, matrixUnbarJet, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hquad]
  ring

end Yau.NodeProofs.F01Aux
