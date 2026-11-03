import Yau.Proofs.C04BoundedGeometryChartsCurvatureOperator

/-! Currying the actual curvature tensor does not enlarge its jet norms. -/
noncomputable section
open scoped ContDiff Topology
namespace Yau.Proofs.C04ChartsAux
open Yau
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

private abbrev Form (n r : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexVector n) (ComplexVector n)
private abbrev End (n : ℕ) := ComplexVector n →L[ℝ] ComplexVector n
private abbrev Conn (n : ℕ) := ComplexVector n →L[ℝ] End n

def multilinearTwoCurry (n : ℕ) : Form n 2 →L[ℝ] Conn n :=
  ((ContinuousLinearMap.compL ℝ (ComplexVector n) (Form n 1) (End n))
      (continuousMultilinearCurryFin1 ℝ (ComplexVector n) (ComplexVector n)).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => ComplexVector n) (ComplexVector n)).toContinuousLinearEquiv.toContinuousLinearMap

theorem multilinearTwoCurry_norm_le (n : ℕ) : ‖multilinearTwoCurry n‖ ≤ 1 := by
  have hN : ‖(continuousMultilinearCurryFin1 ℝ (ComplexVector n) (ComplexVector n)).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    change ‖continuousMultilinearCurryFin1 ℝ (ComplexVector n) (ComplexVector n) T‖ ≤ 1 * ‖T‖
    rw [LinearIsometryEquiv.norm_map, one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  change ‖(continuousMultilinearCurryFin1 ℝ (ComplexVector n) (ComplexVector n)).toContinuousLinearEquiv.toContinuousLinearMap.comp T.curryLeft‖ ≤ 1 * ‖T‖
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [one_mul, ContinuousMultilinearMap.curryLeft_norm] using
      mul_le_mul_of_nonneg_right hN (norm_nonneg T.curryLeft))

def multilinearThreeCurry (n : ℕ) : Form n 3 →L[ℝ] ComplexVector n →L[ℝ] Conn n :=
  ((ContinuousLinearMap.compL ℝ (ComplexVector n) (Form n 2) (Conn n))
    (multilinearTwoCurry n)).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => ComplexVector n) (ComplexVector n)).toContinuousLinearEquiv.toContinuousLinearMap

theorem multilinearThreeCurry_norm_le (n : ℕ) : ‖multilinearThreeCurry n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  change ‖(multilinearTwoCurry n).comp T.curryLeft‖ ≤ 1 * ‖T‖
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [one_mul, ContinuousMultilinearMap.curryLeft_norm] using
      mul_le_mul_of_nonneg_right (multilinearTwoCurry_norm_le n) (norm_nonneg T.curryLeft))

theorem multilinearThreeCurry_apply (T : Form n 3) (u w z : ComplexVector n) :
    multilinearThreeCurry n T u w z = T ![u, w, z] := by
  change continuousMultilinearCurryFin1 ℝ (ComplexVector n) (ComplexVector n)
    ((T.curryLeft u).curryLeft w) z = _
  rw [continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem multilinearThreeCurry_iteratedFDeriv_le (f : ComplexVector n → Form n 3)
    (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ComplexVector n) :
    ‖iteratedFDeriv ℝ m (fun y => multilinearThreeCurry n (f y)) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ := by
  exact ((multilinearThreeCurry n).norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)).trans
    (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (multilinearThreeCurry_norm_le n)
          (norm_nonneg (iteratedFDeriv ℝ m f x)))

end Yau.Proofs.C04ChartsAux
