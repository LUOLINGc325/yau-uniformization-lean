import Yau.Proofs.V03ChartKahlerTwoForm
import Yau.Proofs.V03LeviFormDiagonal
import Yau.Proofs.V03Transitions

/-! The native actual metric two-form transforms by the genuine complex
base-chart differential, with its original tangent vectors. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem chartKahlerTwoForm_chart_change {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x x' : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x)
    (hz' : chartInv x z ∈ (extChartAt (ComplexModel n) x').source) :
    chartKahlerTwoForm h x z =
      (chartKahlerTwoForm h x' (chartPt x' (chartInv x z))).compContinuousLinearMap
        ((fderiv ℂ (fun w => chartPt x' (chartInv x w)) z).restrictScalars ℝ) := by
  have ht : chartPt x' (chartInv x z) ∈ chartTarget x' :=
    (extChartAt (ComplexModel n) x').map_source hz'
  have hi : chartInv x' (chartPt x' (chartInv x z)) = chartInv x z :=
    (extChartAt (ComplexModel n) x').left_inv hz'
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, twoForm_pullback_apply, chartKahlerTwoForm_apply, chartKahlerTwoForm_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [chartTransition_fderiv_eq_coordChange x x' hz, hi,
    chartVec_transition x' x (chartInv x z) hz' ((extChartAt (ComplexModel n) x).map_target hz),
    chartVec_transition x' x (chartInv x z) hz' ((extChartAt (ComplexModel n) x).map_target hz)]

end Yau.Blueprint.V03Proof
