import Yau.Proofs.V03ChartKahlerTwoForm
import Yau.Proofs.V03RealBasisThreeForm

/-! The original coordinate Kähler condition is precisely closure of the
native actual metric two-form at the chart center. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem chartKahlerTwoForm_closed_center {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) :
    extDeriv (chartKahlerTwoForm g.form x) (chartPt x x) = 0 := by
  have hΩ : DifferentiableAt ℝ (chartKahlerTwoForm g.form x) (chartPt x x) :=
    ((chartKahlerTwoForm_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))).differentiableAt (by simp)
  apply threeForm_eq_zero_of_realVec
  intro a b c
  rw [extDeriv_twoForm_cyclic hΩ]
  simpa only [chartKahlerTwoForm_realVec, rDeriv] using hK x a b c

end Yau.Blueprint.V03Proof
