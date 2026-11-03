import Yau.Proofs.V03LeviFormDiagonal
import Yau.Proofs.V03GaussTransport

/-! The entire actual native Gauss two-form transforms under the genuine
cotangent chart differential; diagonal agreement implies full agreement. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem gaussTwoForm_chart_change {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x x' : M.Carrier) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hz' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source) :
    scalarLeviTwoForm (gaussPotential G x) z =
      (scalarLeviTwoForm (gaussPotential G x') (cotangentChart x' (cotangentChartInv x z))).compContinuousLinearMap
        ((fderiv ℂ (fun w => cotangentChart x' (cotangentChartInv x w)) z).restrictScalars ℝ) := by
  apply scalarLeviTwoForm_eq_of_real_diagonal
    ((gaussPotential_contDiffAt hG x hz).of_le (by simp))
    ((gaussPotential_contDiffAt hG x' (cotangentChart_mapsTo x' hz')).of_le (by simp))
  exact gaussPotential_levi_chart_change hG x x' hz hz'

end Yau.Blueprint.V03Proof
