import Yau.LeafProofs.L17ChartNaturality

/-! Actual native metric inequalities transport to every genuine chart
by the computed derivative congruence. -/
noncomputable section
open scoped Matrix ComplexOrder Manifold
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metric_upper_order_in_chart (α k : HermitianField M)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) {C : ℝ}
    (horder : ((C : ℂ) • gMat α (e z) - gMat k (e z)).PosSemidef) :
    ((C : ℂ) • pullbackMatrix α e z - pullbackMatrix k e z).PosSemidef := by
  let J := linearMatrix (coordinateDifferential e (e z) z)
  have hp := horder.conjTranspose_mul_mul_same J
  rw [pullbackMatrix_eq_congruence α e (e z) z (mem_extChartAt_source (e z)),
    pullbackMatrix_eq_congruence k e (e z) z (mem_extChartAt_source (e z))]
  simpa only [J, gMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using hp

theorem metric_lower_order_in_chart (α k : HermitianField M)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) {c : ℝ}
    (horder : (gMat k (e z) - (c : ℂ) • gMat α (e z)).PosSemidef) :
    (pullbackMatrix k e z - (c : ℂ) • pullbackMatrix α e z).PosSemidef := by
  let J := linearMatrix (coordinateDifferential e (e z) z)
  have hp := horder.conjTranspose_mul_mul_same J
  rw [pullbackMatrix_eq_congruence k e (e z) z (mem_extChartAt_source (e z)),
    pullbackMatrix_eq_congruence α e (e z) z (mem_extChartAt_source (e z))]
  simpa only [J, gMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using hp

end Yau.NodeProofs.F01Aux
