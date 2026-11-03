import Yau.LeafProofs.L18

/-! Actual inverse-metric gradient positivity from a genuine nonzero chart derivative. -/
noncomputable section
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem real_coordinate_derivative_ne_zero {n : ℕ} {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : fderiv ℝ f z ≠ 0) : (fun i : RIdx n => rDeriv f z i) ≠ 0 := by
  intro hzero
  apply hf
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ f z v=0
  have hi (i : RIdx n) : fderiv ℝ f z (realVec i)=0 := by
    simpa only [rDeriv,Pi.zero_apply] using congrFun hzero i
  rw [← sum_realCoord_realVec v,map_sum]
  simp only [map_smul,hi,smul_zero,Finset.sum_const_zero]

theorem chartGradientPair_self_pos_of_fderiv_ne_zero {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    {f : ComplexVector n → ℝ} (hf : fderiv ℝ f z ≠ 0) : 0 < chartGradientPair g a f f z := by
  have hp := (realMetricFn_posDef g a z hz).inv.dotProduct_mulVec_pos (real_coordinate_derivative_ne_zero hf)
  simpa only [chartGradientPair,Matrix.toBilin'_apply',star_trivial] using hp

theorem scalarGradientPair_self_pos_of_chart_fderiv_ne_zero {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) {r : M.Carrier → ℝ} (hr : SmoothFn r)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hdr : fderiv ℝ (inChart a r) z ≠ 0) :
    0 < scalarGradientPair g r r (chartInv a z) := by
  rw [scalarGradientPair_eq_chart g hr hr a hz]
  exact chartGradientPair_self_pos_of_fderiv_ne_zero g a hz hdr

end Yau.Proofs.F03Aux
