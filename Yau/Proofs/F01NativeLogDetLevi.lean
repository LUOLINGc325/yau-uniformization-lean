import Yau.Proofs.F01OrdinaryPullback
import Yau.Proofs.F01ScalarLeviLinearity

/-! The native determinant quotient is a scalar: its actual Levi form
is the difference of the two original Ricci forms. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem levi_logdet_ratio_native (k α : HermitianField M)
    (hk : MetricSmooth k) (hα : MetricSmooth α) (x : M.Carrier) :
    levi (fun y => Real.log ((gMat k y).det.re / (gMat α y).det.re)) x = -ricci k x + ricci α x := by
  let e := ordinaryChart x
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have he := (ordinaryChart_contMDiffOn x).mdifferentiableOn (by simp)
  have hei := (ordinaryChart_inverse_contMDiffOn x).mdifferentiableOn (by simp)
  have hEq : inChart x (fun y => Real.log ((gMat k y).det.re / (gMat α y).det.re)) =ᶠ[𝓝 z]
      (fun w => logDet k x w - logDet α x w) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    have hwe : w ∈ e.source := by rw [ordinaryChart_source]; exact hw
    have hr := pullbackMatrix_determinant_ratio k α e he hei (e w) hwe (mem_extChartAt_source (e w))
    change (pullbackMatrix k e w).det.re / (pullbackMatrix α e w).det.re =
      (gMat k (e w)).det.re / (gMat α (e w)).det.re at hr
    rw [ordinaryChart_pullbackMatrix k x hw, ordinaryChart_pullbackMatrix α x hw,
      ordinaryChart_apply] at hr
    change Real.log ((gMat k (chartInv x w)).det.re / (gMat α (chartInv x w)).det.re) =
      Real.log (hMat k x w).det.re - Real.log (hMat α x w).det.re
    rw [← hr, Real.log_div (Yau.LeafProofs.L12Aux.hMat_det_re_pos k x hw).ne'
      (Yau.LeafProofs.L12Aux.hMat_det_re_pos α x hw).ne']
  have hK : ContDiffAt ℝ 2 (logDet k x) z :=
    ((logDet_contDiffOn_of_metricSmooth k hk x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hA : ContDiffAt ℝ 2 (logDet α x) z :=
    ((logDet_contDiffOn_of_metricSmooth α hα x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  change leviC (inChart x (fun y => Real.log ((gMat k y).det.re / (gMat α y).det.re))) z = _
  rw [Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq hEq, leviC_sub hK hA]
  simp only [ricci, neg_neg]
  rfl

end Yau.NodeProofs.F01Aux
