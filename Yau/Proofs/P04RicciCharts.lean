import Yau.Proofs.P04LeviCharts
import Yau.Proofs.P04LocalCanonicalRepresentative
import Yau.LeafProofs.L14Transitions

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual Ricci matrices have the same genuine original-chart
congruence as Levi matrices. No curvature transformation law is assumed. -/
theorem ricciInChart_congruence (g : SmoothMetric M) (a b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    -leviC (logDet g.form a) z =
      (L17Aux.linearMatrix (fderiv ℂ (fun w => chartPt b (chartInv a w)) z))ᴴ*
        (-leviC (logDet g.form b) (chartPt b (chartInv a z)))*
      L17Aux.linearMatrix (fderiv ℂ (fun w => chartPt b (chartInv a w)) z) := by
  let T : ComplexVector n → ComplexVector n := fun w => chartPt b (chartInv a w)
  have hT : ContDiffAt ℂ 3 T z := (L18Aux.chartTransition_contDiffAt a b hz hy).of_le (by simp)
  have htarget : T z ∈ chartTarget b := (extChartAt (ComplexModel n) b).map_source hy
  have hG : ContDiffAt ℝ 2 (logDet g.form b) (T z) :=
    ((L18Aux.logDet_contDiffOn g b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds htarget)).of_le (by simp)
  have hU := (canonicalOverlap_isOpen b a).mem_nhds ⟨hz,hy⟩
  have hpos : ∀ᶠ w in 𝓝 z, 0 < (hMat g.form b (T w)).det.re := by
    filter_upwards [hU] with w hw
    exact L18Aux.hMat_det_re_pos g.form b ((extChartAt (ComplexModel n) b).map_source hw.2)
  have hJ : (L17Aux.linearMatrix (fderiv ℂ T z)).det ≠ 0 :=
    L17Aux.linearMatrix_det_ne_zero _ (chartTransition_fderiv_injective a b hz hy)
  have heq : logDet g.form a =ᶠ[𝓝 z]
      (fun w => Real.log (((L17Aux.linearMatrix (fderiv ℂ T w))ᴴ*
        hMat g.form b (T w)*L17Aux.linearMatrix (fderiv ℂ T w)).det.re)) := by
    filter_upwards [hU] with w hw
    have hoverlap : w ∈ L14Aux.bundleChartOverlap (r := 1) (CanonicalCoefficients M) b a := by
      change w ∈ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) a ∧
        chartInv a w ∈ L14Aux.bundleChartSource (r := 1) (CanonicalCoefficients M) b
      rwa [coefficient_localDomain,coefficient_bundleChartSource]
    have H := L14Aux.hMat_overlap (CanonicalCoefficients M) g.form b a w hoverlap
    change hMat g.form a w=(L17Aux.linearMatrix (fderiv ℂ T w))ᴴ*
      hMat g.form b (T w)*L17Aux.linearMatrix (fderiv ℂ T w) at H
    unfold logDet
    rw [H]
  rw [L22Aux.leviC_congr_of_eventuallyEq heq,L17Aux.leviC_logdet_congruence hT hG hpos hJ]
  simp only [Matrix.mul_neg,Matrix.neg_mul]
  rfl

end Yau.Proofs.P04Aux
