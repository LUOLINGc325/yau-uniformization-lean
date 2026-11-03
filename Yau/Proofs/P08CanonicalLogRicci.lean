import Yau.Proofs.P04HolomorphicNormSmooth
import Yau.LeafProofs.L17RicciNaturality

/-! The nonsingular canonical logarithm has the actual computed Ricci Levi
matrix at every point where the given section is nonzero. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs Yau.Proofs.P04Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem levi_log_canonicalNormSq_at_pos (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) (x : M.Carrier)
    (hpos : 0 < canonicalNormSq g.form S x) :
    levi (fun y => Real.log (canonicalNormSq g.form S y)) x = ricci g.form x := by
  let q := canonicalNormSq g.form S
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hx : chartInv x z = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hq : SmoothFn q := canonicalNormSq_smooth g S hS
  have hq2 : ContDiffAt ℝ 2 (inChart x q) z :=
    (L18Aux.contDiffAt_inChart hq x hz).of_le (by simp)
  have hqz : inChart x q z = q x := congrArg q hx
  have hlog : ContDiffAt ℝ 2 (fun w => Real.log (inChart x q w)) z :=
    hq2.log (by rw [hqz]; exact hpos.ne')
  have hD : ContDiffAt ℝ 2 (logDet g.form x) z :=
    ((L18Aux.logDet_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp)
  have hc : ContDiffAt ℂ 2 (canonicalCoeff S x) z :=
    ((L17Holomorphic.contDiffOn_of_complexDiff (isOpen_extChartAt_target x) (hS x)).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp)
  have hcne : canonicalCoeff S x z ≠ 0 := by
    intro he
    have hzq : canonicalNormSq g.form S x = 0 := by
      simp only [canonicalNormSq, show chartPt x x = z from rfl, he, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
    exact hpos.ne' hzq
  have heq : (fun w => Real.log (inChart x q w) + logDet g.form x w) =ᶠ[𝓝 z]
      (fun w => Real.log (Complex.normSq (canonicalCoeff S x w))) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz,
      hc.continuousAt.eventually_ne hcne] with w hw hcw
    rw [show inChart x q w = ‖canonicalCoeff S x w‖ ^ 2 / (hMat g.form x w).det.re from
      canonicalNormSq_inChart g.form S x hw]
    rw [Real.log_div (pow_ne_zero _ (norm_ne_zero_iff.mpr hcw))
      (L18Aux.hMat_det_re_pos g.form x hw).ne']
    simp only [logDet, Complex.normSq_eq_norm_sq]
    ring
  have hh : leviC (fun w => Real.log (inChart x q w)) z + leviC (logDet g.form x) z = 0 := by
    rw [← L17Aux.leviC_add hlog hD, L22Aux.leviC_congr_of_eventuallyEq heq]
    exact L17Aux.leviC_log_normSq_holomorphic hc hcne
  exact eq_neg_iff_add_eq_zero.mpr hh

end Yau.NodeProofs.P08Aux
