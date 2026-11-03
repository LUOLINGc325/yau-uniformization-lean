import Yau.Proofs.P04RicciCharts
import Yau.Proofs.P04RicciMajorantIdentity

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem levi_log_norm_frame_identity (g : SmoothMetric M) {A : M.Carrier → ℝ}
    (hA : SmoothFn A) (hp : ∀ x, 0 < A x) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    leviC (inChart a (fun y => Real.log (A y))) z-(-leviC (logDet g.form a) z) =
      leviC (fun w => Real.log ((hMat g.form a w).det.re*inChart a A w)) z := by
  have hD : ContDiffAt ℝ 2 (logDet g.form a) z :=
    ((L18Aux.logDet_contDiffOn g a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds hz)).of_le (by simp)
  have hL : ContDiffAt ℝ 2 (inChart a (fun y => Real.log (A y))) z :=
    (((positive_log_smooth hA hp) a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hz)).of_le (by simp)
  have heq : (fun w => Real.log ((hMat g.form a w).det.re*inChart a A w)) =ᶠ[𝓝 z]
      (fun w => logDet g.form a w+inChart a (fun y => Real.log (A y)) w) := by
    filter_upwards [(isOpen_extChartAt_target a).mem_nhds hz] with w hw
    exact Real.log_mul (L18Aux.hMat_det_re_pos g.form a hw).ne' (hp (chartInv a w)).ne'
  rw [L22Aux.leviC_congr_of_eventuallyEq heq,L17Aux.leviC_add hD hL]
  abel

/-- A positive actual norm series with a positive logarithmic frame Levi in
one containing original chart gives the intrinsic original Ricci inequality. -/
theorem ricci_le_levi_log_of_containing_chart (g : SmoothMetric M) {A : M.Carrier → ℝ}
    (hA : SmoothFn A) (hp : ∀ x, 0 < A x) (x a : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source)
    (hlocal : (leviC (fun z => Real.log ((hMat g.form a z).det.re*inChart a A z))
      (chartPt a x)).PosSemidef) :
    Yau.Blueprint.HermLE (ricci g.form x) (levi (fun y => Real.log (A y)) x) := by
  let z₀ := chartPt x x
  have hz : z₀ ∈ chartTarget x := mem_extChartAt_target x
  have hi : chartInv x z₀=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hy : chartInv x z₀ ∈ (extChartAt (ComplexModel n) a).source := by rwa [hi]
  have hLevi := levi_inChart_congruence (positive_log_smooth hA hp) x a hz hy
  have hRic := ricciInChart_congruence g x a hz hy
  rw [hi] at hLevi hRic
  change (leviC (inChart x (fun y => Real.log (A y))) z₀-(-leviC (logDet g.form x) z₀)).PosSemidef
  rw [hLevi,hRic,← Matrix.sub_mul,← Matrix.mul_sub]
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  rw [levi_log_norm_frame_identity g hA hp a (z := chartPt a x)
    ((extChartAt (ComplexModel n) a).map_source hx)]
  exact hlocal

end Yau.Proofs.P04Aux
