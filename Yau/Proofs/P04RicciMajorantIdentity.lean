import Yau.Proofs.P04LogLeviPositivity
import Yau.LeafProofs.L17RicciNaturality

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem positive_log_smooth {A : M.Carrier → ℝ} (hA : SmoothFn A) (hp : ∀ x, 0 < A x) :
    SmoothFn (fun x => Real.log (A x)) := by
  intro a
  exact (hA a).log (fun z _ => (hp (chartInv a z)).ne')

/-- Exact Ricci sign and normalization for the SAME positive norm series.
The metric determinant here is the original computed determinant. -/
theorem levi_log_norm_minus_ricci (g : SmoothMetric M) {A : M.Carrier → ℝ}
    (hA : SmoothFn A) (hp : ∀ x, 0 < A x) (x : M.Carrier) :
    levi (fun y => Real.log (A y)) x-ricci g.form x =
      leviC (fun z => Real.log ((hMat g.form x z).det.re*inChart x A z)) (chartPt x x) := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hD : ContDiffAt ℝ 2 (logDet g.form x) (chartPt x x) :=
    ((L18Aux.logDet_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp)
  have hL : ContDiffAt ℝ 2 (inChart x (fun y => Real.log (A y))) (chartPt x x) :=
    (((positive_log_smooth hA hp) x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp)
  have heq : (fun z => Real.log ((hMat g.form x z).det.re*inChart x A z)) =ᶠ[𝓝 (chartPt x x)]
      (fun z => logDet g.form x z+inChart x (fun y => Real.log (A y)) z) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with z hz'
    exact Real.log_mul (L18Aux.hMat_det_re_pos g.form x hz').ne' (hp (chartInv x z)).ne'
  rw [L22Aux.leviC_congr_of_eventuallyEq heq,L17Aux.leviC_add hD hL]
  change leviC (inChart x (fun y => Real.log (A y))) (chartPt x x)-
      -leviC (logDet g.form x) (chartPt x x) = _
  abel

theorem ricci_le_levi_log_of_frame_psh (g : SmoothMetric M) {A : M.Carrier → ℝ}
    (hA : SmoothFn A) (hp : ∀ x, 0 < A x)
    (hframe : ∀ x, (leviC (fun z => Real.log ((hMat g.form x z).det.re*inChart x A z))
      (chartPt x x)).PosSemidef) :
    ∀ x, Yau.Blueprint.HermLE (ricci g.form x) (levi (fun y => Real.log (A y)) x) := by
  intro x
  change (levi (fun y => Real.log (A y)) x-ricci g.form x).PosSemidef
  rw [levi_log_norm_minus_ricci g hA hp]
  exact hframe x

end Yau.Proofs.P04Aux
