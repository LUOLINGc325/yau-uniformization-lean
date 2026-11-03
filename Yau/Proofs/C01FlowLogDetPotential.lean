import Yau.Proofs.C01ChartDetRatio

/-! The original scalar potential P supplies the exact time derivative
of the log determinant in every fixed spatial chart.  The common frame
Jacobian cancels before any differentiation. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_chart_logDet_identity
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) {t : ℝ} (ht : 0 ≤ t) :
    logDet (h t) x z = P (chartInv x z) t + logDet X.metric.form x z := by
  obtain ⟨_, _, _, _, _, _, _, _, hP, _⟩ := hflow
  have hp := hP (chartInv x z) t ht
  have hratio := hMat_determinant_ratio_center (h t) X.metric.form x z hz
  rw [← hratio] at hp
  have hnum : 0 < (hMat (h t) x z).det.re :=
    (Complex.pos_iff.mp (hMat_posDef (h t) x z hz).det_pos).1
  have hden : 0 < (hMat X.metric.form x z).det.re :=
    (Complex.pos_iff.mp (hMat_posDef X.metric.form x z hz).det_pos).1
  rw [Real.log_div hnum.ne' hden.ne'] at hp
  change Real.log (hMat (h t) x z).det.re =
    P (chartInv x z) t + Real.log (hMat X.metric.form x z).det.re
  linarith

theorem localizedFlow_chart_negativeLogDet_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => -logDet (h s) x z)
      (scalarCurvature (h t) (chartInv x z)) t := by
  have hP := hflow
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdP, _⟩ := hP
  have hd := ((hdP (chartInv x z) t ht.le).1.hasDerivAt (Ici_mem_nhds ht)).neg
  have hnew := hd.sub_const (logDet X.metric.form x z)
  have hgerm : (fun s => -logDet (h s) x z) =ᶠ[𝓝 t]
      (fun s => -P (chartInv x z) s - logDet X.metric.form x z) := by
    filter_upwards [Ici_mem_nhds ht] with s hs
    rw [localizedFlow_chart_logDet_identity hflow x z hz hs]
    ring
  simpa only [neg_neg] using! hnew.congr_of_eventuallyEq hgerm

end Yau.NodeProofs.C01Aux
