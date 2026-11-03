import Yau.Proofs.F01LogQuotientLevi

/-! An affine time curve with the actual one-sided first jet transfers
the previously computed scalar time identities to closed-time derivatives. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

def affineTimeCurve (q₀ qdot t : ℝ) (s : ℝ) : ℝ := q₀ + (s - t) * qdot

theorem affineTimeCurve_self (q₀ qdot t : ℝ) : affineTimeCurve q₀ qdot t t = q₀ := by
  simp only [affineTimeCurve, sub_self, zero_mul, add_zero]

theorem affineTimeCurve_hasDerivAt (q₀ qdot t : ℝ) :
    HasDerivAt (affineTimeCurve q₀ qdot t) qdot t := by
  convert ((((hasDerivAt_id t).sub_const t).mul_const qdot).const_add q₀) using 1 <;>
    first | rfl | simp

theorem log_quotient_curve_hasDerivWithinAt {qcurve : ℝ → ℝ} {I : Set ℝ} {t qdot c : ℝ}
    (hq : HasDerivWithinAt qcurve qdot I t) (hpos : 0 < qcurve t) (hc : 0 < c) :
    HasDerivWithinAt (fun s => Real.log (qcurve s / c)) (qdot / qcurve t) I t := by
  convert (hq.div_const c).log (div_ne_zero hpos.ne' hc.ne') using 1
  field_simp

theorem log_quotient_derivWithin_eq_affine_deriv {qcurve : ℝ → ℝ}
    {I : Set ℝ} {t qdot c : ℝ} (hUnique : UniqueDiffWithinAt ℝ I t)
    (hq : HasDerivWithinAt qcurve qdot I t) (hpos : 0 < qcurve t) (hc : 0 < c) :
    derivWithin (fun s => Real.log (qcurve s / c)) I t =
      deriv (fun s => Real.log (affineTimeCurve (qcurve t) qdot t s / c)) t := by
  rw [(log_quotient_curve_hasDerivWithinAt hq hpos hc).derivWithin hUnique]
  have hline := log_quotient_curve_hasDerivAt (affineTimeCurve_hasDerivAt (qcurve t) qdot t)
    (by simpa only [affineTimeCurve_self] using hpos) hc
  rw [hline.deriv, affineTimeCurve_self]

end Yau.NodeProofs.F01Aux
