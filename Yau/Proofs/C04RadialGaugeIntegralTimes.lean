import Yau.Proofs.C04RadialGaugeIntegralDifferential

/-! The exact radial time derivatives of the connection and coframe. -/

noncomputable section
open Set
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radial_connection_time_derivative (conn : E → E →L[ℝ] E →L[ℝ] E)
    (hc : ContDiff ℝ ∞ conn) {R : ℝ}
    (hrel : ∀ x ∈ Metric.ball (0 : E) R, conn x x = 0)
    (v w : E) {t : ℝ} (ht : 0 < t) (hx : t • v ∈ Metric.ball (0 : E) R) :
    HasDerivAt (fun s : ℝ => s • conn (s • v) w)
      (t • radialGaugeCurvature conn (t • v) v w) t := by
  have hcurve : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const v
  have hconn := ((hc.differentiable (by simp)) (t • v)).hasFDerivAt.comp_hasDerivAt t hcurve
  have heval := hconn.clm_apply (hasDerivAt_const t w)
  have hderiv := (hasDerivAt_id t).smul heval
  have hrad := hrel (t • v) hx
  rw [map_smul] at hrad
  have hcv : conn (t • v) v = 0 := (smul_eq_zero.mp hrad).resolve_left ht.ne'
  have hdc := radial_connection_differential conn hc hrel hx w
  rw [map_smul] at hdc
  have hcoef : conn (t • v) w + t • (fderiv ℝ conn (t • v) v) w =
      t • radialGaugeCurvature conn (t • v) v w := by
    calc
      conn (t • v) w + t • (fderiv ℝ conn (t • v) v) w =
          (t • (fderiv ℝ conn (t • v) w) v + conn (t • v) w) +
            (t • (fderiv ℝ conn (t • v) v) w - t • (fderiv ℝ conn (t • v) w) v) := by abel
      _ = t • (fderiv ℝ conn (t • v) v) w - t • (fderiv ℝ conn (t • v) w) v := by
        rw [hdc, zero_add]
      _ = t • radialGaugeCurvature conn (t • v) v w := by
        simp only [radialGaugeCurvature, hcv, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero, add_zero, sub_zero, smul_sub]
  simp only [id_eq, Function.comp_apply, map_zero, add_zero, one_smul] at hderiv
  change HasDerivAt (fun s : ℝ => s • conn (s • v) w)
    (t • (fderiv ℝ conn (t • v) v) w + conn (t • v) w) t at hderiv
  have hcoef' : t • (fderiv ℝ conn (t • v) v) w + conn (t • v) w =
      t • radialGaugeCurvature conn (t • v) v w := (add_comm _ _).trans hcoef
  rw [hcoef'] at hderiv
  exact hderiv

theorem radial_coframe_time_derivative (conn : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] E) (hc : ContDiff ℝ ∞ conn) (hA : ContDiff ℝ ∞ A) {R : ℝ}
    (hconn : ∀ x ∈ Metric.ball (0 : E) R, conn x x = 0)
    (hrel : ∀ x ∈ Metric.ball (0 : E) R, A x x = x)
    (htorsion : ∀ x ∈ Metric.ball (0 : E) R, ∀ u w,
      (fderiv ℝ A x u) w - (fderiv ℝ A x w) u + conn x u (A x w) - conn x w (A x u) = 0)
    (v w : E) {t : ℝ} (ht : 0 < t) (hx : t • v ∈ Metric.ball (0 : E) R) :
    HasDerivAt (fun s : ℝ => s • A (s • v) w - s • w)
      (t • conn (t • v) w v) t := by
  have hcurve : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const v
  have hmap := ((hA.differentiable (by simp)) (t • v)).hasFDerivAt.comp_hasDerivAt t hcurve
  have heval := hmap.clm_apply (hasDerivAt_const t w)
  have hderiv := ((hasDerivAt_id t).smul heval).sub ((hasDerivAt_id t).smul_const w)
  have hrad := hconn (t • v) hx
  rw [map_smul] at hrad
  have hcv : conn (t • v) v = 0 := (smul_eq_zero.mp hrad).resolve_left ht.ne'
  have hAv : A (t • v) v = v := by
    have hh := hrel (t • v) hx
    rw [map_smul] at hh
    have hh' := congrArg (fun y : E => t⁻¹ • y) hh
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hh'
  have htor := htorsion (t • v) hx v w
  simp only [hcv, hAv, ContinuousLinearMap.zero_apply, add_zero] at htor
  have hArad := radial_coframe_differential A hA hrel hx w
  rw [map_smul] at hArad
  have hcoef : A (t • v) w + t • (fderiv ℝ A (t • v) v) w - w =
      t • conn (t • v) w v := by
    have htor' : (fderiv ℝ A (t • v) v) w =
        (fderiv ℝ A (t • v) w) v + conn (t • v) w v := by
      calc
        (fderiv ℝ A (t • v) v) w =
            ((fderiv ℝ A (t • v) v) w - (fderiv ℝ A (t • v) w) v - conn (t • v) w v) +
              ((fderiv ℝ A (t • v) w) v + conn (t • v) w v) := by abel
        _ = _ := by rw [htor, zero_add]
    rw [htor', smul_add]
    calc
      A (t • v) w + (t • (fderiv ℝ A (t • v) w) v + t • conn (t • v) w v) - w =
          (t • (fderiv ℝ A (t • v) w) v + A (t • v) w) + t • conn (t • v) w v - w := by abel
      _ = _ := by rw [hArad]; abel
  simp only [id_eq, Function.comp_apply, map_zero, add_zero, one_smul] at hderiv
  change HasDerivAt (fun s : ℝ => s • A (s • v) w - s • w)
    (t • (fderiv ℝ A (t • v) v) w + A (t • v) w - w) t at hderiv
  have hcoef' : t • (fderiv ℝ A (t • v) v) w + A (t • v) w - w =
      t • conn (t • v) w v := by
    calc
      _ = A (t • v) w + t • (fderiv ℝ A (t • v) v) w - w := by abel
      _ = _ := hcoef
  rw [hcoef'] at hderiv
  exact hderiv

end Yau.Proofs.C04Aux
