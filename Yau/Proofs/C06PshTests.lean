import Yau.Proofs.C06Angular
import Yau.Proofs.C06Truncation
import Yau.Blueprint.HeatSmoothing

open scoped Topology ContDiff
open Filter Set

noncomputable section

namespace Yau.Proofs.C06Aux

open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The frozen circle-majorant definition excludes a negative Levi upper test.
No continuity of the original extended-real psh function is used. -/
theorem psh_global_upperTest_levi_nonneg {u : M.Carrier → EReal} (hu : IsPsh u)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    {f : ComplexVector n → ℝ} (hf : ContDiff ℝ 2 f)
    (hcontact : u (chartInv c z) = (f z : EReal))
    (hupper : ∀ᶠ w in 𝓝 z, u (chartInv c w) ≤ (f w : EReal))
    (v : ComplexVector n) : 0 ≤ leviDirection (leviC f z) v := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz) hupper)
  let δ : ℝ := R / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hR hden
  have hmin : IsLocalMin (angularLineMean f z v) 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with r hr
    rw [angularLineMean_zero]
    have hr' : |r| < δ := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hr
    have hsmall : |r| * (‖v‖ + 1) < R :=
      (mul_lt_mul_of_pos_right hr' hden).trans_eq (div_mul_cancel₀ R hden.ne')
    have hdisc (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) :
        z + ζ • (r • v) ∈ Metric.ball z R := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        norm_smul, Real.norm_eq_abs]
      calc
        ‖ζ‖ * (|r| * ‖v‖) ≤ |r| * ‖v‖ :=
          mul_le_of_le_one_left (by positivity) hζ
        _ ≤ |r| * (‖v‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg r)
        _ < R := hsmall
    have H := hu.2.2 c z (r • v) (fun ζ hζ => (hball (hdisc ζ hζ)).1)
      (fun θ => f (z + Complex.exp (θ * Complex.I) • (r • v)))
      (hf.continuous.comp (by fun_prop))
      (fun θ => (hball (hdisc (Complex.exp (θ * Complex.I)) (by simp))).2)
    rw [hcontact] at H
    simpa only [angularLineMean, smul_comm r] using EReal.coe_le_coe_iff.mp H
  have H := second_deriv_nonneg_of_localMin hmin
    (angularMean_hasDerivAt hf z v 0).continuousAt
  rw [angularMean_second_deriv hf z v] at H
  rw [leviDirection, leviC_quadratic_re hf.contDiffAt]
  unfold complexLeviQuadratic
  linarith

/-- The actual local C² support, including supports at cut points, is enough. -/
theorem psh_upperTest_levi_nonneg {u : M.Carrier → EReal} (hu : IsPsh u)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    {f : ComplexVector n → ℝ} (hf : ContDiffAt ℝ 2 f z)
    (hcontact : u (chartInv c z) = (f z : EReal))
    (hupper : ∀ᶠ w in 𝓝 z, u (chartInv c w) ≤ (f w : EReal))
    (v : ComplexVector n) : 0 ≤ leviDirection (leviC f z) v := by
  obtain ⟨g, hg, heq⟩ := exists_contDiff_two_extension hf
  have hcontact' : u (chartInv c z) = (g z : EReal) := by
    rw [heq.eq_of_nhds]
    exact hcontact
  have hupper' : ∀ᶠ w in 𝓝 z, u (chartInv c w) ≤ (g w : EReal) := by
    filter_upwards [heq, hupper] with w hw hwu
    rwa [hw]
  rw [← leviC_congr_of_eventuallyEq heq]
  exact psh_global_upperTest_levi_nonneg hu c hz hg hcontact' hupper' v

end Yau.Proofs.C06Aux
