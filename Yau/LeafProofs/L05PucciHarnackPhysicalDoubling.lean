import Yau.LeafProofs.L05PucciHarnackDoubling
import Yau.LeafProofs.L05PucciHarnackParabolicGeometry

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_positive_ball_doubles {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {c : Space n} {r t0 H : ℝ} (hr : 0 < r) (hH : 0 < H)
    (hclosed : harnackClosed c (3*r) t0 (r^2) ⊆ unitClosed n)
    (hopen : harnackOpen c (3*r) t0 (r^2) ⊆ unitOpen n)
    (hBall : ∀ x∈Metric.closedBall c r, H ≤ u (x,t0)) :
    ∀ x∈Metric.closedBall c (2*r), harnackDoublingBeta n ell L*H ≤ u (x,t0+r^2) := by
  let F := harnackAffine c r (t0-r^2) (r^2)
  let U := fun z => u (F z)
  have hr2 := sq_pos_of_ne_zero hr.ne'
  have hMap : MapsTo F (harnackClosed 0 3 0 1) (unitClosed n) := by
    intro z hz
    apply hclosed
    have h := (harnack_parabolic_closed_mem_iff (a := t0) c hr 3 0 1 z).mpr hz
    simpa only [mul_zero,add_zero,mul_one,mul_comm] using h
  have hMapOpen : MapsTo F (harnackOpen 0 3 0 1) (unitOpen n) := by
    intro z hz
    apply hopen
    have h := (harnack_parabolic_open_mem_iff (a := t0) c hr 3 0 1 z).mpr hz
    simpa only [mul_zero,add_zero,mul_one,mul_comm] using h
  have hPull := harnack_super_affine_pullback hell.le hL hu.2.2 c (a := t0-r^2)
    hr hr2 (by norm_num : (0 : ℝ) < 1) hMapOpen
  simp only [div_self hr2.ne',one_mul,mul_zero,div_one] at hPull
  have hU : ContinuousOn U (harnackClosed 0 3 0 1) ∧
      (∀ z∈harnackClosed 0 3 0 1, 0 ≤ U z) ∧
      viscositySuper (harnackOpen 0 3 0 1)
        (fun A _ => harnackPucciMinus ell L A) (fun _ => 0) U :=
    ⟨hu.1.comp (harnack_affine_contDiff c r (t0-r^2) (r^2)).continuous.continuousOn hMap,
      fun z hz => hu.2.1 _ (hMap hz),hPull⟩
  have hRefBall : ∀ x∈Metric.closedBall (0 : Space n) 1, H ≤ U (x,0) := by
    intro x hx
    have hxNorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hPhysical : c+r • x∈Metric.closedBall c r := by
      simp only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos hr]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hxNorm hr.le
    change H ≤ u (harnackAffine c r (t0-r^2) (r^2) (x,0))
    rw [harnack_parabolic_affine_apply]
    simpa only [mul_zero,add_zero] using hBall _ hPhysical
  have hRef := harnack_reference_doubling hell hL hH hU hRefBall
  intro x hx
  let y : Space n := r⁻¹ • (x-c)
  have hy : y∈Metric.closedBall (0 : Space n) 2 := by
    have hxNorm : ‖x-c‖ ≤ 2*r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hMul := mul_le_mul_of_nonneg_left hxNorm (inv_nonneg.mpr hr.le)
    change dist y 0 ≤ 2
    simp only [dist_zero_right,y,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      r⁻¹*‖x-c‖ ≤ r⁻¹*(2*r) := hMul
      _ = 2 := by field_simp
  have hSpace : c+r • y=x := by
    dsimp only [y]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]
  have hValue := hRef y hy
  change harnackDoublingBeta n ell L*H ≤ u (harnackAffine c r (t0-r^2) (r^2) (y,1)) at hValue
  rw [harnack_parabolic_affine_apply,hSpace] at hValue
  simpa only [mul_one] using hValue

end Yau.LeafProofs.L05Aux
