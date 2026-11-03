import Yau.LeafProofs.L05PucciHarnackBallPersistence
import Yau.LeafProofs.L05PucciHarnackParabolicGeometry

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackStackDuration (m : ℕ) : ℝ := 4*(m : ℝ)+3
def harnackStackBeta (n : ℕ) (ell L : ℝ) (m : ℕ) : ℝ :=
  (7/16 : ℝ)^3*Real.exp (-harnackBallDecay n ell L (2*Real.sqrt (2*n))*harnackStackDuration m)

theorem harnack_stackDuration_pos (m : ℕ) : 0 < harnackStackDuration m := by
  unfold harnackStackDuration
  positivity

theorem harnack_stackBeta_pos (n : ℕ) (ell L : ℝ) (m : ℕ) :
    0 < harnackStackBeta n ell L m := mul_pos (by norm_num) (Real.exp_pos _)

theorem harnack_positive_ball_stack {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {c : Space n} {r t0 H : ℝ} (hr : 0 < r) (hH : 0 < H) (m : ℕ)
    (hclosed : harnackClosed c (2*Real.sqrt (2*n)*r) t0 (harnackStackDuration m*r^2) ⊆ unitClosed n)
    (hopen : harnackOpen c (2*Real.sqrt (2*n)*r) t0 (harnackStackDuration m*r^2) ⊆ unitOpen n)
    (hBall : ∀ x∈Metric.closedBall c (2*Real.sqrt (2*n)*r), H ≤ u (x,t0)) :
    ∀ p∈Metric.closedBall c ((3/2)*Real.sqrt (2*n)*r) ×ˢ
      Icc t0 (t0+harnackStackDuration m*r^2), harnackStackBeta n ell L m*H ≤ u p := by
  let F := harnackAffine c r (t0-r^2) (r^2)
  let U := fun z => u (F z)
  have hr2 := sq_pos_of_ne_zero hr.ne'
  have hR : 0 < 2*Real.sqrt (2*n) := by
    have hNat : (0 : ℝ) < n := by exact_mod_cast hn
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hMap : MapsTo F (harnackClosed 0 (2*Real.sqrt (2*n)) 0 (harnackStackDuration m)) (unitClosed n) := by
    intro z hz
    apply hclosed
    have h := (harnack_parabolic_closed_mem_iff (a := t0) c hr (2*Real.sqrt (2*n)) 0 (harnackStackDuration m) z).mpr hz
    simpa only [mul_zero,add_zero,mul_comm] using h
  have hMapOpen : MapsTo F (harnackOpen 0 (2*Real.sqrt (2*n)) 0 (harnackStackDuration m)) (unitOpen n) := by
    intro z hz
    apply hopen
    have h := (harnack_parabolic_open_mem_iff (a := t0) c hr (2*Real.sqrt (2*n)) 0 (harnackStackDuration m) z).mpr hz
    simpa only [mul_zero,add_zero,mul_comm] using h
  have hPull := harnack_super_affine_pullback hell.le hL hu.2.2 c (a := t0-r^2)
    hr hr2 (by norm_num : (0 : ℝ) < 1) hMapOpen
  simp only [div_self hr2.ne',one_mul,mul_zero,div_one] at hPull
  have hU : ContinuousOn U (harnackClosed 0 (2*Real.sqrt (2*n)) 0 (harnackStackDuration m)) ∧
      (∀ z∈harnackClosed 0 (2*Real.sqrt (2*n)) 0 (harnackStackDuration m), 0 ≤ U z) ∧
      viscositySuper (harnackOpen 0 (2*Real.sqrt (2*n)) 0 (harnackStackDuration m))
        (fun A _ => harnackPucciMinus ell L A) (fun _ => 0) U :=
    ⟨hu.1.comp (harnack_affine_contDiff c r (t0-r^2) (r^2)).continuous.continuousOn hMap,
      fun z hz => hu.2.1 _ (hMap hz),hPull⟩
  have hRefBall : ∀ x∈Metric.closedBall (0 : Space n) (2*Real.sqrt (2*n)), H ≤ U (x,0) := by
    intro x hx
    have hxNorm : ‖x‖ ≤ 2*Real.sqrt (2*n) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hPhysical : c+r • x∈Metric.closedBall c (2*Real.sqrt (2*n)*r) := by
      simp only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos hr]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxNorm hr.le
    change H ≤ u (harnackAffine c r (t0-r^2) (r^2) (x,0))
    rw [harnack_parabolic_affine_apply]
    simpa only [mul_zero,add_zero] using hBall _ hPhysical
  have hRef := harnack_reference_ball_persistence hell hL hR (harnack_stackDuration_pos m) hH hU hRefBall
  intro p hp
  let z := harnackAffineInv c r (t0-r^2) (r^2) p
  have hFz : F z=p := harnack_affine_apply_inv hr.ne' hr2.ne' p
  have hTarget : z∈harnackClosed (0 : Space n) (3*(2*Real.sqrt (2*n))/4) 0 (harnackStackDuration m) := by
    apply (harnack_parabolic_closed_mem_iff (a := t0) c hr
      (3*(2*Real.sqrt (2*n))/4) 0 (harnackStackDuration m) z).mp
    change F z∈harnackClosed c (r*(3*(2*Real.sqrt (2*n))/4)) (t0+r^2*0) (r^2*harnackStackDuration m)
    rw [hFz]
    have hRad : r*(3*(2*Real.sqrt (2*n))/4)=(3/2)*Real.sqrt (2*n)*r := by ring
    rw [hRad,mul_zero,add_zero,mul_comm (r^2) (harnackStackDuration m)]
    exact hp
  have hPoint := hRef z.1 hTarget.1 z.2 (by simpa only [zero_add] using hTarget.2)
  change harnackStackBeta n ell L m*H ≤ u (F z) at hPoint
  rwa [hFz] at hPoint

end Yau.LeafProofs.L05Aux
