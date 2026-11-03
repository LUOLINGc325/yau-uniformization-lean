import Yau.LeafProofs.L05PucciHarnackBumpResidual
import Yau.LeafProofs.L05PucciHarnackCylinderLocalization

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackDoublingDecay (n : ℕ) (ell L : ℝ) : ℝ :=
  harnackBumpDecay ell 1 (8+2*L*(2*n)+8*ell)

def harnackDoublingBeta (n : ℕ) (ell L : ℝ) : ℝ := Real.exp (-harnackDoublingDecay n ell L)

def harnackDoublingPhi (n : ℕ) (ell L : ℝ) (H : ℝ) (p : Point n) : ℝ :=
  H*harnackBump (fun _ => 1) (fun t => 1+8*t) (fun _ => 0) (harnackDoublingDecay n ell L) 0 p

theorem harnack_doublingBeta_bounds {n : ℕ} {ell L : ℝ} (hell : 0 < ell) :
    0 < harnackDoublingBeta n ell L ∧ harnackDoublingBeta n ell L < 1 := by
  have hDecay : 0 < harnackDoublingDecay n ell L := harnack_bumpDecay_pos hell (by norm_num)
  exact ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos hDecay)⟩

theorem harnack_doublingPhi_contDiff (n : ℕ) (ell L H : ℝ) :
    ContDiff ℝ 2 (harnackDoublingPhi n ell L H) :=
  contDiff_const.mul (harnack_bump_contDiff contDiff_const
    (contDiff_const.add (contDiff_const.mul contDiff_id)) contDiff_const _ _)

theorem harnack_doublingPhi_residual {n : ℕ} {ell L H : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hH : 0 ≤ H) (p : Point n)
    (hp : p∈harnackClosed 0 3 0 1) :
    timeD univ (harnackDoublingPhi n ell L H) p-
      harnackPucciMinus ell L (hessian (harnackDoublingPhi n ell L H) p) ≤ 0 := by
  have hTime : p.2∈Icc (0 : ℝ) 1 := by simpa only [zero_add] using hp.2
  have hNorm : ‖p.1‖ ≤ 3 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
  have hs : ContDiff ℝ 2 (fun t : ℝ => 1+8*t) := contDiff_const.add (contDiff_const.mul contDiff_id)
  have hds : HasDerivAt (fun t : ℝ => 1+8*t) 8 p.2 := by
    convert! ((hasDerivAt_id p.2).const_mul 8).const_add 1 using 1
    simp only [mul_one]
  have hSeed := harnack_bump_residual hell hL
    (show ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) from contDiff_const) hs
    (show ContDiff ℝ 2 (fun _ : ℝ => (0 : Space n)) from contDiff_const)
    (smin := 1) (kappa := 8) (R := 3) (V := 0) (by norm_num) 0 p
    (by norm_num) (by nlinarith [hTime.1])
    (by rw [hds.deriv])
    (by simpa only [sub_zero] using hNorm) (by simp)
  have hB := harnack_bump_contDiff (show ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) from contDiff_const)
    hs (show ContDiff ℝ 2 (fun _ : ℝ => (0 : Space n)) from contDiff_const)
    (harnackDoublingDecay n ell L) 0
  have hSeed' : timeD univ (harnackBump (fun _ => 1) (fun t => 1+8*t)
      (fun _ : ℝ => (0 : Space n)) (harnackDoublingDecay n ell L) 0) p-
      harnackPucciMinus ell L (hessian (harnackBump (fun _ => 1) (fun t => 1+8*t)
        (fun _ : ℝ => (0 : Space n)) (harnackDoublingDecay n ell L) 0) p) ≤ 0 := by
    simpa only [mul_zero,add_zero,harnackDoublingDecay,deriv_const,zero_mul] using hSeed
  have hScaled := mul_le_mul_of_nonneg_left hSeed' hH
  unfold harnackDoublingPhi
  rw [harnack_timeD_const_mul hB.contDiffAt,harnack_hessian_const_mul hB.contDiffAt,
    harnack_minus_smul hell.le hL hH]
  nlinarith only [hScaled]

theorem harnack_reference_doubling {n : ℕ} {ell L H : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hH : 0 < H) {u : Point n → ℝ}
    (hu : ContinuousOn u (harnackClosed 0 3 0 1) ∧
      (∀ z∈harnackClosed 0 3 0 1, 0 ≤ u z) ∧
      viscositySuper (harnackOpen 0 3 0 1)
        (fun A _ => harnackPucciMinus ell L A) (fun _ => 0) u)
    (hBall : ∀ x∈Metric.closedBall (0 : Space n) 1, H ≤ u (x,0)) :
    ∀ x∈Metric.closedBall (0 : Space n) 2, harnackDoublingBeta n ell L*H ≤ u (x,1) := by
  have hBd : ∀ p∈harnackBoundary (0 : Space n) 3 0 1,
      harnackDoublingPhi n ell L H p ≤ u p := by
    intro p hp
    rcases hp with hp | hp
    · have ht : p.2=0 := hp.2
      by_cases hx : ‖p.1‖ ≤ 1
      · have hP : harnackPositiveCube (1-‖p.1‖^2) ≤ 1 := by
          have hQ : max (1-‖p.1‖^2) 0 ≤ 1 := max_le (by nlinarith [sq_nonneg ‖p.1‖]) (by norm_num)
          simpa only [harnackPositiveCube,one_pow] using pow_le_pow_left₀ (le_max_right _ _) hQ 3
        have hSeed : harnackDoublingPhi n ell L H p ≤ H := by
          change H*(1*Real.exp (-harnackDoublingDecay n ell L*(p.2+0))*
            harnackPositiveCube (1+8*p.2-‖p.1-0‖^2)) ≤ H
          simp only [ht,mul_zero,Real.exp_zero,one_mul,add_zero,sub_zero]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hP hH.le
        have hBall' := hBall p.1 (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
        simpa only [← ht,Prod.eta] using hSeed.trans hBall'
      · have hLevel : 1-‖p.1‖^2 ≤ 0 := by nlinarith [lt_of_not_ge hx,norm_nonneg p.1]
        have hZero : harnackDoublingPhi n ell L H p=0 := by
          simp only [harnackDoublingPhi,harnackBump,ht,mul_zero,add_zero,sub_zero,
            harnackPositiveCube,max_eq_right hLevel,zero_pow (by decide : 3≠0),mul_zero]
        rw [hZero]
        exact hu.2.1 p ⟨hp.1,by rw [ht]; norm_num⟩
    · have hTime : p.2∈Icc (0 : ℝ) 1 := by simpa only [zero_add] using hp.2
      have hx : ‖p.1‖=3 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.1
      have hLevel : 1+8*p.2-‖p.1‖^2 ≤ 0 := by rw [hx]; nlinarith [hTime.2]
      have hZero : harnackDoublingPhi n ell L H p=0 := by
        simp only [harnackDoublingPhi,harnackBump,sub_zero,harnackPositiveCube,max_eq_right hLevel,
          zero_pow (by decide : 3≠0),mul_zero]
      rw [hZero]
      exact hu.2.1 p ⟨Metric.sphere_subset_closedBall hp.1,hp.2⟩
  have hCompare := harnack_smooth_cylinder_comparison hell hL (0 : Space n)
    (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 1) hu.1
    (fun _ _ => (harnack_doublingPhi_contDiff n ell L H).contDiffAt) hu.2.2
    (fun p hp => harnack_doublingPhi_residual hell hL hH.le p (harnack_open_subset_closed hp)) hBd
  intro x hx
  have hx' : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hLevel : 5 ≤ max (1+8*(1 : ℝ)-‖x‖^2) 0 :=
    (by nlinarith [norm_nonneg x] : (5 : ℝ) ≤ 1+8*(1 : ℝ)-‖x‖^2).trans (le_max_left _ _)
  have hP : 1 ≤ harnackPositiveCube (1+8*(1 : ℝ)-‖x‖^2) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hLevel 3
    norm_num [harnackPositiveCube] at h ⊢
    linarith
  have hPhi : harnackDoublingBeta n ell L*H ≤ harnackDoublingPhi n ell L H (x,1) := by
    change Real.exp (-harnackDoublingDecay n ell L)*H ≤
      H*(1*Real.exp (-harnackDoublingDecay n ell L*(1+0))*harnackPositiveCube (1+8*1-‖x-0‖^2))
    simp only [add_zero,mul_one,one_mul,sub_zero]
    simp only [mul_one] at hP
    have hMul := mul_le_mul_of_nonneg_left hP
      (mul_pos hH (Real.exp_pos (-harnackDoublingDecay n ell L))).le
    nlinarith only [hMul]
  exact hPhi.trans (hCompare (x,1) ⟨Metric.closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 3) hx,
    by norm_num⟩)

end Yau.LeafProofs.L05Aux
