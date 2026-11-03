import Yau.LeafProofs.L05PucciHarnackBumpResidual
import Yau.LeafProofs.L05PucciHarnackCylinderLocalization

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackBallDecay (n : ℕ) (ell L R : ℝ) : ℝ :=
  harnackBumpDecay ell (R^2) (2*L*(2*n)+8*ell)

def harnackBallPhi (n : ℕ) (ell L R H : ℝ) (p : Point n) : ℝ :=
  (H/(R^2)^3)*harnackBump (fun _ => 1) (fun _ => R^2) (fun _ => 0)
    (harnackBallDecay n ell L R) 0 p

theorem harnack_ballPhi_contDiff (n : ℕ) (ell L R H : ℝ) :
    ContDiff ℝ 2 (harnackBallPhi n ell L R H) :=
  contDiff_const.mul (harnack_bump_contDiff contDiff_const contDiff_const contDiff_const _ _)

theorem harnack_ballPhi_residual {n : ℕ} {ell L R H : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hR : 0 < R) (hH : 0 ≤ H)
    (p : Point n) (hp : p.1∈Metric.closedBall (0 : Space n) R) :
    timeD univ (harnackBallPhi n ell L R H) p-
      harnackPucciMinus ell L (hessian (harnackBallPhi n ell L R H) p) ≤ 0 := by
  have hNorm : ‖p.1‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp
  have hSeed := harnack_bump_residual hell hL
    (show ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) from contDiff_const)
    (show ContDiff ℝ 2 (fun _ : ℝ => R^2) from contDiff_const)
    (show ContDiff ℝ 2 (fun _ : ℝ => (0 : Space n)) from contDiff_const)
    (smin := R^2) (kappa := 0) (R := R) (V := 0) (sq_pos_of_ne_zero hR.ne') 0 p
    (by norm_num) le_rfl (by simp) (by simpa only [sub_zero] using hNorm) (by simp)
  have hB := harnack_bump_contDiff
    (show ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) from contDiff_const)
    (show ContDiff ℝ 2 (fun _ : ℝ => R^2) from contDiff_const)
    (show ContDiff ℝ 2 (fun _ : ℝ => (0 : Space n)) from contDiff_const)
    (harnackBallDecay n ell L R) 0
  have hSeed' : timeD univ (harnackBump (fun _ => 1) (fun _ => R^2)
      (fun _ : ℝ => (0 : Space n)) (harnackBallDecay n ell L R) 0) p-
      harnackPucciMinus ell L (hessian (harnackBump (fun _ => 1) (fun _ => R^2)
        (fun _ : ℝ => (0 : Space n)) (harnackBallDecay n ell L R) 0) p) ≤ 0 := by
    simpa only [mul_zero,add_zero,zero_add,harnackBallDecay,deriv_const,zero_mul] using hSeed
  have hScaled := mul_le_mul_of_nonneg_left hSeed' (div_nonneg hH (pow_nonneg (sq_nonneg R) 3))
  unfold harnackBallPhi
  rw [harnack_timeD_const_mul hB.contDiffAt,harnack_hessian_const_mul hB.contDiffAt,
    harnack_minus_smul hell.le hL (div_nonneg hH (pow_nonneg (sq_nonneg R) 3))]
  nlinarith only [hScaled]

theorem harnack_reference_ball_persistence {n : ℕ} {ell L R T H : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hR : 0 < R) (hT : 0 < T) (hH : 0 < H)
    {u : Point n → ℝ}
    (hu : ContinuousOn u (harnackClosed 0 R 0 T) ∧
      (∀ z∈harnackClosed 0 R 0 T, 0 ≤ u z) ∧
      viscositySuper (harnackOpen 0 R 0 T)
        (fun A _ => harnackPucciMinus ell L A) (fun _ => 0) u)
    (hBall : ∀ x∈Metric.closedBall (0 : Space n) R, H ≤ u (x,0)) :
    ∀ x∈Metric.closedBall (0 : Space n) (3*R/4), ∀ t∈Icc (0 : ℝ) T,
      (7/16 : ℝ)^3*Real.exp (-harnackBallDecay n ell L R*T)*H ≤ u (x,t) := by
  have hAmp : 0 < H/(R^2)^3 := div_pos hH (pow_pos (sq_pos_of_ne_zero hR.ne') _)
  have hInitBound (x : Space n) : (H/(R^2)^3)*harnackPositiveCube (R^2-‖x‖^2) ≤ H := by
    have hLevel : max (R^2-‖x‖^2) 0 ≤ R^2 :=
      max_le (by linarith [sq_nonneg ‖x‖]) (sq_nonneg R)
    have hP := pow_le_pow_left₀ (le_max_right _ _) hLevel 3
    have hScaled := mul_le_mul_of_nonneg_left hP hAmp.le
    have hEq : (H/(R^2)^3)*(R^2)^3=H := div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hR.ne'))
    rw [hEq] at hScaled
    exact hScaled
  have hBd : ∀ p∈harnackBoundary (0 : Space n) R 0 T, harnackBallPhi n ell L R H p ≤ u p := by
    intro p hp
    rcases hp with hp | hp
    · have ht : p.2=0 := hp.2
      have hBound : harnackBallPhi n ell L R H p ≤ H := by
        simpa only [harnackBallPhi,harnackBump,ht,mul_zero,add_zero,Real.exp_zero,
          one_mul,sub_zero] using hInitBound p.1
      have hBall' := hBall p.1 hp.1
      simpa only [← ht,Prod.eta] using hBound.trans hBall'
    · have hx : ‖p.1‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.1
      have hZero : harnackBallPhi n ell L R H p=0 := by
        simp only [harnackBallPhi,harnackBump,sub_zero,hx,sub_self,harnackPositiveCube,max_self,
          zero_pow (by decide : 3≠0),mul_zero]
      rw [hZero]
      exact hu.2.1 p ⟨Metric.sphere_subset_closedBall hp.1,hp.2⟩
  have hCompare := harnack_smooth_cylinder_comparison hell hL (0 : Space n) hR hT hu.1
    (fun _ _ => (harnack_ballPhi_contDiff n ell L R H).contDiffAt) hu.2.2
    (fun p hp => harnack_ballPhi_residual hell hL hR hH.le p (Metric.ball_subset_closedBall hp.1)) hBd
  intro x hx t ht
  have hxNorm : ‖x‖ ≤ 3*R/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hLevel : (7/16 : ℝ)*R^2 ≤ max (R^2-‖x‖^2) 0 := by
    apply le_trans _ (le_max_left _ _)
    nlinarith [norm_nonneg x]
  have hP : ((7/16 : ℝ)*R^2)^3 ≤ harnackPositiveCube (R^2-‖x‖^2) :=
    pow_le_pow_left₀ (by positivity) hLevel 3
  have hDecay : 0 < harnackBallDecay n ell L R := harnack_bumpDecay_pos hell (sq_pos_of_ne_zero hR.ne')
  have hExp : Real.exp (-harnackBallDecay n ell L R*T) ≤ Real.exp (-harnackBallDecay n ell L R*t) :=
    Real.exp_le_exp.mpr (by nlinarith [ht.2])
  have hProd := mul_le_mul hExp hP (by positivity) (Real.exp_pos _).le
  have hScaled := mul_le_mul_of_nonneg_left hProd hAmp.le
  have hPhi : (7/16 : ℝ)^3*Real.exp (-harnackBallDecay n ell L R*T)*H ≤
      harnackBallPhi n ell L R H (x,t) := by
    have hEq : (H/(R^2)^3)*(Real.exp (-harnackBallDecay n ell L R*T)*((7/16 : ℝ)*R^2)^3)=
        (7/16 : ℝ)^3*Real.exp (-harnackBallDecay n ell L R*T)*H := by
      field_simp [hR.ne']
    rw [hEq] at hScaled
    simpa only [harnackBallPhi,harnackBump,one_mul,add_zero,sub_zero] using hScaled
  exact hPhi.trans (hCompare (x,t) ⟨Metric.closedBall_subset_closedBall (by linarith : 3*R/4 ≤ R) hx,
    by simpa only [zero_add] using ht⟩)

end Yau.LeafProofs.L05Aux
