import Yau.LeafProofs.L05PucciHarnackBumpResidual
import Yau.LeafProofs.L05PucciHarnackCylinderLocalization
import Yau.LeafProofs.L05PucciHarnackSlabs

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackMovingCenter {n : ℕ} (c z : Space n) (t0 T : ℝ) (t : ℝ) : Space n :=
  c+((t-t0)/T) • (z-c)

theorem harnack_movingCenter_contDiff {n : ℕ} (c z : Space n) (t0 T : ℝ) :
    ContDiff ℝ 2 (harnackMovingCenter c z t0 T) :=
  contDiff_const.add (((contDiff_id.sub contDiff_const).div_const T).smul contDiff_const)

theorem harnack_movingCenter_hasDerivAt {n : ℕ} (c z : Space n) (t0 T t : ℝ) :
    HasDerivAt (harnackMovingCenter c z t0 T) (T⁻¹ • (z-c)) t := by
  convert! (((hasDerivAt_id t).sub_const t0).div_const T).smul_const (z-c) |>.const_add c using 1
  simp only [one_div]

theorem harnack_movingCenter_norm {n : ℕ} {c z : Space n} {t0 T t : ℝ}
    (hc : ‖c‖ ≤ 3/8) (hz : ‖z‖ ≤ 1/4) (hT : 0 < T) (ht : t∈Icc t0 (t0+T)) :
    ‖harnackMovingCenter c z t0 T t‖ ≤ 3/8 := by
  let q := (t-t0)/T
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr ht.1) hT.le
  have hq1 : q ≤ 1 := (div_le_one hT).mpr (by linarith [ht.2])
  have hEq : harnackMovingCenter c z t0 T t=(1-q) • c+q • z := by
    dsimp only [harnackMovingCenter,q]
    module
  rw [hEq]
  calc
    ‖(1-q) • c+q • z‖ ≤ ‖(1-q) • c‖+‖q • z‖ := norm_add_le _ _
    _ = (1-q)*‖c‖+q*‖z‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq0,abs_of_nonneg (sub_nonneg.mpr hq1)]
    _ ≤ (1-q)*(3/8)+q*(1/4) := add_le_add
      (mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hq1)) (mul_le_mul_of_nonneg_left hz hq0)
    _ ≤ 3/8 := by linarith

theorem harnack_movingCenter_speed {n : ℕ} {c z : Space n} {t0 T t : ℝ}
    (hc : ‖c‖ ≤ 3/8) (hz : ‖z‖ ≤ 1/4) (hT : 1/8 ≤ T) :
    ‖deriv (harnackMovingCenter c z t0 T) t‖ ≤ 8 := by
  have hTpos : 0 < T := by linarith
  rw [(harnack_movingCenter_hasDerivAt c z t0 T t).deriv,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hTpos)]
  have hNorm : ‖z-c‖ ≤ 5/8 := (norm_sub_le z c).trans (by linarith)
  have hMul := mul_le_mul_of_nonneg_left hNorm (inv_nonneg.mpr hTpos.le)
  calc
    T⁻¹*‖z-c‖ ≤ T⁻¹*(5/8) := hMul
    _ ≤ 8 := by rw [← div_eq_inv_mul,div_le_iff₀ hTpos]; linarith

def harnackMovingDecay (n : ℕ) (ell L : ℝ) : ℝ :=
  harnackBumpDecay ell ((1/128)^2) (2*L*(2*n)+2*(1/128)*8+8*ell)

def harnackPropagationC (n : ℕ) (ell L : ℝ) : ℝ := Real.exp (-harnackMovingDecay n ell L)

def harnackMovingPhi {n : ℕ} (ell L H : ℝ) (c z : Space n) (t0 T : ℝ) (p : Point n) : ℝ :=
  (H/((1/128)^2)^3)*harnackBump (fun _ => 1) (fun _ => (1/128)^2)
    (harnackMovingCenter c z t0 T) (harnackMovingDecay n ell L) (-t0) p

theorem harnack_movingPhi_contDiff {n : ℕ} (ell L H : ℝ) (c z : Space n) (t0 T : ℝ) :
    ContDiff ℝ 2 (harnackMovingPhi ell L H c z t0 T) :=
  contDiff_const.mul (harnack_bump_contDiff contDiff_const contDiff_const
    (harnack_movingCenter_contDiff c z t0 T) _ _)

theorem harnack_movingPhi_residual {n : ℕ} {ell L H : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hH : 0 ≤ H) {c z : Space n} {t0 T : ℝ}
    (hc : ‖c‖ ≤ 3/8) (hz : ‖z‖ ≤ 1/4) (hT : 1/8 ≤ T) (p : Point n) :
    timeD univ (harnackMovingPhi ell L H c z t0 T) p-
      harnackPucciMinus ell L (hessian (harnackMovingPhi ell L H c z t0 T) p) ≤ 0 := by
  have hCenter := harnack_movingCenter_contDiff c z t0 T
  have hB := harnack_bump_contDiff
    (show ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) from contDiff_const)
    (show ContDiff ℝ 2 (fun _ : ℝ => ((1 : ℝ)/128)^2) from contDiff_const)
    hCenter (harnackMovingDecay n ell L) (-t0)
  have hSeed : timeD univ (harnackBump (fun _ => 1) (fun _ => ((1 : ℝ)/128)^2)
      (harnackMovingCenter c z t0 T) (harnackMovingDecay n ell L) (-t0)) p-
      harnackPucciMinus ell L (hessian (harnackBump (fun _ => 1) (fun _ => ((1 : ℝ)/128)^2)
        (harnackMovingCenter c z t0 T) (harnackMovingDecay n ell L) (-t0)) p) ≤ 0 := by
    by_cases hq : ((1 : ℝ)/128)^2-‖p.1-harnackMovingCenter c z t0 T p.2‖^2 ≤ 0
    · have hZero := harnack_bump_jets_zero_of_level_nonpos
        (show ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) from contDiff_const)
        (show ContDiff ℝ 2 (fun _ : ℝ => ((1 : ℝ)/128)^2) from contDiff_const)
        hCenter (harnackMovingDecay n ell L) (-t0) p hq
      rw [hZero.2.1,hZero.2.2]
      simp only [harnackPucciMinus,neg_zero,pucciPlus_zero hell.le hL,sub_zero,le_refl]
    · have hY : ‖p.1-harnackMovingCenter c z t0 T p.2‖ ≤ 1/128 := by
        nlinarith [norm_nonneg (p.1-harnackMovingCenter c z t0 T p.2),lt_of_not_ge hq]
      have h := harnack_bump_residual hell hL
        (show ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) from contDiff_const)
        (show ContDiff ℝ 2 (fun _ : ℝ => ((1 : ℝ)/128)^2) from contDiff_const)
        hCenter (smin := (1/128)^2) (kappa := 0) (R := 1/128) (V := 8) (by norm_num)
        (-t0) p (by norm_num) le_rfl (by simp) hY (harnack_movingCenter_speed hc hz hT)
      simpa only [zero_add,harnackMovingDecay,deriv_const,zero_mul] using h
  have hAmp : 0 ≤ H/(((1 : ℝ)/128)^2)^3 := div_nonneg hH (by norm_num)
  have hScaled := mul_le_mul_of_nonneg_left hSeed hAmp
  unfold harnackMovingPhi
  rw [harnack_timeD_const_mul hB.contDiffAt,harnack_hessian_const_mul hB.contDiffAt,
    harnack_minus_smul hell.le hL hAmp]
  nlinarith only [hScaled]

theorem harnack_propagationC_pos (n : ℕ) (ell L : ℝ) :
    0 < harnackPropagationC n ell L := Real.exp_pos _

theorem harnack_positive_ball_moves {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {c : Space n} {t0 H : ℝ} (hc : ‖c‖ ≤ 3/8)
    (ht0 : t0∈Icc (-7/8 : ℝ) (-3/8)) (hH : 0 < H)
    (hBall : ∀ x∈Metric.closedBall c (1/128), H ≤ u (x,t0))
    {z : Point n} (hz : z∈harnackQplus n) :
    harnackPropagationC n ell L*H ≤ u z := by
  let T := z.2-t0
  have hT : 1/8 ≤ T := by dsimp only [T]; linarith [hz.2.1,ht0.2]
  have hTpos : 0 < T := by linarith
  have hT1 : T ≤ 1 := by dsimp only [T]; linarith [hz.2.2,ht0.1]
  have hEnd : t0+T=z.2 := by dsimp only [T]; ring
  have hzNorm : ‖z.1‖ ≤ 1/4 := by
    exact (show ‖z.1‖ < 1/4 from by simpa only [Metric.mem_ball,dist_zero_right] using hz.1).le
  let Phi := harnackMovingPhi ell L H c z.1 t0 T
  have hAmp : 0 < H/(((1 : ℝ)/128)^2)^3 := by positivity
  have hClosed : harnackClosed (0 : Space n) 1 t0 T ⊆ unitClosed n := by
    intro p hp
    exact ⟨hp.1,by linarith [hp.2.1,ht0.1],by linarith [hp.2.2,hz.2.2]⟩
  have hOpen : harnackOpen (0 : Space n) 1 t0 T ⊆ unitOpen n := by
    intro p hp
    exact ⟨hp.1,by linarith [hp.2.1,ht0.1],by linarith [hp.2.2,hz.2.2]⟩
  have hBd : ∀ p∈harnackBoundary (0 : Space n) 1 t0 T, Phi p ≤ u p := by
    intro p hp
    rcases hp with hp | hp
    · have ht : p.2=t0 := hp.2
      have hCenter : harnackMovingCenter c z.1 t0 T p.2=c := by
        simp only [harnackMovingCenter,ht,sub_self,zero_div,zero_smul,add_zero]
      by_cases hx : ‖p.1-c‖ ≤ 1/128
      · have hP : harnackPositiveCube (((1 : ℝ)/128)^2-‖p.1-c‖^2) ≤ (((1 : ℝ)/128)^2)^3 := by
          exact pow_le_pow_left₀ (le_max_right _ _)
            (max_le (by linarith [sq_nonneg ‖p.1-c‖]) (by norm_num)) _
        have hScaled := mul_le_mul_of_nonneg_left hP hAmp.le
        have hValue : Phi p ≤ H := by
          change H/(((1 : ℝ)/128)^2)^3*
            (1*Real.exp (-harnackMovingDecay n ell L*(p.2+(-t0)))*
              harnackPositiveCube (((1 : ℝ)/128)^2-‖p.1-harnackMovingCenter c z.1 t0 T p.2‖^2)) ≤ H
          rw [hCenter]
          simp only [ht,add_neg_cancel,mul_zero,Real.exp_zero,one_mul]
          norm_num at hScaled ⊢
          exact hScaled
        have hBall' := hBall p.1 (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
        simpa only [← ht,Prod.eta] using hValue.trans hBall'
      · have hLevel : ((1 : ℝ)/128)^2-‖p.1-c‖^2 ≤ 0 := by
          nlinarith [lt_of_not_ge hx,norm_nonneg (p.1-c)]
        have hZero : Phi p=0 := by
          change H/(((1 : ℝ)/128)^2)^3*
            (1*Real.exp (-harnackMovingDecay n ell L*(p.2+(-t0)))*
              harnackPositiveCube (((1 : ℝ)/128)^2-‖p.1-harnackMovingCenter c z.1 t0 T p.2‖^2))=0
          rw [hCenter]
          simp only [harnackPositiveCube,max_eq_right hLevel,zero_pow (by decide : 3≠0),mul_zero]
        rw [hZero]
        exact hu.2.1 p (hClosed ⟨hp.1,by rw [ht]; exact ⟨le_rfl,by linarith⟩⟩)
    · have hCenterNorm := harnack_movingCenter_norm hc hzNorm hTpos hp.2
      have hx : ‖p.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.1
      have hTriangle : ‖p.1‖ ≤ ‖p.1-harnackMovingCenter c z.1 t0 T p.2‖+
          ‖harnackMovingCenter c z.1 t0 T p.2‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          (p.1-harnackMovingCenter c z.1 t0 T p.2) (harnackMovingCenter c z.1 t0 T p.2)
      have hLevel : ((1 : ℝ)/128)^2-‖p.1-harnackMovingCenter c z.1 t0 T p.2‖^2 ≤ 0 := by
        nlinarith [norm_nonneg (p.1-harnackMovingCenter c z.1 t0 T p.2)]
      have hZero : Phi p=0 := by
        simp only [Phi,harnackMovingPhi,harnackBump,harnackPositiveCube,max_eq_right hLevel,
          zero_pow (by decide : 3≠0),mul_zero]
      rw [hZero]
      exact hu.2.1 p (hClosed ⟨Metric.sphere_subset_closedBall hp.1,hp.2⟩)
  have hCompare := harnack_smooth_cylinder_comparison hell hL (0 : Space n)
    (by norm_num : (0 : ℝ) < 1) hTpos (hu.1.mono hClosed)
    (fun _ _ => (harnack_movingPhi_contDiff ell L H c z.1 t0 T).contDiffAt)
    (fun p hp => hu.2.2 p (hOpen hp))
    (fun p _ => harnack_movingPhi_residual hell hL hH.le hc hzNorm hT p) hBd
  have hCyl : z∈harnackClosed (0 : Space n) 1 t0 T := by
    refine ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1) hz.1),?_,?_⟩
    · dsimp only [T] at hT
      linarith
    · exact hEnd.ge
  have hCenterEnd : harnackMovingCenter c z.1 t0 T z.2=z.1 := by
    simp only [harnackMovingCenter,show z.2-t0=T from rfl,div_self hTpos.ne',one_smul,add_sub_cancel]
  have hPhiEnd : Phi z=H*Real.exp (-harnackMovingDecay n ell L*T) := by
    change H/(((1 : ℝ)/128)^2)^3*
      (1*Real.exp (-harnackMovingDecay n ell L*(z.2+(-t0)))*
        harnackPositiveCube (((1 : ℝ)/128)^2-‖z.1-harnackMovingCenter c z.1 t0 T z.2‖^2))=_
    rw [hCenterEnd]
    simp only [sub_self,norm_zero,zero_pow (by decide : 2≠0),sub_zero,harnackPositiveCube,
      max_eq_left (by norm_num : (0 : ℝ) ≤ (1/128)^2),one_mul,← sub_eq_add_neg]
    change H/(((1 : ℝ)/128)^2)^3*
      (Real.exp (-harnackMovingDecay n ell L*T)*(((1 : ℝ)/128)^2)^3)=_
    ring
  have hDecay : 0 < harnackMovingDecay n ell L := harnack_bumpDecay_pos hell (by norm_num)
  have hExp : Real.exp (-harnackMovingDecay n ell L) ≤ Real.exp (-harnackMovingDecay n ell L*T) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hPoint := hCompare z hCyl
  change Phi z ≤ u z at hPoint
  rw [hPhiEnd] at hPoint
  change Real.exp (-harnackMovingDecay n ell L)*H ≤ u z
  have hScale := mul_le_mul_of_nonneg_left hExp hH.le
  exact (by simpa only [mul_comm] using hScale : Real.exp (-harnackMovingDecay n ell L)*H ≤
    H*Real.exp (-harnackMovingDecay n ell L*T)).trans hPoint

end Yau.LeafProofs.L05Aux


