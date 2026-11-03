import Yau.LeafProofs.L05PucciHarnackBumpResidual

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackExactRadiusSq (t : ℝ) : ℝ := 1/64+harnackPositiveCube (t+5/8)
def harnackExactCutoff (t : ℝ) : ℝ := harnackStep (16*(t+11/16))
def harnackExactGrowth (n : ℕ) (ell L : ℝ) : ℝ := 2+2*L*(2*n)+8*ell
def harnackExactDecay (n : ℕ) (ell L : ℝ) : ℝ :=
  harnackBumpDecay ell (1/64) (harnackExactGrowth n ell L)
def harnackExactAmplitude (n : ℕ) (ell L : ℝ) : ℝ :=
  2/(Real.exp (-harnackExactDecay n ell L)*(3/512)^3)
def harnackExactPhi (n : ℕ) (ell L : ℝ) (p : Point n) : ℝ :=
  harnackExactAmplitude n ell L*
    harnackBump harnackExactCutoff harnackExactRadiusSq (fun _ => 0) (harnackExactDecay n ell L) 1 p
def harnackExactSource (n : ℕ) (ell L : ℝ) (p : Point n) : ℝ :=
  harnackExactAmplitude n ell L*deriv harnackExactCutoff p.2*
    Real.exp (-harnackExactDecay n ell L*(p.2+1))*
      harnackPositiveCube (harnackExactRadiusSq p.2-‖p.1‖^2)
def harnackExactForcingSet (n : ℕ) : Set (Point n) :=
  Metric.closedBall 0 (1/8) ×ˢ Icc (-11/16) (-5/8)
def harnackExactM (n : ℕ) (ell L : ℝ) : ℝ := 1+harnackExactAmplitude n ell L
def harnackExactK (n : ℕ) (ell L : ℝ) : ℝ := 30*harnackExactAmplitude n ell L*(1/64)^3

theorem harnack_exactRadius_contDiff : ContDiff ℝ 2 harnackExactRadiusSq :=
  contDiff_const.add (harnack_positiveCube_contDiff.comp (contDiff_id.add contDiff_const))

theorem harnack_exactCutoff_contDiff : ContDiff ℝ 2 harnackExactCutoff :=
  harnack_step_contDiff.comp (contDiff_const.mul (contDiff_id.add contDiff_const))

theorem harnack_exactRadius_hasDerivAt (t : ℝ) :
    HasDerivAt harnackExactRadiusSq (3*(max (t+5/8) 0)^2) t := by
  convert! (hasDerivAt_const t (1/64 : ℝ)).add
    ((harnack_positiveCube_hasDerivAt (t+5/8)).comp t ((hasDerivAt_id t).add_const (5/8))) using 1
  simp only [zero_add,mul_one]

theorem harnack_exactCutoff_hasDerivAt (t : ℝ) :
    HasDerivAt harnackExactCutoff (16*deriv harnackStep (16*(t+11/16))) t := by
  convert! ((harnack_step_contDiff.differentiable (by norm_num) (16*(t+11/16))).hasDerivAt).comp t
    (((hasDerivAt_id t).add_const (11/16)).const_mul 16) using 1
  simp only [mul_one]
  ring

theorem harnack_exactCutoff_bounds (t : ℝ) :
    0 ≤ harnackExactCutoff t ∧ harnackExactCutoff t ≤ 1 := harnack_step_bounds _

theorem harnack_exactCutoff_deriv_bounds (t : ℝ) :
    0 ≤ deriv harnackExactCutoff t ∧ deriv harnackExactCutoff t ≤ 30 := by
  rw [(harnack_exactCutoff_hasDerivAt t).deriv]
  have h := harnack_step_deriv_bounds (16*(t+11/16))
  constructor <;> nlinarith [h.1,h.2]

theorem harnack_exactCutoff_deriv_zero_left {t : ℝ} (ht : t ≤ -11/16) :
    deriv harnackExactCutoff t=0 := by
  rw [(harnack_exactCutoff_hasDerivAt t).deriv,
    harnack_step_deriv_eq_zero_of_nonpos (by linarith : 16*(t+11/16) ≤ 0),mul_zero]

theorem harnack_exactCutoff_deriv_zero_right {t : ℝ} (ht : -5/8 ≤ t) :
    deriv harnackExactCutoff t=0 := by
  rw [(harnack_exactCutoff_hasDerivAt t).deriv,
    harnack_step_deriv_eq_zero_of_one_le (by linarith : 1 ≤ 16*(t+11/16)),mul_zero]

theorem harnack_exactRadius_eq_initial {t : ℝ} (ht : t ≤ -5/8) : harnackExactRadiusSq t=1/64 := by
  simp only [harnackExactRadiusSq,harnackPositiveCube,max_eq_right (by linarith : t+5/8 ≤ 0),
    zero_pow (by decide : 3≠0),add_zero]

theorem harnack_exactRadius_bounds {t : ℝ} (ht : t∈Icc (-1 : ℝ) 0) :
    1/64 ≤ harnackExactRadiusSq t ∧ harnackExactRadiusSq t ≤ 133/512 ∧
      0 ≤ deriv harnackExactRadiusSq t ∧ deriv harnackExactRadiusSq t ≤ 2 := by
  have h0 : 0 ≤ max (t+5/8) 0 := le_max_right _ _
  have h1 : max (t+5/8) 0 ≤ 5/8 := max_le (by linarith [ht.2]) (by norm_num)
  have h2 := pow_le_pow_left₀ h0 h1 2
  have h3 := pow_le_pow_left₀ h0 h1 3
  rw [(harnack_exactRadius_hasDerivAt t).deriv]
  dsimp only [harnackExactRadiusSq,harnackPositiveCube]
  norm_num at h2 h3
  refine ⟨?_,?_,by positivity,by linarith⟩
  · linarith [pow_nonneg h0 3]
  · linarith

theorem harnack_exactDecay_pos {n : ℕ} {ell L : ℝ} (hell : 0<ell) :
    0<harnackExactDecay n ell L := harnack_bumpDecay_pos hell (by norm_num)

theorem harnack_exactAmplitude_pos (n : ℕ) (ell L : ℝ) : 0<harnackExactAmplitude n ell L := by
  unfold harnackExactAmplitude
  positivity

theorem harnack_exactPhi_contDiff (n : ℕ) (ell L : ℝ) : ContDiff ℝ 2 (harnackExactPhi n ell L) :=
  contDiff_const.mul (harnack_bump_contDiff harnack_exactCutoff_contDiff harnack_exactRadius_contDiff
    contDiff_const (harnackExactDecay n ell L) 1)

theorem harnack_exactSource_continuous (n : ℕ) (ell L : ℝ) : Continuous (harnackExactSource n ell L) := by
  have hD : Continuous (deriv harnackExactCutoff) :=
    harnack_exactCutoff_contDiff.continuous_deriv (by norm_num)
  have hq : Continuous (fun z : Point n => harnackExactRadiusSq z.2-‖z.1‖^2) := by
    exact (harnack_exactRadius_contDiff.continuous.comp continuous_snd).sub
      (continuous_fst.norm.pow 2)
  exact ((continuous_const.mul (hD.comp continuous_snd)).mul (by fun_prop)).mul
    (harnack_positiveCube_contDiff.continuous.comp hq)

theorem harnack_exactPhi_residual {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell ≤ L)
    (p : Point n) (hp : p∈unitClosed n) :
    timeD univ (harnackExactPhi n ell L) p-
      harnackPucciMinus ell L (hessian (harnackExactPhi n ell L) p) ≤ harnackExactSource n ell L p := by
  have hS := harnack_exactRadius_bounds hp.2
  have hNorm : ‖p.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
  have hSeed := harnack_bump_residual hell hL harnack_exactCutoff_contDiff harnack_exactRadius_contDiff
    (show ContDiff ℝ 2 (fun _ : ℝ => (0 : Space n)) from contDiff_const)
    (smin := 1/64) (kappa := 2) (R := 1) (V := 0) (by norm_num) 1 p
    (harnack_exactCutoff_bounds p.2).1 hS.1 hS.2.2.2
    (by simpa only [sub_zero] using hNorm) (by simp)
  have hB : ContDiff ℝ 2 (harnackBump harnackExactCutoff harnackExactRadiusSq
      (fun _ : ℝ => (0 : Space n)) (harnackExactDecay n ell L) 1) :=
    harnack_bump_contDiff harnack_exactCutoff_contDiff harnack_exactRadius_contDiff contDiff_const _ _
  have hSeed' : timeD univ (harnackBump harnackExactCutoff harnackExactRadiusSq
      (fun _ : ℝ => (0 : Space n)) (harnackExactDecay n ell L) 1) p-
      harnackPucciMinus ell L (hessian (harnackBump harnackExactCutoff harnackExactRadiusSq
        (fun _ : ℝ => (0 : Space n)) (harnackExactDecay n ell L) 1) p) ≤ 
      deriv harnackExactCutoff p.2*Real.exp (-harnackExactDecay n ell L*(p.2+1))*
        harnackPositiveCube (harnackExactRadiusSq p.2-‖p.1‖^2) := by
    simpa only [mul_zero,add_zero,harnackExactDecay,harnackExactGrowth,sub_zero] using hSeed
  have hScaled := mul_le_mul_of_nonneg_left hSeed' (harnack_exactAmplitude_pos n ell L).le
  unfold harnackExactPhi
  rw [harnack_timeD_const_mul hB.contDiffAt,harnack_hessian_const_mul hB.contDiffAt,
    harnack_minus_smul hell.le hL (harnack_exactAmplitude_pos n ell L).le]
  dsimp only [harnackExactSource]
  nlinarith only [hScaled]

theorem harnack_exactForcingSet_measurable (n : ℕ) : MeasurableSet (harnackExactForcingSet n) :=
  Metric.isClosed_closedBall.measurableSet.prod measurableSet_Icc

theorem harnack_qminus_subset_unitClosed {n : ℕ} : harnackQminus n ⊆ unitClosed n := by
  intro p hp
  refine ⟨Metric.closedBall_subset_closedBall (by norm_num : (1/4 : ℝ) ≤ 1)
    (Metric.ball_subset_closedBall hp.1),?_,?_⟩ <;> linarith [hp.2.1,hp.2.2]

theorem harnack_qplus_subset_unitClosed {n : ℕ} : harnackQplus n ⊆ unitClosed n := by
  intro p hp
  refine ⟨Metric.closedBall_subset_closedBall (by norm_num : (1/4 : ℝ) ≤ 1)
    (Metric.ball_subset_closedBall hp.1),?_,?_⟩ <;> linarith [hp.2.1,hp.2.2]

theorem harnack_exactForcingSet_subset_qminus {n : ℕ} : harnackExactForcingSet n ⊆ harnackQminus n := by
  intro p hp
  refine ⟨Metric.closedBall_subset_ball (by norm_num : (1/8 : ℝ) < 1/4) hp.1,?_,?_⟩ <;>
    linarith [hp.2.1,hp.2.2]

theorem harnack_exactForcingSet_subset_unitOpen {n : ℕ} : harnackExactForcingSet n ⊆ unitOpen n := by
  intro p hp
  have hq := harnack_exactForcingSet_subset_qminus hp
  refine ⟨Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1) hq.1,?_,?_⟩ <;>
    linarith [hq.2.1,hq.2.2]

theorem harnack_exactSource_zero {n : ℕ} (ell L : ℝ) (p : Point n)
    (hp : p ∉ harnackExactForcingSet n) : harnackExactSource n ell L p=0 := by
  by_cases ht0 : p.2 ≤ -11/16
  · simp only [harnackExactSource,harnack_exactCutoff_deriv_zero_left ht0,mul_zero,zero_mul]
  by_cases ht1 : -5/8 ≤ p.2
  · simp only [harnackExactSource,harnack_exactCutoff_deriv_zero_right ht1,mul_zero,zero_mul]
  have ht : p.2 ∈ Icc (-11/16 : ℝ) (-5/8) := ⟨(not_le.mp ht0).le,(not_le.mp ht1).le⟩
  have hNorm : 1/8 < ‖p.1‖ := by
    by_contra hn
    apply hp
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using not_lt.mp hn,ht⟩
  have hLevel : harnackExactRadiusSq p.2-‖p.1‖^2 ≤ 0 := by
    rw [harnack_exactRadius_eq_initial ht.2]
    nlinarith [norm_nonneg p.1]
  simp only [harnackExactSource,harnackPositiveCube,max_eq_right hLevel,
    zero_pow (by decide : 3≠0),mul_zero]

theorem harnack_exactK_pos (n : ℕ) (ell L : ℝ) : 0 < harnackExactK n ell L := by
  have ha := harnack_exactAmplitude_pos n ell L
  dsimp only [harnackExactK]
  positivity

theorem harnack_exactM_gt_one (n : ℕ) (ell L : ℝ) : 1 < harnackExactM n ell L := by
  have ha := harnack_exactAmplitude_pos n ell L
  dsimp only [harnackExactM]
  linarith

theorem harnack_exactSource_bounds {n : ℕ} {ell L : ℝ} (hell : 0 < ell) (p : Point n) :
    0 ≤ harnackExactSource n ell L p ∧ harnackExactSource n ell L p ≤ harnackExactK n ell L := by
  have ha := harnack_exactAmplitude_pos n ell L
  have hd := harnack_exactCutoff_deriv_bounds p.2
  have hExp0 : 0 ≤ Real.exp (-harnackExactDecay n ell L*(p.2+1)) := (Real.exp_pos _).le
  have hP0 : 0 ≤ harnackPositiveCube (harnackExactRadiusSq p.2-‖p.1‖^2) :=
    pow_nonneg (le_max_right _ _) _
  refine ⟨?_,?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg ha.le hd.1) hExp0) hP0
  by_cases hd0 : deriv harnackExactCutoff p.2=0
  · simp only [harnackExactSource,hd0,mul_zero,zero_mul]
    exact (harnack_exactK_pos n ell L).le
  have ht0 : -11/16 < p.2 := by
    by_contra ht
    exact hd0 (harnack_exactCutoff_deriv_zero_left (not_lt.mp ht))
  have ht1 : p.2 < -5/8 := by
    by_contra ht
    exact hd0 (harnack_exactCutoff_deriv_zero_right (not_lt.mp ht))
  have hDecay := harnack_exactDecay_pos (n := n) (L := L) hell
  have hExp : Real.exp (-harnackExactDecay n ell L*(p.2+1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hLevel : max (harnackExactRadiusSq p.2-‖p.1‖^2) 0 ≤ 1/64 := by
    rw [harnack_exactRadius_eq_initial ht1.le]
    apply max_le _ (by norm_num)
    nlinarith [sq_nonneg ‖p.1‖]
  have hP : harnackPositiveCube (harnackExactRadiusSq p.2-‖p.1‖^2) ≤ (1/64 : ℝ)^3 :=
    pow_le_pow_left₀ (le_max_right _ _) hLevel _
  calc
    _ ≤ harnackExactAmplitude n ell L*30*1*(1/64 : ℝ)^3 := by
      dsimp only [harnackExactSource]
      gcongr
      exact hd.2
    _ = _ := by dsimp only [harnackExactK]; ring

theorem harnack_exactPhi_bound {n : ℕ} {ell L : ℝ} (hell : 0 < ell)
    (p : Point n) (hp : p ∈ unitClosed n) : harnackExactPhi n ell L p ≤ harnackExactM n ell L := by
  have ha := harnack_exactAmplitude_pos n ell L
  have hchi := harnack_exactCutoff_bounds p.2
  have hS := harnack_exactRadius_bounds hp.2
  have hDecay := harnack_exactDecay_pos (n := n) (L := L) hell
  have hExp0 : 0 ≤ Real.exp (-harnackExactDecay n ell L*(p.2+1)) := (Real.exp_pos _).le
  have hExp : Real.exp (-harnackExactDecay n ell L*(p.2+1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hp.2.1])
  have hLevel : max (harnackExactRadiusSq p.2-‖p.1‖^2) 0 ≤ 1 :=
    max_le (by nlinarith [sq_nonneg ‖p.1‖]) (by norm_num)
  have hP0 : 0 ≤ harnackPositiveCube (harnackExactRadiusSq p.2-‖p.1‖^2) :=
    pow_nonneg (le_max_right _ _) _
  have hP : harnackPositiveCube (harnackExactRadiusSq p.2-‖p.1‖^2) ≤ 1 := by
    simpa only [harnackPositiveCube,one_pow] using pow_le_pow_left₀ (le_max_right _ _) hLevel 3
  have hSeed : harnackBump harnackExactCutoff harnackExactRadiusSq (fun _ => (0 : Space n))
      (harnackExactDecay n ell L) 1 p ≤ 1 := by
    dsimp only [harnackBump]
    simp only [sub_zero]
    have hFirst : harnackExactCutoff p.2*Real.exp (-harnackExactDecay n ell L*(p.2+1)) ≤ 1*1 :=
      mul_le_mul hchi.2 hExp hExp0 (by norm_num)
    have hLast := mul_le_mul hFirst hP hP0 (by norm_num : (0 : ℝ) ≤ 1*1)
    simpa only [one_mul] using hLast
  change harnackExactAmplitude n ell L*(_ : ℝ) ≤ 1+harnackExactAmplitude n ell L
  have hScaled := mul_le_mul_of_nonneg_left hSeed ha.le
  linarith

theorem harnack_exactPhi_boundary {n : ℕ} (ell L : ℝ) (p : Point n)
    (hp : p ∈ parabolicBoundary n) : harnackExactPhi n ell L p=0 := by
  rcases hp with hp | hp
  · have ht : p.2=(-1 : ℝ) := hp.2
    have hChi : harnackExactCutoff (-1)=0 := harnack_step_eq_zero (by norm_num)
    simp only [harnackExactPhi,harnackBump,ht,hChi,zero_mul,mul_zero]
  · have hS := harnack_exactRadius_bounds hp.2
    have hx : ‖p.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.1
    have hLevel : harnackExactRadiusSq p.2-‖p.1‖^2 ≤ 0 := by rw [hx]; nlinarith
    simp only [harnackExactPhi,harnackBump,sub_zero,harnackPositiveCube,max_eq_right hLevel,
      zero_pow (by decide : 3≠0),mul_zero]

theorem harnack_exactPhi_later {n : ℕ} {ell L : ℝ} (hell : 0 < ell)
    (p : Point n) (hp : p ∈ harnackQplus n) : 2 ≤ harnackExactPhi n ell L p := by
  have hDecay := harnack_exactDecay_pos (n := n) (L := L) hell
  have ha := harnack_exactAmplitude_pos n ell L
  have hchi : harnackExactCutoff p.2=1 :=
    harnack_step_eq_one (by linarith [hp.2.1])
  have hR : 3/8 ≤ max (p.2+5/8) 0 := (by linarith [hp.2.1] : (3/8 : ℝ) ≤ p.2+5/8).trans (le_max_left _ _)
  have hPow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3/8) hR 3
  have hS : 35/512 ≤ harnackExactRadiusSq p.2 := by
    dsimp only [harnackExactRadiusSq,harnackPositiveCube]
    nlinarith only [hPow]
  have hNorm : ‖p.1‖ < 1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
  have hQ : 3/512 ≤ harnackExactRadiusSq p.2-‖p.1‖^2 := by
    nlinarith [norm_nonneg p.1]
  have hP : (3/512 : ℝ)^3 ≤ harnackPositiveCube (harnackExactRadiusSq p.2-‖p.1‖^2) :=
    pow_le_pow_left₀ (by norm_num) (hQ.trans (le_max_left _ _)) 3
  have hExp : Real.exp (-harnackExactDecay n ell L) ≤
      Real.exp (-harnackExactDecay n ell L*(p.2+1)) := Real.exp_le_exp.mpr (by nlinarith [hp.2.2])
  have hSeed : Real.exp (-harnackExactDecay n ell L)*(3/512 : ℝ)^3 ≤
      harnackBump harnackExactCutoff harnackExactRadiusSq (fun _ => (0 : Space n))
        (harnackExactDecay n ell L) 1 p := by
    dsimp only [harnackBump]
    rw [hchi]
    simp only [one_mul,sub_zero]
    exact mul_le_mul hExp hP (by positivity) (Real.exp_pos _).le
  have hScaled := mul_le_mul_of_nonneg_left hSeed ha.le
  have hEq : harnackExactAmplitude n ell L*
      (Real.exp (-harnackExactDecay n ell L)*(3/512 : ℝ)^3)=2 := by
    dsimp only [harnackExactAmplitude]
    field_simp
  rw [hEq] at hScaled
  exact hScaled

end Yau.LeafProofs.L05Aux
