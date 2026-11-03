import Yau.LeafProofs.L05PucciHarnackBumpResidual
import Yau.LeafProofs.L05PucciHarnackCylinderLocalization

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackLocalKappa (n : ℕ) : ℝ := 16*((2*n : ℕ)+1)
def harnackLocalEpsilon (n : ℕ) : ℝ := 1/(256*harnackLocalKappa n)
def harnackLocalRadiusSq (n : ℕ) (t : ℝ) : ℝ := 1/64+harnackLocalKappa n*t
def harnackLocalCutoff (n : ℕ) (t : ℝ) : ℝ :=
  harnackStep ((t-harnackLocalEpsilon n)/harnackLocalEpsilon n)
def harnackLocalGrowth (n : ℕ) (ell L : ℝ) : ℝ := harnackLocalKappa n+2*L*(2*n)+8*ell
def harnackLocalDecay (n : ℕ) (ell L : ℝ) : ℝ :=
  harnackBumpDecay ell (1/64) (harnackLocalGrowth n ell L)
def harnackLocalGap (n : ℕ) : ℝ := 1/64+harnackLocalKappa n-4*(2*n)
def harnackLocalAmplitude (n : ℕ) (ell L : ℝ) : ℝ :=
  2*Real.exp (2*harnackLocalDecay n ell L)/(harnackLocalGap n)^3
def harnackLocalRadius (n : ℕ) : ℝ := Real.sqrt (1+1/64+2*harnackLocalKappa n)
def harnackLocalPhi (n : ℕ) (ell L : ℝ) (z : Point n) : ℝ :=
  harnackLocalAmplitude n ell L*harnackBump (harnackLocalCutoff n)
    (harnackLocalRadiusSq n) (fun _ => 0) (harnackLocalDecay n ell L) 0 z
def harnackLocalSource (n : ℕ) (ell L : ℝ) (z : Point n) : ℝ :=
  harnackLocalAmplitude n ell L*deriv (harnackLocalCutoff n) z.2*
    Real.exp (-harnackLocalDecay n ell L*z.2)*
      harnackPositiveCube (harnackLocalRadiusSq n z.2-‖z.1‖^2)
def harnackLocalForcingSet (n : ℕ) : Set (Point n) :=
  Metric.closedBall 0 (Real.sqrt (3/128)) ×ˢ
    Icc (harnackLocalEpsilon n) (2*harnackLocalEpsilon n)
def harnackLocalM (n : ℕ) (ell L : ℝ) : ℝ :=
  2+harnackLocalAmplitude n ell L*(1/64+2*harnackLocalKappa n)^3
def harnackLocalK (n : ℕ) (ell L : ℝ) : ℝ :=
  harnackLocalAmplitude n ell L*(15/(8*harnackLocalEpsilon n))*(3/128)^3

theorem harnack_localKappa_pos (n : ℕ) : 0 < harnackLocalKappa n := by
  unfold harnackLocalKappa
  positivity

theorem harnack_localEpsilon_pos (n : ℕ) : 0 < harnackLocalEpsilon n := by
  unfold harnackLocalEpsilon
  exact one_div_pos.mpr (mul_pos (by norm_num) (harnack_localKappa_pos n))

theorem harnack_localEpsilon_small (n : ℕ) : harnackLocalEpsilon n ≤ 1/4096 := by
  have hk : 16 ≤ harnackLocalKappa n := by
    unfold harnackLocalKappa
    have hn := Nat.cast_nonneg (2*n) (α := ℝ)
    linarith
  apply (div_le_iff₀ (by positivity : 0 < 256*harnackLocalKappa n)).mpr
  nlinarith

theorem harnack_localGap_pos (n : ℕ) : 0 < harnackLocalGap n := by
  unfold harnackLocalGap harnackLocalKappa
  have hn := Nat.cast_nonneg n (α := ℝ)
  push_cast
  linarith

theorem harnack_localRadius_pos (n : ℕ) : 0 < harnackLocalRadius n := by
  apply Real.sqrt_pos.mpr
  linarith [harnack_localKappa_pos n]

theorem harnack_localRadius_sq (n : ℕ) :
    (harnackLocalRadius n)^2=1+1/64+2*harnackLocalKappa n := by
  exact Real.sq_sqrt (by linarith [harnack_localKappa_pos n])

theorem harnack_localRadius_contDiff (n : ℕ) : ContDiff ℝ 2 (harnackLocalRadiusSq n) :=
  contDiff_const.add (contDiff_const.mul contDiff_id)

theorem harnack_localCutoff_contDiff (n : ℕ) : ContDiff ℝ 2 (harnackLocalCutoff n) :=
  harnack_step_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem harnack_localRadius_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (harnackLocalRadiusSq n) (harnackLocalKappa n) t := by
  convert! (hasDerivAt_const t (1/64 : ℝ)).add ((hasDerivAt_id t).const_mul (harnackLocalKappa n)) using 1
  simp

theorem harnack_localCutoff_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (harnackLocalCutoff n)
      (deriv harnackStep ((t-harnackLocalEpsilon n)/harnackLocalEpsilon n)/harnackLocalEpsilon n) t := by
  convert! ((harnack_step_contDiff.differentiable (by norm_num)
    ((t-harnackLocalEpsilon n)/harnackLocalEpsilon n)).hasDerivAt).comp t
      (((hasDerivAt_id t).sub_const (harnackLocalEpsilon n)).div_const (harnackLocalEpsilon n)) using 1
  ring

theorem harnack_localCutoff_bounds (n : ℕ) (t : ℝ) :
    0 ≤ harnackLocalCutoff n t ∧ harnackLocalCutoff n t ≤ 1 := harnack_step_bounds _

theorem harnack_localCutoff_deriv_bounds (n : ℕ) (t : ℝ) :
    0 ≤ deriv (harnackLocalCutoff n) t ∧
      deriv (harnackLocalCutoff n) t ≤ 15/(8*harnackLocalEpsilon n) := by
  rw [(harnack_localCutoff_hasDerivAt n t).deriv]
  have h := harnack_step_deriv_bounds ((t-harnackLocalEpsilon n)/harnackLocalEpsilon n)
  refine ⟨div_nonneg h.1 (harnack_localEpsilon_pos n).le,?_⟩
  convert! div_le_div_of_nonneg_right h.2 (harnack_localEpsilon_pos n).le using 1
  ring

theorem harnack_localDecay_pos {n : ℕ} {ell L : ℝ} (hell : 0 < ell) :
    0 < harnackLocalDecay n ell L := harnack_bumpDecay_pos hell (by norm_num)

theorem harnack_localAmplitude_pos (n : ℕ) (ell L : ℝ) :
    0 < harnackLocalAmplitude n ell L :=
  div_pos (mul_pos (by norm_num) (Real.exp_pos _)) (pow_pos (harnack_localGap_pos n) _)

theorem harnack_localPhi_contDiff (n : ℕ) (ell L : ℝ) :
    ContDiff ℝ 2 (harnackLocalPhi n ell L) :=
  contDiff_const.mul (harnack_bump_contDiff (harnack_localCutoff_contDiff n)
    (harnack_localRadius_contDiff n) contDiff_const _ _)

theorem harnack_localSource_continuous (n : ℕ) (ell L : ℝ) :
    Continuous (harnackLocalSource n ell L) := by
  have hD := (harnack_localCutoff_contDiff n).continuous_deriv (by norm_num)
  have hq : Continuous (fun z : Point n => harnackLocalRadiusSq n z.2-‖z.1‖^2) :=
    ((harnack_localRadius_contDiff n).continuous.comp continuous_snd).sub (continuous_fst.norm.pow 2)
  exact ((continuous_const.mul (hD.comp continuous_snd)).mul (by fun_prop)).mul
    (harnack_positiveCube_contDiff.continuous.comp hq)

theorem harnack_localCutoff_deriv_zero_left (n : ℕ) {t : ℝ}
    (ht : t ≤ harnackLocalEpsilon n) : deriv (harnackLocalCutoff n) t=0 := by
  rw [(harnack_localCutoff_hasDerivAt n t).deriv,
    harnack_step_deriv_eq_zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (harnack_localEpsilon_pos n).le),zero_div]

theorem harnack_localCutoff_deriv_zero_right (n : ℕ) {t : ℝ}
    (ht : 2*harnackLocalEpsilon n ≤ t) : deriv (harnackLocalCutoff n) t=0 := by
  rw [(harnack_localCutoff_hasDerivAt n t).deriv,
    harnack_step_deriv_eq_zero_of_one_le
      ((le_div_iff₀ (harnack_localEpsilon_pos n)).mpr (by linarith)),zero_div]

theorem harnack_local_radius_time_bounds (n : ℕ) {t : ℝ} (ht : t∈Icc (0 : ℝ) 2) :
    1/64 ≤ harnackLocalRadiusSq n t ∧
      harnackLocalRadiusSq n t ≤ 1/64+2*harnackLocalKappa n := by
  have hLo := mul_nonneg (harnack_localKappa_pos n).le ht.1
  have hHi := mul_le_mul_of_nonneg_left ht.2 (harnack_localKappa_pos n).le
  dsimp only [harnackLocalRadiusSq]
  constructor <;> linarith

theorem harnack_local_radius_transition (n : ℕ) {t : ℝ}
    (ht : t ≤ 2*harnackLocalEpsilon n) : harnackLocalRadiusSq n t ≤ 3/128 := by
  have hk := harnack_localKappa_pos n
  have h := mul_le_mul_of_nonneg_left ht hk.le
  have hEq : harnackLocalKappa n*(2*harnackLocalEpsilon n)=1/128 := by
    unfold harnackLocalEpsilon
    field_simp [hk.ne']
    norm_num
  rw [hEq] at h
  dsimp only [harnackLocalRadiusSq]
  linarith

theorem harnack_localPhi_residual {n : ℕ} {ell L : ℝ} (hell : 0 < ell) (hL : ell ≤ L)
    (p : Point n) (hp : p∈harnackClosed 0 (harnackLocalRadius n) 0 2) :
    timeD univ (harnackLocalPhi n ell L) p-
      harnackPucciMinus ell L (hessian (harnackLocalPhi n ell L) p) ≤
        harnackLocalSource n ell L p := by
  have hTime : p.2∈Icc (0 : ℝ) 2 := by simpa only [zero_add] using hp.2
  have hNorm : ‖p.1‖ ≤ harnackLocalRadius n := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
  have hSeed := harnack_bump_residual hell hL (harnack_localCutoff_contDiff n)
    (harnack_localRadius_contDiff n)
    (show ContDiff ℝ 2 (fun _ : ℝ => (0 : Space n)) from contDiff_const)
    (smin := 1/64) (kappa := harnackLocalKappa n) (R := harnackLocalRadius n)
    (V := 0) (by norm_num) 0 p (harnack_localCutoff_bounds n p.2).1
    (harnack_local_radius_time_bounds n hTime).1
    (by rw [(harnack_localRadius_hasDerivAt n p.2).deriv])
    (by simpa only [sub_zero] using hNorm) (by simp)
  have hB := harnack_bump_contDiff (harnack_localCutoff_contDiff n)
    (harnack_localRadius_contDiff n)
    (show ContDiff ℝ 2 (fun _ : ℝ => (0 : Space n)) from contDiff_const)
    (harnackLocalDecay n ell L) 0
  have hSeed' : timeD univ (harnackBump (harnackLocalCutoff n) (harnackLocalRadiusSq n)
      (fun _ : ℝ => (0 : Space n)) (harnackLocalDecay n ell L) 0) p-
      harnackPucciMinus ell L (hessian (harnackBump (harnackLocalCutoff n) (harnackLocalRadiusSq n)
        (fun _ : ℝ => (0 : Space n)) (harnackLocalDecay n ell L) 0) p) ≤
      deriv (harnackLocalCutoff n) p.2*Real.exp (-harnackLocalDecay n ell L*p.2)*
        harnackPositiveCube (harnackLocalRadiusSq n p.2-‖p.1‖^2) := by
    simpa only [mul_zero,add_zero,harnackLocalDecay,harnackLocalGrowth,sub_zero] using hSeed
  have hScaled := mul_le_mul_of_nonneg_left hSeed' (harnack_localAmplitude_pos n ell L).le
  unfold harnackLocalPhi
  rw [harnack_timeD_const_mul hB.contDiffAt,harnack_hessian_const_mul hB.contDiffAt,
    harnack_minus_smul hell.le hL (harnack_localAmplitude_pos n ell L).le]
  dsimp only [harnackLocalSource]
  nlinarith only [hScaled]

theorem harnack_localForcingSet_measurable (n : ℕ) :
    MeasurableSet (harnackLocalForcingSet n) :=
  Metric.isClosed_closedBall.measurableSet.prod measurableSet_Icc

theorem harnack_localSource_zero (n : ℕ) (ell L : ℝ) (p : Point n)
    (hp : p∉harnackLocalForcingSet n) : harnackLocalSource n ell L p=0 := by
  by_cases ht : p.2∈Icc (harnackLocalEpsilon n) (2*harnackLocalEpsilon n)
  · have hx : p.1∉Metric.closedBall (0 : Space n) (Real.sqrt (3/128)) := fun h => hp ⟨h,ht⟩
    have hn : Real.sqrt (3/128) < ‖p.1‖ := by
      simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
    have hn2 : 3/128 ≤ ‖p.1‖^2 := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/128)
      nlinarith [Real.sqrt_nonneg (3/128)]
    have hLevel : harnackLocalRadiusSq n p.2-‖p.1‖^2 ≤ 0 :=
      sub_nonpos.mpr ((harnack_local_radius_transition n ht.2).trans hn2)
    simp only [harnackLocalSource,harnackPositiveCube,max_eq_right hLevel,
      zero_pow (by decide : 3≠0),mul_zero]
  · have hd : deriv (harnackLocalCutoff n) p.2=0 := by
      rcases not_and_or.mp ht with h | h
      · exact harnack_localCutoff_deriv_zero_left n (le_of_not_ge h)
      · exact harnack_localCutoff_deriv_zero_right n (le_of_not_ge h)
    simp only [harnackLocalSource,hd,mul_zero,zero_mul]

theorem harnack_localK_pos (n : ℕ) (ell L : ℝ) : 0 < harnackLocalK n ell L := by
  have ha := harnack_localAmplitude_pos n ell L
  have he := harnack_localEpsilon_pos n
  unfold harnackLocalK
  positivity

theorem harnack_localM_gt_one (n : ℕ) (ell L : ℝ) : 1 < harnackLocalM n ell L := by
  have ha := harnack_localAmplitude_pos n ell L
  have hk := harnack_localKappa_pos n
  have hProd : 0 < harnackLocalAmplitude n ell L*(1/64+2*harnackLocalKappa n)^3 := by positivity
  unfold harnackLocalM
  linarith

theorem harnack_localSource_bounds {n : ℕ} {ell L : ℝ} (hell : 0 < ell) (p : Point n) :
    0 ≤ harnackLocalSource n ell L p ∧ harnackLocalSource n ell L p ≤ harnackLocalK n ell L := by
  have ha := harnack_localAmplitude_pos n ell L
  have hd := harnack_localCutoff_deriv_bounds n p.2
  have he := harnack_localEpsilon_pos n
  have hExp0 : 0 ≤ Real.exp (-harnackLocalDecay n ell L*p.2) := (Real.exp_pos _).le
  have hP0 : 0 ≤ harnackPositiveCube (harnackLocalRadiusSq n p.2-‖p.1‖^2) :=
    pow_nonneg (le_max_right _ _) _
  refine ⟨mul_nonneg (mul_nonneg (mul_nonneg ha.le hd.1) hExp0) hP0,?_⟩
  by_cases hd0 : deriv (harnackLocalCutoff n) p.2=0
  · simp only [harnackLocalSource,hd0,mul_zero,zero_mul]
    exact (harnack_localK_pos n ell L).le
  have ht0 : harnackLocalEpsilon n < p.2 := by
    by_contra ht
    exact hd0 (harnack_localCutoff_deriv_zero_left n (not_lt.mp ht))
  have ht1 : p.2 < 2*harnackLocalEpsilon n := by
    by_contra ht
    exact hd0 (harnack_localCutoff_deriv_zero_right n (not_lt.mp ht))
  have hDecay := harnack_localDecay_pos (n := n) (L := L) hell
  have hTime : 0 < p.2 := (harnack_localEpsilon_pos n).trans ht0
  have hExp : Real.exp (-harnackLocalDecay n ell L*p.2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hLevel : max (harnackLocalRadiusSq n p.2-‖p.1‖^2) 0 ≤ 3/128 :=
    max_le (by linarith [harnack_local_radius_transition n ht1.le,sq_nonneg ‖p.1‖]) (by norm_num)
  have hP : harnackPositiveCube (harnackLocalRadiusSq n p.2-‖p.1‖^2) ≤ (3/128 : ℝ)^3 :=
    pow_le_pow_left₀ (le_max_right _ _) hLevel _
  calc
    _ ≤ harnackLocalAmplitude n ell L*(15/(8*harnackLocalEpsilon n))*1*(3/128 : ℝ)^3 := by
      dsimp only [harnackLocalSource]
      gcongr
      exact hd.2
    _ = _ := by dsimp only [harnackLocalK]; ring

theorem harnack_localPhi_bound {n : ℕ} {ell L : ℝ} (hell : 0 < ell)
    (p : Point n) (hp : p∈harnackClosed 0 (harnackLocalRadius n) 0 2) :
    harnackLocalPhi n ell L p ≤ harnackLocalM n ell L := by
  have ha := harnack_localAmplitude_pos n ell L
  have hk := harnack_localKappa_pos n
  have hchi := harnack_localCutoff_bounds n p.2
  have ht : p.2∈Icc (0 : ℝ) 2 := by simpa only [zero_add] using hp.2
  have hS := harnack_local_radius_time_bounds n ht
  have hDecay := harnack_localDecay_pos (n := n) (L := L) hell
  have hExp0 : 0 ≤ Real.exp (-harnackLocalDecay n ell L*p.2) := (Real.exp_pos _).le
  have hExp : Real.exp (-harnackLocalDecay n ell L*p.2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
  have hLevel : max (harnackLocalRadiusSq n p.2-‖p.1‖^2) 0 ≤ 1/64+2*harnackLocalKappa n :=
    max_le (by linarith [sq_nonneg ‖p.1‖]) (by positivity)
  have hP0 : 0 ≤ harnackPositiveCube (harnackLocalRadiusSq n p.2-‖p.1‖^2) :=
    pow_nonneg (le_max_right _ _) _
  have hP : harnackPositiveCube (harnackLocalRadiusSq n p.2-‖p.1‖^2) ≤
      (1/64+2*harnackLocalKappa n)^3 :=
    pow_le_pow_left₀ (le_max_right _ _) hLevel _
  have hSeed : harnackBump (harnackLocalCutoff n) (harnackLocalRadiusSq n)
      (fun _ => (0 : Space n)) (harnackLocalDecay n ell L) 0 p ≤
        (1/64+2*harnackLocalKappa n)^3 := by
    dsimp only [harnackBump]
    simp only [sub_zero,add_zero]
    have hFirst : harnackLocalCutoff n p.2*Real.exp (-harnackLocalDecay n ell L*p.2) ≤ 1*1 :=
      mul_le_mul hchi.2 hExp hExp0 (by norm_num)
    have hLast := mul_le_mul hFirst hP hP0 (by norm_num : (0 : ℝ) ≤ 1*1)
    simpa only [one_mul] using hLast
  have hScaled := mul_le_mul_of_nonneg_left hSeed ha.le
  change harnackLocalAmplitude n ell L*(_ : ℝ) ≤
    2+harnackLocalAmplitude n ell L*(1/64+2*harnackLocalKappa n)^3
  linarith

theorem harnack_localPhi_boundary (n : ℕ) (ell L : ℝ) (p : Point n)
    (hp : p∈harnackBoundary 0 (harnackLocalRadius n) 0 2) :
    harnackLocalPhi n ell L p=0 := by
  rcases hp with hp | hp
  · have ht : p.2=0 := hp.2
    have hChi : harnackLocalCutoff n 0=0 :=
      harnack_step_eq_zero (div_nonpos_of_nonpos_of_nonneg (by linarith [harnack_localEpsilon_pos n])
        (harnack_localEpsilon_pos n).le)
    simp only [harnackLocalPhi,harnackBump,ht,hChi,zero_mul,mul_zero]
  · have ht : p.2∈Icc (0 : ℝ) 2 := by simpa only [zero_add] using hp.2
    have hS := harnack_local_radius_time_bounds n ht
    have hx : ‖p.1‖=harnackLocalRadius n := by
      simpa only [Metric.mem_sphere,dist_zero_right] using hp.1
    have hLevel : harnackLocalRadiusSq n p.2-‖p.1‖^2 ≤ 0 := by
      rw [hx,harnack_localRadius_sq]
      linarith
    simp only [harnackLocalPhi,harnackBump,sub_zero,harnackPositiveCube,max_eq_right hLevel,
      zero_pow (by decide : 3≠0),mul_zero]

theorem harnack_localPhi_target {n : ℕ} {ell L : ℝ} (hell : 0 < ell) (p : Point n)
    (hp : p∈Metric.closedBall (0 : Space n) (2*Real.sqrt (2*n)) ×ˢ Icc (1 : ℝ) 2) :
    2 ≤ harnackLocalPhi n ell L p := by
  have hDecay := harnack_localDecay_pos (n := n) (L := L) hell
  have ha := harnack_localAmplitude_pos n ell L
  have hk := harnack_localKappa_pos n
  have hchi : harnackLocalCutoff n p.2=1 := harnack_step_eq_one
    ((le_div_iff₀ (harnack_localEpsilon_pos n)).mpr (by linarith [harnack_localEpsilon_small n,hp.2.1]))
  have hNorm : ‖p.1‖ ≤ 2*Real.sqrt (2*n) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
  have hNorm2 : ‖p.1‖^2 ≤ 4*(2*n) := by
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*n)
    nlinarith [norm_nonneg p.1,Real.sqrt_nonneg (2*n)]
  have hS : 1/64+harnackLocalKappa n ≤ harnackLocalRadiusSq n p.2 := by
    have h := mul_le_mul_of_nonneg_left hp.2.1 hk.le
    dsimp only [harnackLocalRadiusSq]
    linarith
  have hQ : harnackLocalGap n ≤ harnackLocalRadiusSq n p.2-‖p.1‖^2 := by
    dsimp only [harnackLocalGap]
    linarith
  have hP : (harnackLocalGap n)^3 ≤ harnackPositiveCube (harnackLocalRadiusSq n p.2-‖p.1‖^2) :=
    pow_le_pow_left₀ (harnack_localGap_pos n).le (hQ.trans (le_max_left _ _)) 3
  have hExp : Real.exp (-2*harnackLocalDecay n ell L) ≤
      Real.exp (-harnackLocalDecay n ell L*p.2) := Real.exp_le_exp.mpr (by nlinarith [hp.2.2])
  have hSeed : Real.exp (-2*harnackLocalDecay n ell L)*(harnackLocalGap n)^3 ≤
      harnackBump (harnackLocalCutoff n) (harnackLocalRadiusSq n)
        (fun _ => (0 : Space n)) (harnackLocalDecay n ell L) 0 p := by
    dsimp only [harnackBump]
    rw [hchi]
    simp only [one_mul,sub_zero,add_zero]
    exact mul_le_mul hExp hP (pow_nonneg (harnack_localGap_pos n).le _) (Real.exp_pos _).le
  have hScaled := mul_le_mul_of_nonneg_left hSeed ha.le
  have hEq : harnackLocalAmplitude n ell L*
      (Real.exp (-2*harnackLocalDecay n ell L)*(harnackLocalGap n)^3)=2 := by
    have hExpEq : Real.exp (2*harnackLocalDecay n ell L)*Real.exp (-2*harnackLocalDecay n ell L)=1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      _ = 2*(Real.exp (2*harnackLocalDecay n ell L)*Real.exp (-2*harnackLocalDecay n ell L)) := by
        dsimp only [harnackLocalAmplitude]
        field_simp [(harnack_localGap_pos n).ne']
      _ = 2 := by rw [hExpEq,mul_one]
  rw [hEq] at hScaled
  exact hScaled

theorem harnack_localForcingSet_subset_open (n : ℕ) :
    harnackLocalForcingSet n ⊆ harnackOpen 0 (harnackLocalRadius n) 0 2 := by
  intro p hp
  have hR : 1 < harnackLocalRadius n := by
    have hs := harnack_localRadius_sq n
    have hPos := harnack_localRadius_pos n
    nlinarith [harnack_localKappa_pos n]
  have hr : Real.sqrt (3/128) < (1 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/128)
    nlinarith [Real.sqrt_nonneg (3/128)]
  refine ⟨Metric.closedBall_subset_ball (hr.trans hR) hp.1,?_,?_⟩
  · exact lt_of_lt_of_le (harnack_localEpsilon_pos n) hp.2.1
  · have h := harnack_localEpsilon_small n
    change p.2 < 0+2
    linarith [hp.2.2]

theorem harnack_local_target_subset_closed (n : ℕ) :
    Metric.closedBall (0 : Space n) (2*Real.sqrt (2*n)) ×ˢ Icc (1 : ℝ) 2 ⊆
      harnackClosed 0 (harnackLocalRadius n) 0 2 := by
  intro p hp
  have hR : 2*Real.sqrt (2*n) ≤ harnackLocalRadius n := by
    have hs := harnack_localRadius_sq n
    have hPos := harnack_localRadius_pos n
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*n)
    have hn := Nat.cast_nonneg n (α := ℝ)
    unfold harnackLocalKappa at hs
    push_cast at hs
    nlinarith [Real.sqrt_nonneg (2*n)]
  exact ⟨Metric.closedBall_subset_closedBall hR hp.1,by linarith [hp.2.1],by simpa only [zero_add] using hp.2.2⟩

def harnackLocalJ (n : ℕ) (ell L : ℝ) : ℝ :=
  (1/(2*harnackABPCoefficient n ell (harnackLocalRadius n) 2*harnackLocalK n ell L))^(2*n+1)

theorem harnack_localJ_pos {n : ℕ} {ell L : ℝ} (hell : 0 < ell) :
    0 < harnackLocalJ n ell L := by
  have hB := harnack_abpCoefficient_pos n hell (harnack_localRadius_pos n) (by norm_num : (0 : ℝ) < 2)
  have hK := harnack_localK_pos n ell L
  unfold harnackLocalJ
  positivity

theorem harnack_reference_local_low_measure {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ}
    (hu : ContinuousOn u (harnackClosed 0 (harnackLocalRadius n) 0 2) ∧
      (∀ z∈harnackClosed 0 (harnackLocalRadius n) 0 2, 0 ≤ u z) ∧
      viscositySuper (harnackOpen 0 (harnackLocalRadius n) 0 2)
        (fun H _ => harnackPucciMinus ell L H) (fun _ => 0) u)
    (hLow : ∃ z∈Metric.closedBall (0 : Space n) (2*Real.sqrt (2*n)) ×ˢ Icc (1 : ℝ) 2,
      u z ≤ 1) :
    harnackLocalJ n ell L ≤
      harnackMu (harnackLocalForcingSet n ∩ {z | u z ≤ harnackLocalM n ell L}) := by
  obtain ⟨z,hz,hu1⟩ := hLow
  exact harnack_localized_cylinder_abp hell hL 0 (harnack_localRadius_pos n) (by norm_num)
    hu (harnack_localPhi_contDiff n ell L) (harnack_localSource_continuous n ell L).continuousOn
    (harnack_localForcingSet_measurable n) (harnack_localForcingSet_subset_open n)
    (harnack_localK_pos n ell L) (fun p _ => harnack_localSource_bounds hell p)
    (fun p _ hp => harnack_localSource_zero n ell L p hp)
    (fun p hp => harnack_localPhi_residual hell hL p (harnack_open_subset_closed hp))
    (fun p hp => (harnack_localPhi_boundary n ell L p hp).le) (harnack_localPhi_bound hell)
    (harnack_local_target_subset_closed n hz) (harnack_localPhi_target hell z hz) hu1

end Yau.LeafProofs.L05Aux






