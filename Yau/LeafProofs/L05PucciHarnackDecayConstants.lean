import Yau.LeafProofs.L05PucciHarnackScaledDensity
import Yau.LeafProofs.L05PucciHarnackPropagationPoint
import Yau.LeafProofs.L05PucciHarnackStackPropagation

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackIterationM (n : ℕ) (ell L : ℝ) : ℕ := Nat.ceil (2/harnackDelta n ell L)+1
def harnackIterationQ (n : ℕ) (ell L : ℝ) : ℝ :=
  (1-harnackDelta n ell L)*(1+1/(harnackIterationM n ell L : ℝ))

theorem harnack_iterationM_pos (n : ℕ) (ell L : ℝ) : 0 < harnackIterationM n ell L := by
  unfold harnackIterationM
  omega

theorem harnack_iterationM_lower (n : ℕ) (ell L : ℝ) :
    2/harnackDelta n ell L ≤ (harnackIterationM n ell L : ℝ) := by
  have h := Nat.le_ceil (2/harnackDelta n ell L)
  unfold harnackIterationM
  push_cast
  linarith

theorem harnack_iterationQ_bounds {n : ℕ} {ell L : ℝ} (hell : 0 < ell) :
    0 < harnackIterationQ n ell L ∧ harnackIterationQ n ell L ≤ 1-harnackDelta n ell L/2 ∧
      harnackIterationQ n ell L < 1 := by
  have hd := harnack_delta_pos (n := n) (L := L) hell
  have hd1 := harnack_delta_le_quarter n ell L
  have hm : (0 : ℝ) < harnackIterationM n ell L := by exact_mod_cast harnack_iterationM_pos n ell L
  have hmLower := harnack_iterationM_lower n ell L
  have hProduct : 2 ≤ (harnackIterationM n ell L : ℝ)*harnackDelta n ell L :=
    (div_le_iff₀ hd).mp hmLower
  have hInv : 1/(harnackIterationM n ell L : ℝ) ≤ harnackDelta n ell L/2 :=
    (div_le_iff₀ hm).mpr (by nlinarith)
  have hqPos : 0 < harnackIterationQ n ell L :=
    mul_pos (by linarith) (by positivity)
  have hqLe : harnackIterationQ n ell L ≤ 1-harnackDelta n ell L/2 := by
    have h := mul_le_mul_of_nonneg_left hInv (by linarith : 0 ≤ 1-harnackDelta n ell L)
    unfold harnackIterationQ
    nlinarith [sq_nonneg (harnackDelta n ell L)]
  exact ⟨hqPos,hqLe,lt_of_le_of_lt hqLe (by linarith)⟩

theorem harnack_small_grid_scale_exists (n m : ℕ) :
    ∃ J : ℕ, let h0 := (1/2 : ℝ)^J
      h0 ≤ 1/128 ∧ (Real.sqrt (2*n)+harnackLocalRadius n+3)*h0 ≤ 1/32 ∧
        (4*(m : ℝ)+6)*h0^2 ≤ 1/64 := by
  let Cx := Real.sqrt (2*n)+harnackLocalRadius n+3
  let Ct := 4*(m : ℝ)+6
  have hCx : 0 < Cx := by dsimp only [Cx]; linarith [Real.sqrt_nonneg (2*n),harnack_localRadius_pos n]
  have hCt : 0 < Ct := by dsimp only [Ct]; positivity
  let eps := min (1/128) (min (1/(32*Cx)) (Real.sqrt (1/(64*Ct))))
  have heps : 0 < eps := by
    apply lt_min (by norm_num)
    exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
  obtain ⟨J,hJ⟩ := exists_pow_lt_of_lt_one heps (by norm_num : (1/2 : ℝ) < 1)
  have hJ0 : 0 < (1/2 : ℝ)^J := pow_pos (by norm_num) _
  have h1 : (1/2 : ℝ)^J ≤ 1/128 := hJ.le.trans (min_le_left _ _)
  have h2 : (1/2 : ℝ)^J ≤ 1/(32*Cx) := hJ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : (1/2 : ℝ)^J ≤ Real.sqrt (1/(64*Ct)) := hJ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3sq := pow_le_pow_left₀ hJ0.le h3 2
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1/(64*Ct))] at h3sq
  have hCxProduct := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 32) hCx)).mp h2
  have hCtProduct := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 64) hCt)).mp h3sq
  exact ⟨J,h1,by nlinarith,by nlinarith⟩

def harnackBufferSpace (n : ℕ) : ℝ := 4*Real.sqrt (2*n)
def harnackBufferTime (m : ℕ) : ℝ := 8*(m : ℝ)+16
def harnackBufferRho (n m : ℕ) (h0 : ℝ) : ℝ :=
  min (h0/4) (min (1/(64*harnackBufferSpace n))
    (min (Real.sqrt (1/(256*harnackBufferTime m))) (1/128)))
def harnackDecayRatio (n : ℕ) (ell L : ℝ) (m : ℕ) : ℝ :=
  max 2 (max (2*harnackLocalM n ell L/harnackStackBeta n ell L m)
    ((4 : ℝ)^(harnackPropagationExponent n ell L)))
def harnackDecayInitialLevel (n : ℕ) (ell L : ℝ) (m : ℕ) (h0 : ℝ) : ℝ :=
  2*harnackLocalM n ell L/(harnackPropagationC n ell L*
    (harnackBufferRho n m h0)^(harnackPropagationExponent n ell L))
def harnackBufferRadius (n m : ℕ) (h0 : ℝ) (k : ℕ) : ℝ :=
  1/4+(4/3)*harnackBufferSpace n*harnackBufferRho n m h0*(1/4 : ℝ)^k
def harnackBufferBottom (n m : ℕ) (h0 : ℝ) (k : ℕ) : ℝ :=
  -3/4-(16/15)*harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k
def harnackBufferTop (n m : ℕ) (h0 : ℝ) (k : ℕ) : ℝ :=
  -1/2+(16/15)*harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k
def harnackBufferDomain (n m : ℕ) (h0 : ℝ) (k : ℕ) : Set (Point n) :=
  Metric.ball 0 (harnackBufferRadius n m h0 k) ×ˢ
    Ioo (harnackBufferBottom n m h0 k) (harnackBufferTop n m h0 k)

theorem harnack_bufferSpace_pos {n : ℕ} (hn : 0 < n) : 0 < harnackBufferSpace n := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity))

theorem harnack_bufferTime_pos (m : ℕ) : 0 < harnackBufferTime m := by
  unfold harnackBufferTime
  positivity

theorem harnack_bufferRho_pos {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) :
    0 < harnackBufferRho n m h0 := by
  have hCx := harnack_bufferSpace_pos hn
  have hCt := harnack_bufferTime_pos m
  exact lt_min (by positivity) (lt_min (by positivity)
    (lt_min (Real.sqrt_pos.mpr (by positivity)) (by norm_num)))

theorem harnack_bufferRho_bounds (n m : ℕ) (h0 : ℝ) :
    harnackBufferRho n m h0 ≤ h0/4 ∧ harnackBufferRho n m h0 ≤ 1/(64*harnackBufferSpace n) ∧
      harnackBufferRho n m h0 ≤ Real.sqrt (1/(256*harnackBufferTime m)) ∧
      harnackBufferRho n m h0 ≤ 1/128 := by
  exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem harnack_buffer_space_product {n m : ℕ} (hn : 0 < n) (h0 : ℝ) :
    harnackBufferSpace n*harnackBufferRho n m h0 ≤ 1/64 := by
  have hCx := harnack_bufferSpace_pos hn
  have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 64) hCx)).mp
    (harnack_bufferRho_bounds n m h0).2.1
  nlinarith

theorem harnack_buffer_time_product {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) :
    harnackBufferTime m*(harnackBufferRho n m h0)^2 ≤ 1/256 := by
  have hCt := harnack_bufferTime_pos m
  have hRho := harnack_bufferRho_pos (m := m) hn hh0
  have h := pow_le_pow_left₀ hRho.le (harnack_bufferRho_bounds n m h0).2.2.1 2
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1/(256*harnackBufferTime m))] at h
  have hProd := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 256) hCt)).mp h
  nlinarith

theorem harnack_decayRatio_bounds (n : ℕ) (ell L : ℝ) (m : ℕ) :
    2 ≤ harnackDecayRatio n ell L m ∧
      2*harnackLocalM n ell L/harnackStackBeta n ell L m ≤ harnackDecayRatio n ell L m ∧
      (4 : ℝ)^(harnackPropagationExponent n ell L) ≤ harnackDecayRatio n ell L m :=
  ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem harnack_decayInitialLevel_pos {n m : ℕ} (hn : 0 < n) (ell L : ℝ)
    {h0 : ℝ} (hh0 : 0 < h0) : 0 < harnackDecayInitialLevel n ell L m h0 := by
  have hM := harnack_localM_gt_one n ell L
  have hC := harnack_propagationC_pos n ell L
  have hRho := harnack_bufferRho_pos (m := m) hn hh0
  exact div_pos (by linarith) (mul_pos hC (Real.rpow_pos_of_pos hRho _))

theorem harnack_buffer_radius_step (n m : ℕ) (h0 : ℝ) (k : ℕ) :
    harnackBufferRadius n m h0 k-harnackBufferRadius n m h0 (k+1)=
      harnackBufferSpace n*harnackBufferRho n m h0*(1/4 : ℝ)^k := by
  unfold harnackBufferRadius
  rw [pow_succ]
  ring

theorem harnack_buffer_bottom_step (n m : ℕ) (h0 : ℝ) (k : ℕ) :
    harnackBufferBottom n m h0 (k+1)-harnackBufferBottom n m h0 k=
      harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by
  unfold harnackBufferBottom
  rw [pow_succ]
  ring

theorem harnack_buffer_top_step (n m : ℕ) (h0 : ℝ) (k : ℕ) :
    harnackBufferTop n m h0 k-harnackBufferTop n m h0 (k+1)=
      harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by
  unfold harnackBufferTop
  rw [pow_succ]
  ring

theorem harnack_buffer_domain_open (n m : ℕ) (h0 : ℝ) (k : ℕ) :
    IsOpen (harnackBufferDomain n m h0 k) := Metric.isOpen_ball.prod isOpen_Ioo

theorem harnack_qminus_subset_buffer {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) (k : ℕ) :
    harnackQminus n ⊆ harnackBufferDomain n m h0 k := by
  have hCx := harnack_bufferSpace_pos hn
  have hCt := harnack_bufferTime_pos m
  have hRho := harnack_bufferRho_pos (m := m) hn hh0
  have hSpace : 1/4 ≤ harnackBufferRadius n m h0 k := by
    unfold harnackBufferRadius
    have hP : 0 ≤ (4/3 : ℝ)*harnackBufferSpace n*harnackBufferRho n m h0*(1/4 : ℝ)^k := by positivity
    linarith
  have hBottom : harnackBufferBottom n m h0 k ≤ -3/4 := by
    unfold harnackBufferBottom
    have hNonneg : 0 ≤ (16/15 : ℝ)*harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by positivity
    linarith
  have hTop : (-1 : ℝ)/2 ≤ harnackBufferTop n m h0 k := by
    unfold harnackBufferTop
    have hNonneg : 0 ≤ (16/15 : ℝ)*harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by positivity
    linarith
  intro p hp
  exact ⟨Metric.ball_subset_ball hSpace hp.1,lt_of_le_of_lt hBottom hp.2.1,lt_of_lt_of_le hp.2.2 hTop⟩

theorem harnack_buffer_domain_antitone {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) :
    Antitone (harnackBufferDomain n m h0) := by
  have hCx := harnack_bufferSpace_pos hn
  have hCt := harnack_bufferTime_pos m
  have hRho := harnack_bufferRho_pos (m := m) hn hh0
  apply antitone_nat_of_succ_le
  intro k p hp
  have hRad := harnack_buffer_radius_step n m h0 k
  have hLo := harnack_buffer_bottom_step n m h0 k
  have hHi := harnack_buffer_top_step n m h0 k
  have hRle : harnackBufferRadius n m h0 (k+1) ≤ harnackBufferRadius n m h0 k := by
    have hP : 0 ≤ harnackBufferSpace n*harnackBufferRho n m h0*(1/4 : ℝ)^k := by positivity
    linarith
  have hLle : harnackBufferBottom n m h0 k ≤ harnackBufferBottom n m h0 (k+1) := by
    have hP : 0 ≤ harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by positivity
    linarith
  have hHle : harnackBufferTop n m h0 (k+1) ≤ harnackBufferTop n m h0 k := by
    have hP : 0 ≤ harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by positivity
    linarith
  exact ⟨Metric.ball_subset_ball hRle hp.1,hLle.trans_lt hp.2.1,hp.2.2.trans_le hHle⟩

theorem harnack_buffer_zero_bounds {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) :
    harnackBufferRadius n m h0 0 < 5/16 ∧
      -13/16 < harnackBufferBottom n m h0 0 ∧ harnackBufferTop n m h0 0 < -7/16 := by
  have hSpace := harnack_buffer_space_product (m := m) hn h0
  have hTime := harnack_buffer_time_product (m := m) hn hh0
  simp only [harnackBufferRadius,harnackBufferBottom,harnackBufferTop,pow_zero,mul_one]
  exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

theorem harnack_buffer_subset_interior {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) (k : ℕ) :
    harnackBufferDomain n m h0 k ⊆ Metric.ball 0 (5/16) ×ˢ Ioo (-13/16) (-7/16) := by
  intro p hp
  have hp0 := harnack_buffer_domain_antitone (m := m) hn hh0 (Nat.zero_le k) hp
  have hBounds := harnack_buffer_zero_bounds (m := m) hn hh0
  exact ⟨Metric.ball_subset_ball hBounds.1.le hp0.1,hBounds.2.1.trans hp0.2.1,hp0.2.2.trans hBounds.2.2⟩

theorem harnack_forward_stack_in_buffer {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0)
    (k : ℕ) {r : ℝ} (hr : 0 < r) (hrSmall : r < harnackBufferRho n m h0*(1/4 : ℝ)^k)
    {p z : Point n} (hp : p∈harnackBufferDomain n m h0 (k+1))
    (hDist : dist z.1 p.1 ≤ 2*Real.sqrt (2*n)*r)
    (hTimeLo : p.2 ≤ z.2) (hTimeHi : z.2 ≤ p.2+4*((m : ℝ)+1)*r^2) :
    z∈harnackBufferDomain n m h0 k := by
  have hCx := harnack_bufferSpace_pos hn
  have hCt := harnack_bufferTime_pos m
  have hRho := harnack_bufferRho_pos (m := m) hn hh0
  have hScale : 0 < harnackBufferRho n m h0*(1/4 : ℝ)^k := by positivity
  have hRadStep := harnack_buffer_radius_step n m h0 k
  have hBottomStep := harnack_buffer_bottom_step n m h0 k
  have hTopStep := harnack_buffer_top_step n m h0 k
  have hpNorm : ‖p.1‖ < harnackBufferRadius n m h0 (k+1) :=
    by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
  have hSqrt : 0 < Real.sqrt (2*n) := by
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr (by positivity)
  have hSpaceInc : 2*Real.sqrt (2*n)*r < harnackBufferSpace n*harnackBufferRho n m h0*(1/4 : ℝ)^k := by
    have h := mul_lt_mul_of_pos_left hrSmall (mul_pos (by norm_num : (0 : ℝ) < 2) hSqrt)
    unfold harnackBufferSpace
    nlinarith [mul_pos hSqrt hScale]
  have hzNorm : ‖z.1‖ < harnackBufferRadius n m h0 k := by
    have hTriangle : ‖z.1‖ ≤ dist z.1 p.1+‖p.1‖ := by
      simpa only [dist_eq_norm,sub_add_cancel] using norm_add_le (z.1-p.1) p.1
    linarith
  have hPow : ((1/4 : ℝ)^k)^2=(1/16 : ℝ)^k := by rw [← pow_mul,mul_comm k 2,pow_mul]; norm_num
  have hRSq := pow_le_pow_left₀ hr.le hrSmall.le 2
  rw [mul_pow,hPow] at hRSq
  have hTimeInc : 4*((m : ℝ)+1)*r^2 < harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by
    have h := mul_le_mul_of_nonneg_left hRSq (by positivity : (0 : ℝ) ≤ 4*((m : ℝ)+1))
    have hS : 0 < (harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by positivity
    unfold harnackBufferTime
    nlinarith [mul_pos (by positivity : (0 : ℝ) < 4*(m : ℝ)+12) hS]
  refine ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hzNorm,?_,?_⟩
  · have hNonneg : 0 ≤ harnackBufferTime m*(harnackBufferRho n m h0)^2*(1/16 : ℝ)^k := by positivity
    linarith [hp.2.1]
  · linarith [hp.2.2]

theorem harnack_level_radius_scale {r rho alpha M C K : ℝ}
    (hr : 0 ≤ r) (hRho : 0 < rho) (hAlpha : 0 < alpha) (hM : 0 < M) (hC : 0 < C)
    (hK : 2 ≤ K) (hKscale : (4 : ℝ)^alpha ≤ K) (k : ℕ)
    (hBound : r^alpha ≤ M/(C*((2*M/(C*rho^alpha))*K^(k+1)))) :
    r < rho*(1/4 : ℝ)^k := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hRpow : 0 < rho^alpha := Real.rpow_pos_of_pos hRho _
  have h4pow : 0 < (4 : ℝ)^alpha := Real.rpow_pos_of_pos (by norm_num) _
  have hNormalize : M/(C*((2*M/(C*rho^alpha))*K^(k+1)))=rho^alpha/(2*K^(k+1)) := by
    field_simp [hC.ne',hM.ne',hRpow.ne',pow_ne_zero _ hKpos.ne']
  rw [hNormalize] at hBound
  have hDen : K^k < 2*K^(k+1) := by
    have h := mul_lt_mul_of_pos_left (by linarith : (1 : ℝ) < 2*K) (pow_pos hKpos k)
    rw [pow_succ]
    nlinarith only [h]
  have hStrict : rho^alpha/(2*K^(k+1)) < rho^alpha/K^k := by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2*K^(k+1)) (pow_pos hKpos k)).mpr
    exact mul_lt_mul_of_pos_left hDen hRpow
  have hPowCompare : ((4 : ℝ)^alpha)^k ≤ K^k := pow_le_pow_left₀ h4pow.le hKscale _
  have hDivCompare : rho^alpha/K^k ≤ rho^alpha/((4 : ℝ)^alpha)^k := by
    apply (div_le_div_iff₀ (pow_pos hKpos k) (pow_pos h4pow k)).mpr
    exact mul_le_mul_of_nonneg_left hPowCompare hRpow.le
  have hTarget : (rho*(1/4 : ℝ)^k)^alpha=rho^alpha/((4 : ℝ)^alpha)^k := by
    rw [Real.mul_rpow hRho.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/4) k),
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1/4) alpha k]
    have hInv : (1/4 : ℝ)^alpha=((4 : ℝ)^alpha)⁻¹ := by
      rw [one_div,Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4)]
    rw [hInv,inv_pow,div_eq_mul_inv]
  apply (Real.rpow_lt_rpow_iff hr (mul_nonneg hRho.le (pow_nonneg (by norm_num) _)) hAlpha).mp
  rw [hTarget]
  exact lt_of_lt_of_le (lt_of_le_of_lt hBound hStrict) hDivCompare

theorem harnack_decay_level_radius {n m : ℕ} (hn : 0 < n) {ell L h0 r : ℝ}
    (hell : 0 < ell) (hh0 : 0 < h0) (hr : 0 ≤ r) (k : ℕ)
    (hBound : r^(harnackPropagationExponent n ell L) ≤
      harnackLocalM n ell L/(harnackPropagationC n ell L*
        (harnackDecayInitialLevel n ell L m h0*(harnackDecayRatio n ell L m)^(k+1)))) :
    r < harnackBufferRho n m h0*(1/4 : ℝ)^k := by
  have hM : 0 < harnackLocalM n ell L := lt_trans (by norm_num) (harnack_localM_gt_one n ell L)
  exact harnack_level_radius_scale hr (harnack_bufferRho_pos hn hh0)
    (harnack_propagationExponent_pos hell) hM (harnack_propagationC_pos n ell L)
    (harnack_decayRatio_bounds n ell L m).1 (harnack_decayRatio_bounds n ell L m).2.2 k hBound

theorem harnack_decay_stack_level {n m : ℕ} {ell L H0 : ℝ} (hH0 : 0 < H0) (k : ℕ) :
    2*(H0*(harnackDecayRatio n ell L m)^k) ≤
      harnackStackBeta n ell L m*(H0*(harnackDecayRatio n ell L m)^(k+1)/harnackLocalM n ell L) := by
  have hM : 0 < harnackLocalM n ell L := lt_trans (by norm_num) (harnack_localM_gt_one n ell L)
  have hBeta := harnack_stackBeta_pos n ell L m
  have hK : 0 < harnackDecayRatio n ell L m := lt_of_lt_of_le (by norm_num) (harnack_decayRatio_bounds n ell L m).1
  have hRatio := (div_le_iff₀ hBeta).mp (harnack_decayRatio_bounds n ell L m).2.1
  have hScaled := mul_le_mul_of_nonneg_left hRatio (mul_pos hH0 (pow_pos hK k)).le
  rw [pow_succ,← mul_div_assoc]
  apply (le_div_iff₀ hM).mpr
  convert hScaled using 1 <;> ring

theorem harnack_closed_cylinder_subset_unitOpen {n : ℕ} {c : Space n} {R a T : ℝ}
    (hSpace : ‖c‖+R < 1) (hLo : -1 < a) (hHi : a+T < 0) :
    harnackClosed c R a T ⊆ unitOpen n := by
  intro p hp
  have hx : ‖p.1-c‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hp.1
  have hTriangle : ‖p.1‖ ≤ ‖p.1-c‖+‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (p.1-c) c
  exact ⟨by simp only [Metric.mem_ball,dist_zero_right]; linarith,
    hLo.trans_le hp.2.1,hp.2.2.trans_lt hHi⟩

theorem harnack_cube_cylinder_budgets {n m : ℕ} (hn : 0 < n) {h0 : ℝ}
    (hh0 : 0 < h0)
    (hSpace : (Real.sqrt (2*n)+harnackLocalRadius n+3)*h0 ≤ 1/32)
    (hTime : (4*(m : ℝ)+6)*h0^2 ≤ 1/64)
    {c : Space n} {r a : ℝ} (hr : 0 < r) (hr0 : r ≤ h0)
    {p : Point n} (hp : p∈harnackBufferDomain n m h0 0)
    (hDist : dist c p.1 ≤ Real.sqrt (2*n)*r/2)
    (hpTime : p.2∈Ioc a (a+r^2)) :
    ‖c‖ ≤ 3/8 ∧ a+r^2∈Icc (-7/8 : ℝ) (-13/32) ∧
      (harnackClosed c (harnackLocalRadius n*r) a (2*r^2) ⊆ unitOpen n) ∧
      (harnackClosed c (2*Real.sqrt (2*n)*r) (a+r^2) (harnackStackDuration m*r^2) ⊆ unitOpen n) := by
  have hBounds := harnack_buffer_zero_bounds (m := m) hn hh0
  have hpNorm : ‖p.1‖ < 5/16 := by
    have hSmall : ‖p.1‖ < harnackBufferRadius n m h0 0 := by
      simpa only [Metric.mem_ball,dist_zero_right] using hp.1
    exact hSmall.trans hBounds.1
  have hpLo : -13/16 < p.2 := hBounds.2.1.trans hp.2.1
  have hpHi : p.2 < -7/16 := hp.2.2.trans hBounds.2.2
  have hSqrt := Real.sqrt_nonneg (2*n)
  have hR := harnack_localRadius_pos n
  have hSqrtProduct : Real.sqrt (2*n)*h0 ≤ 1/32 := by
    nlinarith [mul_nonneg hR.le hh0.le]
  have hRProduct : harnackLocalRadius n*h0 ≤ 1/32 := by
    nlinarith [mul_nonneg hSqrt hh0.le]
  have hSqrtR : Real.sqrt (2*n)*r ≤ 1/32 :=
    (mul_le_mul_of_nonneg_left hr0 hSqrt).trans hSqrtProduct
  have hLocalR : harnackLocalRadius n*r ≤ 1/32 :=
    (mul_le_mul_of_nonneg_left hr0 hR.le).trans hRProduct
  have hCenterTriangle : ‖c‖ ≤ dist c p.1+‖p.1‖ := by
    simpa only [dist_eq_norm,sub_add_cancel] using norm_add_le (c-p.1) p.1
  have hc : ‖c‖ ≤ 3/8 := by linarith
  have hrSq : r^2 ≤ h0^2 := pow_le_pow_left₀ hr.le hr0 _
  have hTimeR : (4*(m : ℝ)+6)*r^2 ≤ 1/64 :=
    (mul_le_mul_of_nonneg_left hrSq (by positivity)).trans hTime
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hR2 : r^2 ≤ 1/64 := by
    nlinarith [mul_nonneg hm0 (sq_nonneg r)]
  have hTwoR2 : 2*r^2 ≤ 1/64 := by
    nlinarith [mul_nonneg hm0 (sq_nonneg r)]
  have hStackTime : (4*(m : ℝ)+4)*r^2 ≤ 1/64 := by nlinarith [sq_nonneg r]
  have ht0 : a+r^2∈Icc (-7/8 : ℝ) (-13/32) :=
    ⟨by linarith [hpTime.2],by linarith [hpTime.1]⟩
  refine ⟨hc,ht0,?_,?_⟩
  · apply harnack_closed_cylinder_subset_unitOpen
    · linarith
    · linarith [hpTime.2]
    · linarith [hpTime.1]
  · apply harnack_closed_cylinder_subset_unitOpen
    · linarith
    · linarith [hpTime.2,sq_nonneg r]
    · unfold harnackStackDuration
      nlinarith [hpTime.1]

theorem harnack_buffer_subset_unitOpen {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) (k : ℕ) :
    harnackBufferDomain n m h0 k ⊆ unitOpen n := by
  intro p hp
  have h := harnack_buffer_subset_interior hn hh0 k hp
  exact ⟨Metric.ball_subset_ball (by norm_num : (5/16 : ℝ) ≤ 1) h.1,
    by linarith [h.2.1],by linarith [h.2.2]⟩

theorem harnack_buffer_domain_bounded {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) (k : ℕ) :
    Bornology.IsBounded (harnackBufferDomain n m h0 k) :=
  ((isCompact_closedBall (0 : Space n) 1).prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))).isBounded.subset
    (fun _p hp => unitOpen_subset_unitClosed (harnack_buffer_subset_unitOpen hn hh0 k hp))

theorem harnack_buffer_measure_ne_top {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) (k : ℕ) :
    (volume : Measure (Point n)) (harnackBufferDomain n m h0 k) ≠ ⊤ :=
  ne_top_of_le_ne_top
    ((isCompact_closedBall (0 : Space n) 1).prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))).measure_ne_top
    (measure_mono (fun _p hp => unitOpen_subset_unitClosed (harnack_buffer_subset_unitOpen hn hh0 k hp)))

theorem harnack_buffer_mu_pos {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) (k : ℕ) :
    0 < harnackMu (harnackBufferDomain n m h0 k) :=
  (harnack_qminus_mu_pos n).trans_le
    (harnack_mu_mono (harnack_buffer_measure_ne_top hn hh0 k) (harnack_qminus_subset_buffer hn hh0 k))

theorem harnack_buffer_level_open {n m : ℕ} (hn : 0 < n) {h0 : ℝ} (hh0 : 0 < h0) (k : ℕ)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n)) (H : ℝ) :
    IsOpen (harnackBufferDomain n m h0 k ∩ {z | H < u z}) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hzUnit := harnack_buffer_subset_unitOpen hn hh0 k hz.1
  have hCont : ContinuousAt u z := hu.continuousAt
    (mem_of_superset ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hzUnit) unitOpen_subset_unitClosed)
  have hLevel : {p | H < u p}∈𝓝 z := hCont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hz.2)
  exact inter_mem ((harnack_buffer_domain_open n m h0 k).mem_nhds hz.1) hLevel

end Yau.LeafProofs.L05Aux
