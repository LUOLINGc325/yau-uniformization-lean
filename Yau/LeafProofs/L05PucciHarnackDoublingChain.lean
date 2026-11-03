import Yau.LeafProofs.L05PucciHarnackPhysicalDoubling

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_doubling_levels {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1/128) :
    ∃ N : ℕ, 0 < N ∧ 1/64 ≤ (2 : ℝ)^N*r ∧ (2 : ℝ)^N*r < 1/32 ∧
      ∀ j<N, (2 : ℝ)^j*r < 1/64 := by
  have hExists : ∃ N : ℕ, (1/64 : ℝ) ≤ (2 : ℝ)^N*r := by
    obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt ((1/64 : ℝ)/r) (by norm_num : (1 : ℝ) < 2)
    exact ⟨N,((div_le_iff₀ hr).mp hN.le)⟩
  let N := Nat.find hExists
  have hLower : (1/64 : ℝ) ≤ (2 : ℝ)^N*r := Nat.find_spec hExists
  have hNpos : 0 < N := by
    by_contra h
    have hN0 : N=0 := by omega
    rw [hN0,pow_zero,one_mul] at hLower
    linarith
  have hMinimal (j : ℕ) (hj : j<N) : (2 : ℝ)^j*r < 1/64 :=
    lt_of_not_ge (Nat.find_min hExists hj)
  have hPred := hMinimal (N-1) (by omega)
  have hPredEq : N-1+1=N := by omega
  have hPow : (2 : ℝ)^N*r=2*((2 : ℝ)^(N-1)*r) := by
    conv_lhs => rw [← hPredEq,pow_succ]
    ring
  exact ⟨N,hNpos,hLower,by rw [hPow]; linarith,hMinimal⟩

def harnackDoublingRadius (r : ℝ) (j : ℕ) : ℝ := (2 : ℝ)^j*r
def harnackDoublingTime (r t0 : ℝ) (j : ℕ) : ℝ := t0+r^2*((4 : ℝ)^j-1)/3

theorem harnack_doublingRadius_pos {r : ℝ} (hr : 0 < r) (j : ℕ) :
    0 < harnackDoublingRadius r j := mul_pos (pow_pos (by norm_num) _) hr

theorem harnack_doublingRadius_succ (r : ℝ) (j : ℕ) :
    harnackDoublingRadius r (j+1)=2*harnackDoublingRadius r j := by
  unfold harnackDoublingRadius
  rw [pow_succ]
  ring

theorem harnack_doublingRadius_sq (r : ℝ) (j : ℕ) :
    (harnackDoublingRadius r j)^2=(4 : ℝ)^j*r^2 := by
  rw [harnackDoublingRadius,mul_pow,← pow_mul,mul_comm j 2,pow_mul]
  norm_num

theorem harnack_doublingTime_succ (r t0 : ℝ) (j : ℕ) :
    harnackDoublingTime r t0 (j+1)=harnackDoublingTime r t0 j+(harnackDoublingRadius r j)^2 := by
  rw [harnackDoublingTime,harnackDoublingTime,harnack_doublingRadius_sq,pow_succ]
  ring

theorem harnack_doublingTime_bounds {r t0 : ℝ} (hr : 0 < r) (j : ℕ) :
    t0 ≤ harnackDoublingTime r t0 j ∧
      harnackDoublingTime r t0 j < t0+(harnackDoublingRadius r j)^2/3 := by
  have hPow : (1 : ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  rw [harnackDoublingTime,harnack_doublingRadius_sq]
  constructor
  · have hProd : 0 ≤ r^2*((4 : ℝ)^j-1) := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hPow)
    linarith
  · nlinarith [sq_pos_of_ne_zero hr.ne']

theorem harnack_doubling_chain {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {c : Space n} {r t0 H : ℝ} (hc : ‖c‖ ≤ 3/8) (hr : 0 < r) (hr1 : r ≤ 1/128)
    (ht0 : t0∈Icc (-7/8 : ℝ) (-13/32)) (hH : 0 < H)
    (hBall : ∀ x∈Metric.closedBall c r, H ≤ u (x,t0)) :
    ∃ N : ℕ, 0 < N ∧ 1/64 ≤ harnackDoublingRadius r N ∧ harnackDoublingRadius r N < 1/32 ∧
      t0 ≤ harnackDoublingTime r t0 N ∧ harnackDoublingTime r t0 N < t0+1/3072 ∧
      ∀ x∈Metric.closedBall c (harnackDoublingRadius r N),
        (harnackDoublingBeta n ell L)^N*H ≤ u (x,harnackDoublingTime r t0 N) := by
  obtain ⟨N,hNpos,hNlo,hNhi,hSmall⟩ := harnack_doubling_levels hr hr1
  have hRadSmall (j : ℕ) (hj : j ≤ N) : harnackDoublingRadius r j < 1/32 := by
    apply lt_of_le_of_lt _ hNhi
    unfold harnackDoublingRadius
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hr.le
  have hTimeSmall (j : ℕ) (hj : j ≤ N) :
      t0 ≤ harnackDoublingTime r t0 j ∧ harnackDoublingTime r t0 j < t0+1/3072 := by
    have h := harnack_doublingTime_bounds (t0 := t0) hr j
    have hRad := hRadSmall j hj
    have hRadPos := harnack_doublingRadius_pos hr j
    exact ⟨h.1,by nlinarith [h.2]⟩
  have hCyl (j : ℕ) (hj : j<N) :
      harnackClosed c (3*harnackDoublingRadius r j) (harnackDoublingTime r t0 j)
        ((harnackDoublingRadius r j)^2) ⊆ unitOpen n := by
    intro p hp
    have hRadius : harnackDoublingRadius r j < 1/64 := hSmall j hj
    have hxDist : ‖p.1-c‖ ≤ 3*harnackDoublingRadius r j := by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hp.1
    have hxNorm : ‖p.1‖ < 1 := by
      have hTriangle : ‖p.1‖ ≤ ‖p.1-c‖+‖c‖ := by
        simpa only [sub_add_cancel] using norm_add_le (p.1-c) c
      linarith
    have hTimeLo := (hTimeSmall j (by omega)).1
    have hTimeHi := (hTimeSmall (j+1) (by omega)).2
    rw [harnack_doublingTime_succ] at hTimeHi
    exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hxNorm,
      by linarith [hp.2.1,ht0.1],by linarith [hp.2.2,ht0.2]⟩
  have hBeta := harnack_doublingBeta_bounds (n := n) (L := L) hell
  have hInd : ∀ j≤N, ∀ x∈Metric.closedBall c (harnackDoublingRadius r j),
      (harnackDoublingBeta n ell L)^j*H ≤ u (x,harnackDoublingTime r t0 j) := by
    intro j
    induction j with
    | zero =>
      intro _ x hx
      simpa only [harnackDoublingRadius,harnackDoublingTime,pow_zero,mul_one,one_mul,
        sub_self,mul_zero,zero_div,add_zero] using hBall x (by simpa only [harnackDoublingRadius,pow_zero,one_mul] using hx)
    | succ j ih =>
      intro hj x hx
      have hjN : j<N := by omega
      have hClosed : harnackClosed c (3*harnackDoublingRadius r j) (harnackDoublingTime r t0 j)
          ((harnackDoublingRadius r j)^2) ⊆ unitClosed n :=
        fun p hp => unitOpen_subset_unitClosed (hCyl j hjN hp)
      have hOpen : harnackOpen c (3*harnackDoublingRadius r j) (harnackDoublingTime r t0 j)
          ((harnackDoublingRadius r j)^2) ⊆ unitOpen n :=
        fun p hp => hCyl j hjN (harnack_open_subset_closed hp)
      have hStep := harnack_positive_ball_doubles hell hL hu (harnack_doublingRadius_pos hr j)
        (mul_pos (pow_pos hBeta.1 _) hH) hClosed hOpen (ih (by omega))
      have hx' : x∈Metric.closedBall c (2*harnackDoublingRadius r j) := by
        rwa [← harnack_doublingRadius_succ]
      have h := hStep x hx'
      rw [← harnack_doublingTime_succ] at h
      simpa only [pow_succ,mul_assoc,mul_left_comm] using h
  exact ⟨N,hNpos,hNlo,hNhi,(hTimeSmall N le_rfl).1,(hTimeSmall N le_rfl).2,hInd N le_rfl⟩

def harnackPropagationExponent (n : ℕ) (ell L : ℝ) : ℝ :=
  harnackDoublingDecay n ell L/Real.log 2

theorem harnack_propagationExponent_pos {n : ℕ} {ell L : ℝ} (hell : 0 < ell) :
    0 < harnackPropagationExponent n ell L :=
  div_pos (harnack_bumpDecay_pos hell (by norm_num)) (Real.log_pos (by norm_num))

theorem harnack_doubling_amplitude_lower {n : ℕ} {ell L r : ℝ} (hell : 0 < ell)
    (hr : 0 < r) (N : ℕ) (hRadius : (2 : ℝ)^N*r ≤ 1) :
    r^(harnackPropagationExponent n ell L) ≤ (harnackDoublingBeta n ell L)^N := by
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hAlpha := harnack_propagationExponent_pos (n := n) (L := L) hell
  have hLog := Real.log_le_log (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) hr) hRadius
  rw [Real.log_one,Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ)≠0)) hr.ne',Real.log_pow] at hLog
  have hProduct := mul_le_mul_of_nonneg_right hLog hAlpha.le
  have hCancel : ((N : ℝ)*Real.log 2+Real.log r)*harnackPropagationExponent n ell L=
      (N : ℝ)*harnackDoublingDecay n ell L+Real.log r*harnackPropagationExponent n ell L := by
    unfold harnackPropagationExponent
    field_simp [hLog2.ne']
  rw [hCancel,zero_mul] at hProduct
  rw [Real.rpow_def_of_pos hr]
  unfold harnackDoublingBeta
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by linarith)

end Yau.LeafProofs.L05Aux


