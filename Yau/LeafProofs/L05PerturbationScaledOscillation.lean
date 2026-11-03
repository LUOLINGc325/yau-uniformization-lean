import Yau.LeafProofs.L05PerturbationUnitOscillation
import Yau.LeafProofs.L05PucciHarnackDomains

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_harnack_closed {n : ℕ} (c : Space n) (R T : ℝ) :
    harnackClosed c R (T-R^2) (R^2)=perturbClosed c R T := by
  simp [harnackClosed,perturbClosed]

theorem perturb_harnack_open {n : ℕ} (c : Space n) (R T : ℝ) :
    harnackOpen c R (T-R^2) (R^2)=perturbOpen c R T := by
  simp [harnackOpen,perturbOpen]

theorem perturb_inverse_quarter_mem {n : ℕ} (c : Space n) {R T : ℝ} (hR : 0 < R)
    {p : Point n} (hp : p∈perturbClosed c (R/4) T) :
    harnackAffineInv c R (T-R^2) (R^2) p∈perturbClosed (0 : Space n) (1/4) 0 := by
  let q := harnackAffineInv c R (T-R^2) (R^2) p
  have hR2 : 0 < R^2 := sq_pos_of_pos hR
  have he : harnackAffine c R (T-R^2) (R^2) q=p :=
    harnack_affine_apply_inv hR.ne' hR2.ne' p
  have hd := harnack_affine_space_dist c (T-R^2) (R^2) hR q
  rw [he] at hd
  have hx : ‖q.1‖ ≤ 1/4 := by
    have hpx : dist p.1 c ≤ R/4 := hp.1
    rw [hd] at hpx
    nlinarith only [hpx,hR]
  have ht : p.2=T+R^2*q.2 := by
    have hh := congrArg Prod.snd he
    rw [harnack_affine_apply] at hh
    change T-R^2+R^2*(q.2+1)=p.2 at hh
    linarith
  have hpLo : T-(R/4)^2 ≤ p.2 := hp.2.1
  have hpHi : p.2 ≤ T := hp.2.2
  have hqLo : -(1/4 : ℝ)^2 ≤ q.2 := by nlinarith only [hpLo,ht,hR2]
  have hqHi : q.2 ≤ 0 := by nlinarith only [hpHi,ht,hR2]
  exact ⟨by simpa only [mem_closedBall,dist_zero_right] using hx,
    by simpa only [zero_sub] using hqLo,hqHi⟩

theorem perturb_scaled_range_contraction {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ theta : ℝ, 1/2 ≤ theta ∧ theta < 1 ∧
      ∀ c : Space n, ∀ R T K : ℝ, 0 < R → 0 ≤ K →
      ∀ w : Point n → ℝ, ContinuousOn w (perturbClosed c R T) →
      ∀ m M : ℝ, (∀ z∈perturbClosed c R T, m ≤ w z ∧ w z ≤ M) →
      viscositySub (perturbOpen c R T) (fun H _ => pucciPlus ell L H) (fun _ => K) w →
      viscositySuper (perturbOpen c R T) (fun H _ => harnackPucciMinus ell L H) (fun _ => -K) w →
      ∃ m' M' : ℝ, m ≤ m' ∧ M' ≤ M ∧
        (∀ z∈perturbClosed c (R/4) T, m' ≤ w z ∧ w z ≤ M') ∧
        M'-m' ≤ theta*(M-m)+K*R^2 := by
  obtain ⟨theta,ht0,ht1,hContract⟩ := perturb_unit_range_contraction hn hell hL
  refine ⟨theta,ht0,ht1,?_⟩
  intro c R T K hR hK w hw m M hRange hSub hSuper
  have hR2 : 0 < R^2 := sq_pos_of_pos hR
  let Z := harnackAffine c R (T-R^2) (R^2)
  have hClosed : MapsTo Z (unitClosed n) (perturbClosed c R T) := by
    intro p hp
    rw [← perturb_harnack_closed]
    exact (harnack_affine_closed_mem_iff (a := T-R^2) c hR hR2 p).mpr hp
  have hOpen : MapsTo Z (unitOpen n) (perturbOpen c R T) := by
    intro p hp
    rw [← perturb_harnack_open]
    exact (harnack_affine_open_mem_iff (a := T-R^2) c hR hR2 p).mpr hp
  have hRatio : R^2/R^2=1 := div_self hR2.ne'
  have hSubPull := harnack_sub_affine_pullback hell.le hL hSub c (a := T-R^2)
    (h := 1) hR hR2 (by norm_num) hOpen
  have hSuperPull := harnack_super_affine_pullback hell.le hL hSuper c (a := T-R^2)
    (h := 1) hR hR2 (by norm_num) hOpen
  simp only [hRatio,one_mul,div_one] at hSubPull hSuperPull
  have hSub' : viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H)
      (fun _ => K*R^2) (fun p => w (Z p)) := by
    simpa only [Z,mul_comm] using hSubPull
  have hSuper' : viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H)
      (fun _ => -(K*R^2)) (fun p => w (Z p)) := by
    simpa only [Z,mul_neg,neg_mul,mul_comm] using hSuperPull
  have hCont : ContinuousOn (fun p => w (Z p)) (unitClosed n) :=
    hw.comp (harnack_affine_contDiff c R (T-R^2) (R^2)).continuous.continuousOn hClosed
  obtain ⟨m',M',hm',hM',hRange',hWidth⟩ := hContract (K*R^2) (mul_nonneg hK hR2.le)
    (fun p => w (Z p)) hCont m M (fun p hp => hRange _ (hClosed hp)) hSub' hSuper'
  refine ⟨m',M',hm',hM',?_,hWidth⟩
  intro p hp
  have hh := hRange' _ (perturb_inverse_quarter_mem c hR hp)
  simpa only [Z,harnack_affine_apply_inv hR.ne' hR2.ne'] using hh

end Yau.LeafProofs.L05Aux
