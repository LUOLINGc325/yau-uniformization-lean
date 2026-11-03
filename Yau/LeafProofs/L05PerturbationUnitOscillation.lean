import Yau.LeafProofs.L05PerturbationMeanDeficits
import Yau.LeafProofs.L05PerturbationGeometry

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_sub_neg_super {n : ℕ} {Q : Set (Point n)} {ell L K : ℝ}
    {w : Point n → ℝ}
    (hw : viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => K) w) :
    viscositySuper Q (fun H _ => harnackPucciMinus ell L H) (fun _ => -K)
      (fun p => -w p) := by
  intro p hp phi hphi ht
  have hTouch : touchAbove (fun q => -phi q) w p := by
    refine ⟨by have hh := ht.1; dsimp only at hh ⊢; linarith,?_⟩
    filter_upwards [ht.2] with q hq
    change phi q ≤ -w q at hq
    change w q ≤ -phi q
    linarith
  have hRes := hw p hp (fun q => -phi q) hphi.neg hTouch
  have hTime : timeD univ (fun q => -phi q) p= -timeD univ phi p := by
    simpa only [neg_one_mul] using harnack_timeD_const_mul hphi (-1)
  have hHess : hessian (fun q => -phi q) p= -hessian phi p := by
    simpa only [neg_one_mul,neg_one_smul] using harnack_hessian_const_mul hphi (-1)
  rw [hTime,hHess] at hRes
  change -K ≤ timeD univ phi p-(-pucciPlus ell L (-hessian phi p))
  linarith only [hRes]

theorem perturb_deficit_super {n : ℕ} {Q : Set (Point n)} {ell L K : ℝ}
    {w : Point n → ℝ}
    (hw : viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => K) w) (M : ℝ) :
    viscositySuper Q (fun H _ => harnackPucciMinus ell L H) (fun _ => -K)
      (fun p => M-w p) := by
  convert viscositySuper_add_const (perturb_sub_neg_super hw) M using 1
  funext p
  ring

theorem perturb_quarter_subset_later {n : ℕ} :
    perturbClosed (0 : Space n) (1/4) 0 ⊆
      closedBall (0 : Space n) (1/4) ×ˢ Icc (-1/4 : ℝ) 0 := by
  intro p hp
  refine ⟨hp.1,?_,hp.2.2⟩
  have ht : 0-(1/4 : ℝ)^2 ≤ p.2 := hp.2.1
  linarith

theorem perturb_quarter_subset_unit {n : ℕ} :
    perturbClosed (0 : Space n) (1/4) 0 ⊆ unitClosed n := by
  intro p hp
  exact perturb_qplus_closure_subset (by
    rw [perturb_qplus_closure]
    exact perturb_quarter_subset_later hp)

theorem perturb_unit_range_contraction {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ theta : ℝ, 1/2 ≤ theta ∧ theta < 1 ∧
      ∀ K : ℝ, 0 ≤ K → ∀ w : Point n → ℝ, ContinuousOn w (unitClosed n) →
      ∀ m M : ℝ, (∀ z∈unitClosed n, m ≤ w z ∧ w z ≤ M) →
      viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) (fun _ => K) w →
      viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H) (fun _ => -K) w →
      ∃ m' M' : ℝ, m ≤ m' ∧ M' ≤ M ∧
        (∀ z∈perturbClosed (0 : Space n) (1/4) 0, m' ≤ w z ∧ w z ≤ M') ∧
        M'-m' ≤ theta*(M-m)+K := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := perturb_forced_weak_harnack_closed hn hell hL
  let c := (1/2 : ℝ)^(1/p)
  let a := min (1/2 : ℝ) (c/C)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have ha : 0 < a := lt_min (by norm_num) (div_pos hc hC)
  have ha2 : a ≤ 1/2 := min_le_left _ _
  have hCa : C*a ≤ c := by
    have hh := (le_div_iff₀ hC).mp (min_le_right (1/2 : ℝ) (c/C))
    simpa only [mul_comm] using hh
  refine ⟨1-a,by linarith,by linarith,?_⟩
  intro K hK w hw m M hRange hSub hSuper
  have hZero : (0 : Point n)∈unitClosed n := by simp [unitClosed,Yau.Parabolic.cylinder]
  have hD : 0 ≤ M-m := by have hh := hRange 0 hZero; linarith
  have hHi : ContinuousOn (fun z => M-w z) (unitClosed n) := continuousOn_const.sub hw
  have hLo : ContinuousOn (fun z => w z-m) (unitClosed n) := hw.sub continuousOn_const
  have hHi0 : ∀ z∈unitClosed n, 0 ≤ M-w z := fun z hz => sub_nonneg.mpr (hRange z hz).2
  have hLo0 : ∀ z∈unitClosed n, 0 ≤ w z-m := fun z hz => sub_nonneg.mpr (hRange z hz).1
  have hLowSuper : viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H)
      (fun _ => -K) (fun z => w z-m) := by
    simpa only [sub_eq_add_neg] using viscositySuper_add_const hSuper (-m)
  have hChoice := perturb_two_early_means hp hp1.le hD hHi hLo hHi0 hLo0
    (fun z _ => by ring)
  rcases hChoice with hChoice | hChoice
  · have hBound := hWH K hK (fun z => M-w z) hHi hHi0 (perturb_deficit_super hSub M)
    have hMove (z : Point n) (hz : z∈perturbClosed (0 : Space n) (1/4) 0) :
        a*(M-m) ≤ M-w z+K := by
      have hh := hChoice.trans (hBound z (perturb_quarter_subset_later hz))
      have hcD := mul_le_mul_of_nonneg_right hCa hD
      apply (mul_le_mul_iff_right₀ hC).mp
      dsimp only [c] at hCa hcD
      nlinarith only [hh,hcD]
    refine ⟨m,min M (M-a*(M-m)+K),le_rfl,min_le_left _ _,?_,?_⟩
    · intro z hz
      exact ⟨(hRange z (perturb_quarter_subset_unit hz)).1,
        le_min (hRange z (perturb_quarter_subset_unit hz)).2 (by linarith [hMove z hz])⟩
    · have hh := min_le_right M (M-a*(M-m)+K)
      nlinarith only [hh]
  · have hBound := hWH K hK (fun z => w z-m) hLo hLo0 hLowSuper
    have hMove (z : Point n) (hz : z∈perturbClosed (0 : Space n) (1/4) 0) :
        a*(M-m) ≤ w z-m+K := by
      have hh := hChoice.trans (hBound z (perturb_quarter_subset_later hz))
      have hcD := mul_le_mul_of_nonneg_right hCa hD
      apply (mul_le_mul_iff_right₀ hC).mp
      dsimp only [c] at hCa hcD
      nlinarith only [hh,hcD]
    refine ⟨max m (m+a*(M-m)-K),M,le_max_left _ _,le_rfl,?_,?_⟩
    · intro z hz
      exact ⟨max_le (hRange z (perturb_quarter_subset_unit hz)).1 (by linarith [hMove z hz]),
        (hRange z (perturb_quarter_subset_unit hz)).2⟩
    · have hh := le_max_right m (m+a*(M-m)-K)
      nlinarith only [hh]

end Yau.LeafProofs.L05Aux
