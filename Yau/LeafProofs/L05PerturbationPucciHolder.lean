import Yau.LeafProofs.L05PerturbationHolderGeometry

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_half_buffer_open {n : ℕ} {z : Point n}
    (hz : z∈perturbClosed (0 : Space n) (1/2) 0) :
    perturbOpen z.1 (1/4) z.2 ⊆ unitOpen n := by
  intro p hp
  have hpc : p∈perturbClosed z.1 (1/4) z.2 :=
    ⟨ball_subset_closedBall hp.1,hp.2.1.le,hp.2.2.le⟩
  have hb := perturb_half_buffer hz hpc
  exact ⟨hb.1,by simpa only [one_pow,neg_mul,one_mul] using hb.2.1,
    hp.2.2.trans_le hz.2.2⟩

theorem perturb_forced_pucci_holder {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa < 1 ∧
      ∀ w : Point n → ℝ, ContinuousOn w (backward 1) →
      (∀ p∈backward 1, |w p| ≤ 1) →
      viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) (fun _ => 2) w →
      viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H) (fun _ => -2) w →
      HolderBound kappa (perturbClosed (0 : Space n) (1/2) 0) w 100 := by
  obtain ⟨kappa,hk0,hkhalf,hDecay⟩ := perturb_oscillation_decay hn hell hL
  have hk1 : kappa ≤ 1 := by linarith
  refine ⟨kappa,hk0,by linarith,?_⟩
  intro w hw hBound hSub hSuper
  have hLocal (z : Point n) (hz : z∈perturbClosed (0 : Space n) (1/2) 0)
      (r : ℝ) (hr : 0 < r) (hrR : r ≤ 1/4) :
      perturbOscillation z.1 r z.2 w ≤ (16*r)^kappa*(19/8 : ℝ) := by
    have hBuf := perturb_half_buffer hz
    have hOpen := perturb_half_buffer_open hz
    have hCont := hw.mono hBuf
    have hs : viscositySub (perturbOpen z.1 (1/4) z.2)
        (fun H _ => pucciPlus ell L H) (fun _ => 2) w := by
      intro p hp
      exact hSub p (hOpen hp)
    have hsp : viscositySuper (perturbOpen z.1 (1/4) z.2)
        (fun H _ => harnackPucciMinus ell L H) (fun _ => -2) w := by
      intro p hp
      exact hSuper p (hOpen hp)
    have hOsc : perturbOscillation z.1 (1/4) z.2 w ≤ 2 := by
      have hh := perturb_oscillation_le_range z.1 (R := 1/4) (T := z.2) (w := w)
        (m := -1) (M := 1) (by norm_num) (fun p hp => abs_le.mp (hBound p (hBuf hp)))
      norm_num at hh ⊢
      exact hh
    have hDec := hDecay z.1 (1/4) z.2 2 (by norm_num) (by norm_num) w hCont hs hsp r hr hrR
    rw [show 4*r/(1/4 : ℝ)=16*r from by ring] at hDec
    exact hDec.trans (mul_le_mul_of_nonneg_left (by linarith only [hOsc])
      (Real.rpow_nonneg (by positivity : 0 ≤ 16*r) kappa))
  refine ⟨by norm_num,?_,?_⟩
  · intro p hp
    rw [Real.norm_eq_abs]
    exact (hBound p (perturb_half_subset_back hp)).trans (by norm_num)
  intro p hp q hq
  rw [Real.norm_eq_abs]
  let d := parabolicDistance p q
  have hd0 : 0 ≤ d := perturb_distance_nonneg p q
  have hWeight : d^kappa ≤ holderWeight kappa p q :=
    perturb_distance_rpow_le_weight hk0.le hk1 p q
  have hAbs : |w p-w q| ≤ 2 := (abs_sub _ _).trans (by
    have hpB := hBound p (perturb_half_subset_back hp)
    have hqB := hBound q (perturb_half_subset_back hq)
    linarith)
  by_cases hd : d=0
  · have hpq : p=q := perturb_distance_zero hd
    subst q
    simp only [sub_self,abs_zero]
    exact mul_nonneg (by norm_num) (by
      dsimp only [holderWeight]
      positivity)
  have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
  by_cases hSmall : d ≤ 1/32
  · let z : Point n := (p.1,max p.2 q.2)
    have hz : z∈perturbClosed (0 : Space n) (1/2) 0 := perturb_half_pair_top hp hq
    have hr : 0 < 2*d := by positivity
    have hrR : 2*d ≤ 1/4 := by linarith only [hSmall]
    have hPair := perturb_pair_mem_closed p q
    have hCont : ContinuousOn w (perturbClosed p.1 (2*d) (max p.2 q.2)) :=
      hw.mono ((perturb_closed_subset_radius p.1 hr.le hrR (max p.2 q.2)).trans
        (perturb_half_buffer hz))
    have hOsc := perturb_oscillation_abs_sub p.1 hr.le hCont hPair.1 hPair.2
    have hDec := hLocal z hz (2*d) hr hrR
    have hPow32 : (32 : ℝ)^kappa ≤ 32 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 32) hk1
    have hConst : (32*d)^kappa*(19/8 : ℝ) ≤ 100*d^kappa := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) hd0]
      have hh := mul_le_mul_of_nonneg_right hPow32 (Real.rpow_nonneg hd0 kappa)
      have hN := Real.rpow_nonneg hd0 kappa
      nlinarith only [hh,hN]
    have hDec' : perturbOscillation p.1 (2*d) (max p.2 q.2) w ≤
        (32*d)^kappa*(19/8 : ℝ) := by
      simpa only [show 16*(2*d)=32*d from by ring] using hDec
    exact hOsc.trans (hDec'.trans (hConst.trans (mul_le_mul_of_nonneg_left hWeight (by norm_num))))
  · have hFloor : (1/32 : ℝ) ≤ (1/32 : ℝ)^kappa := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0 : ℝ) < 1/32) (by norm_num : (1/32 : ℝ) ≤ 1) hk1
    have hDpow : (1/32 : ℝ) ≤ d^kappa := hFloor.trans
      (Real.rpow_le_rpow (by norm_num) (le_of_lt (lt_of_not_ge hSmall)) hk0.le)
    nlinarith only [hAbs,hDpow,hWeight]

end Yau.LeafProofs.L05Aux
