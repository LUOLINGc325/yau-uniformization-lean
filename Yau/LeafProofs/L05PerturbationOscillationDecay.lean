import Yau.LeafProofs.L05PerturbationOscillation

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_oscillation_decay {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa ≤ 1/2 ∧
      ∀ c : Space n, ∀ R T K : ℝ, 0 < R → 0 ≤ K →
      ∀ w : Point n → ℝ, ContinuousOn w (perturbClosed c R T) →
      viscositySub (perturbOpen c R T) (fun H _ => pucciPlus ell L H) (fun _ => K) w →
      viscositySuper (perturbOpen c R T) (fun H _ => harnackPucciMinus ell L H) (fun _ => -K) w →
      ∀ r : ℝ, 0 < r → r ≤ R →
        perturbOscillation c r T w ≤ (4*r/R)^kappa*(perturbOscillation c R T w+3*K*R^2) := by
  obtain ⟨theta,ht0,ht1,hQuarter⟩ := perturb_oscillation_quarter hn hell hL
  have htpos : 0 < theta := by linarith
  let kappa := harnackMomentExponent theta 4
  have hk := harnack_momentExponent_bounds htpos ht1 (by norm_num : (1 : ℝ) < 4)
  have hk0 : 0 < kappa := hk.1
  have hkhalf : kappa ≤ 1/2 := min_le_left _ _
  have htq : theta ≤ (1/4 : ℝ)^kappa := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 4),
      Real.one_rpow]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) kappa)).mpr
    exact hk.2.2.le
  refine ⟨kappa,hk0,hkhalf,?_⟩
  intro c R T K hR hK w hw hSub hSuper r hr hrR
  let rad := fun j : ℕ => R*(1/4 : ℝ)^j
  have hRad (j : ℕ) : 0 < rad j := mul_pos hR (by positivity)
  have hRadR (j : ℕ) : rad j ≤ R := by
    have hh := pow_le_one₀ (n := j) (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (1/4 : ℝ) ≤ 1)
    exact (mul_le_mul_of_nonneg_left hh hR.le).trans_eq (mul_one R)
  have hRadSucc (j : ℕ) : rad (j+1)=rad j/4 := by dsimp only [rad]; rw [pow_succ]; ring
  have hPow (j : ℕ) : ((1/4 : ℝ)^j)^2=(1/16 : ℝ)^j := by
    calc
      _ = (1/4 : ℝ)^j*(1/4 : ℝ)^j := pow_two _
      _ = ((1/4 : ℝ)*(1/4 : ℝ))^j := (mul_pow _ _ _).symm
      _ = _ := by norm_num
  have hStep (j : ℕ) : perturbOscillation c (rad (j+1)) T w ≤
      theta*perturbOscillation c (rad j) T w+(K*R^2)*(1/16 : ℝ)^j := by
    have hSet := perturb_closed_subset_radius c (hRad j).le (hRadR j) T
    have hOSet := perturb_open_subset_radius c (hRad j).le (hRadR j) T
    have hs : viscositySub (perturbOpen c (rad j) T)
        (fun H _ => pucciPlus ell L H) (fun _ => K) w := by
      intro p hp
      exact hSub p (hOSet hp)
    have hsp : viscositySuper (perturbOpen c (rad j) T)
        (fun H _ => harnackPucciMinus ell L H) (fun _ => -K) w := by
      intro p hp
      exact hSuper p (hOSet hp)
    have hh := hQuarter c (rad j) T K (hRad j) hK w (hw.mono hSet) hs hsp
    rw [← hRadSucc] at hh
    have hForce : K*(rad j)^2=(K*R^2)*(1/16 : ℝ)^j := by
      dsimp only [rad]
      rw [mul_pow,hPow]
      ring
    rwa [hForce] at hh
  have hDyadic (j : ℕ) : perturbOscillation c (rad j) T w ≤
      theta^j*(perturbOscillation c R T w+3*K*R^2) := by
    have hh := perturb_oscillation_sequence ht0 (mul_nonneg hK (sq_nonneg R))
      (fun j => perturbOscillation c (rad j) T w) hStep j
    simpa only [rad,pow_zero,mul_one,mul_assoc] using hh
  obtain ⟨j,hLower,hUpper⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) < 1)
  have hrRad : r ≤ rad j := by
    have hh := (div_le_iff₀ hR).mp hUpper
    simpa only [rad,mul_comm] using hh
  have hRadSmall : (1/4 : ℝ)^j ≤ 4*r/R := by
    rw [pow_succ] at hLower
    calc
      (1/4 : ℝ)^j ≤ 4*(r/R) := by nlinarith only [hLower]
      _ = 4*r/R := by ring
  have hPower : theta^j ≤ (4*r/R)^kappa := by
    calc
      theta^j ≤ ((1/4 : ℝ)^kappa)^j := pow_le_pow_left₀ htpos.le htq j
      _ = ((1/4 : ℝ)^j)^kappa := Real.rpow_pow_comm (by norm_num) _ _
      _ ≤ (4*r/R)^kappa := Real.rpow_le_rpow (by positivity) hRadSmall hk0.le
  have hCoef : 0 ≤ perturbOscillation c R T w+3*K*R^2 :=
    add_nonneg (perturb_oscillation_nonneg c hR.le hw) (by positivity)
  exact (perturb_oscillation_mono c hr.le hrRad
    (hw.mono (perturb_closed_subset_radius c (hRad j).le (hRadR j) T))).trans
      ((hDyadic j).trans (mul_le_mul_of_nonneg_right hPower hCoef))

end Yau.LeafProofs.L05Aux
