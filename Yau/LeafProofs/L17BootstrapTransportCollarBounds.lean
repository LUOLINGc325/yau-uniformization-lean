import Yau.LeafProofs.L17LocalizedSchauderLocalData

open Set Metric
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux
variable {n : ℕ} {T : ℝ} {F : Type*} [NormedAddCommGroup F]

theorem collar_far_scaledDistance_ge_half {rho : ℝ} (hrho : 0 < rho)
    (q r : ComplexVector n × Time T)
    (hq : q.1 ∉ ball (0 : ComplexVector n) rho)
    (hr : r.1 ∈ ball (0 : ComplexVector n) (rho/4)) :
    (1 : ℝ)/2 ≤ localScaledDistance rho q r := by
  have hqn : rho ≤ ‖q.1‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hq
  have hrn : ‖r.1‖ < rho/4 := by simpa only [mem_ball,dist_zero_right] using hr
  have htri : ‖q.1‖ ≤ ‖q.1-r.1‖+‖r.1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (q.1-r.1) r.1
  apply (le_div_iff₀ hrho).mpr
  linarith [Real.sqrt_nonneg |(q.2 : ℝ)-(r.2 : ℝ)|]

theorem half_le_rpow_of_half_le {d gamma : ℝ} (hd : (1 : ℝ)/2 ≤ d)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) : (1 : ℝ)/2 ≤ d^gamma := by
  by_cases hd1 : d ≤ 1
  · exact hd.trans (Real.self_le_rpow_of_le_one (by linarith) hd1 hgamma1)
  · exact (by norm_num : (1 : ℝ)/2 ≤ 1).trans
      (Real.one_le_rpow (lt_of_not_ge hd1).le hgamma0)

theorem localScaledDistance_comm (rho : ℝ) (q r : ComplexVector n × Time T) :
    localScaledDistance rho q r=localScaledDistance rho r q := by
  simp only [localScaledDistance,norm_sub_rev,abs_sub_comm]

theorem zero_collar_sup_bound {rho A : ℝ} (hrho : 0 < rho) (hA : 0 ≤ A)
    (f : ComplexVector n × Time T → F)
    (hZero : ∀ q, q.1 ∉ ball (0 : ComplexVector n) (rho/4) → f q=0)
    (hSup : ∀ q, q.1 ∈ ball (0 : ComplexVector n) rho → ‖f q‖ ≤ A)
    (q : ComplexVector n × Time T) : ‖f q‖ ≤ A := by
  by_cases hq : q.1 ∈ ball (0 : ComplexVector n) rho
  · exact hSup q hq
  · rw [hZero q (fun h => hq (ball_subset_ball (by linarith) h)),norm_zero]
    exact hA

theorem zero_collar_far_difference_bound {rho A gamma : ℝ} (hrho : 0 < rho)
    (hA : 0 ≤ A) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (f : ComplexVector n × Time T → F)
    (hZero : ∀ q, q.1 ∉ ball (0 : ComplexVector n) (rho/4) → f q=0)
    (hSup : ∀ q, q.1 ∈ ball (0 : ComplexVector n) rho → ‖f q‖ ≤ A)
    (q r : ComplexVector n × Time T) (hq : q.1 ∉ ball (0 : ComplexVector n) rho) :
    ‖f q-f r‖ ≤ 2*A*(localScaledDistance rho q r)^gamma := by
  have hfq := hZero q (fun h => hq (ball_subset_ball (by linarith) h))
  rw [hfq,zero_sub,norm_neg]
  by_cases hr : r.1 ∈ ball (0 : ComplexVector n) (rho/4)
  · have hPow := half_le_rpow_of_half_le (collar_far_scaledDistance_ge_half hrho q r hq hr) hgamma0 hgamma1
    have hmul := mul_le_mul_of_nonneg_left hPow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
    exact (zero_collar_sup_bound hrho hA f hZero hSup r).trans (by nlinarith)
  · rw [hZero r hr,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hA) (Real.rpow_nonneg (by
      dsimp only [localScaledDistance]
      positivity) _)

theorem zero_collar_difference_bound {rho A gamma : ℝ} (hrho : 0 < rho)
    (hA : 0 ≤ A) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (f : ComplexVector n × Time T → F)
    (hZero : ∀ q, q.1 ∉ ball (0 : ComplexVector n) (rho/4) → f q=0)
    (hSup : ∀ q, q.1 ∈ ball (0 : ComplexVector n) rho → ‖f q‖ ≤ A)
    (hPair : ∀ q r, q.1 ∈ ball (0 : ComplexVector n) rho →
      r.1 ∈ ball (0 : ComplexVector n) rho →
      ‖f q-f r‖ ≤ A*(localScaledDistance rho q r)^gamma)
    (q r : ComplexVector n × Time T) :
    ‖f q-f r‖ ≤ 2*A*(localScaledDistance rho q r)^gamma := by
  by_cases hq : q.1 ∈ ball (0 : ComplexVector n) rho
  · by_cases hr : r.1 ∈ ball (0 : ComplexVector n) rho
    · exact (hPair q r hq hr).trans (by
        have hPow : 0 ≤ (localScaledDistance rho q r)^gamma :=
          Real.rpow_nonneg (by dsimp only [localScaledDistance]; positivity) _
        nlinarith [mul_nonneg hA hPow])
    · rw [norm_sub_rev,localScaledDistance_comm rho q r]
      exact zero_collar_far_difference_bound hrho hA hgamma0 hgamma1 f hZero hSup r q hr
  · exact zero_collar_far_difference_bound hrho hA hgamma0 hgamma1 f hZero hSup q r hq

end Yau.LeafProofs.L17BootstrapTransportAux
