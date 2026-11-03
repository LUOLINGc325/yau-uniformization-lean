import Yau.LeafProofs.L05PerturbationPowers

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_power_below_shape_max {S Smax nu : ℝ} (hS : 0 ≤ S) (hSS : S ≤ Smax)
    (hMax : 1 ≤ Smax) (hn0 : 0 ≤ nu) (hn1 : nu ≤ 1) : S^nu ≤ Smax := by
  by_cases hSmall : S ≤ 1
  · exact (Real.rpow_le_one hS hSmall hn0).trans hMax
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hSmall) hn1).trans hSS

theorem perturb_shape_weight {n : ℕ} {kappa S Smax : ℝ} (hk0 : 0 < kappa)
    (hk1 : kappa < 1) (hS0 : 0 ≤ S) (hSS : S ≤ Smax) (hMax : 1 ≤ Smax)
    (p q : Point n) (hSpace : ‖p.1-q.1‖^2 ≤ 2*S) (hTime : |p.2-q.2|^2 ≤ S) :
    holderWeight kappa p q ≤ (2+2*Smax)*S^(kappa/4) := by
  let nu := kappa/4
  have hn0 : 0 < nu := by dsimp only [nu]; positivity
  have hn1 : nu ≤ 1 := by dsimp only [nu]; linarith
  have hHalf : 0 ≤ kappa/2 := by positivity
  by_cases hSz : S=0
  · have hx : ‖p.1-q.1‖=0 := by
      rw [hSz,mul_zero] at hSpace
      nlinarith only [hSpace,norm_nonneg (p.1-q.1)]
    have ht : |p.2-q.2|=0 := by
      rw [hSz] at hTime
      nlinarith only [hTime,abs_nonneg (p.2-q.2)]
    simp only [holderWeight,hx,ht,hSz,Real.zero_rpow hk0.ne',
      Real.zero_rpow (show kappa/2≠0 by positivity),
      Real.zero_rpow (show kappa/4≠0 by positivity),zero_add,mul_zero,le_refl]
  have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSz)
  have hSn := Real.rpow_nonneg hS0 nu
  have hSnMax : S^nu ≤ Smax := perturb_power_below_shape_max hS0 hSS hMax hn0.le hn1
  have hSExp : S^(kappa/2)=S^nu*S^nu := by
    rw [← Real.rpow_add hSp]
    congr 1
    dsimp only [nu]
    ring
  have hNormPow : (‖p.1-q.1‖^2)^(kappa/2)=‖p.1-q.1‖^kappa := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _) 2]
    congr 1
    norm_num
    ring
  have hNorm := Real.rpow_le_rpow (sq_nonneg ‖p.1-q.1‖) hSpace hHalf
  rw [hNormPow,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hS0,hSExp] at hNorm
  have hTwo : (2 : ℝ)^(kappa/2) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (show kappa/2 ≤ 1 by linarith)
  have hNormB : ‖p.1-q.1‖^kappa ≤ 2*Smax*S^nu := by
    have h1 := mul_le_mul_of_nonneg_right hTwo (mul_nonneg hSn hSn)
    have h2 := mul_le_mul_of_nonneg_right hSnMax hSn
    nlinarith only [hNorm,h1,h2]
  have hTimePow : (|p.2-q.2|^2)^nu=|p.2-q.2|^(kappa/2) := by
    rw [← Real.rpow_natCast_mul (abs_nonneg _) 2]
    congr 1
    dsimp only [nu]
    norm_num
    ring
  have hTimeB := Real.rpow_le_rpow (sq_nonneg |p.2-q.2|) hTime hn0.le
  rw [hTimePow] at hTimeB
  change ‖p.1-q.1‖^kappa+|p.2-q.2|^(kappa/2) ≤ (2+2*Smax)*S^nu
  nlinarith only [hNormB,hTimeB,hSn]

end Yau.LeafProofs.L05Aux
