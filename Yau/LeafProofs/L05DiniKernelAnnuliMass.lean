import Yau.LeafProofs.L05DiniKernelAnnuliGeometry

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem diniAnnulus_mass_le {n : ℕ} {kappa : Space n → ℝ} {Q R : ℝ}
    (hQ : 0 ≤ Q) (hR : 0 < R) (hk0 : ∀ y : Space n, 0 ≤ kappa y) (hk : Integrable kappa)
    (hk2 : Integrable (fun y : Space n => kappa y*‖y‖^2))
    (hm0 : (∫ y : Space n, kappa y) ≤ Q) (hm2 : (∫ y : Space n, kappa y*‖y‖^2) ≤ Q*R^2)
    (i : ℕ) : (∫ y in diniAnnulus R i, kappa y) ≤ 4*Q*(1/4:ℝ)^i := by
  cases i with
  | zero =>
    have hh := (setIntegral_le_integral hk (ae_of_all _ hk0) (s := diniAnnulus R 0)).trans hm0
    simp only [pow_zero,mul_one]
    nlinarith only [hh,hQ]
  | succ k =>
    let a := (2:ℝ)^k*R
    have ha : 0 < a := mul_pos (pow_pos (by norm_num) _) hR
    have hmono : (∫ y in diniAnnulus R (k+1), kappa y) ≤ ∫ y in {y : Space n | a < ‖y‖}, kappa y := by
      apply setIntegral_mono_set hk.integrableOn
      · exact ae_of_all _ hk0
      · exact Filter.Eventually.of_forall (fun y hy => hy.1)
    have htail := dini_kernel_tail_mass_bound ha hk0 hk hk2
    have hM := div_le_div_of_nonneg_right hm2 (sq_nonneg a)
    have hPow : ((2:ℝ)^k)^2=(4:ℝ)^k := by
      rw [← pow_mul,Nat.mul_comm k 2,pow_mul]
      norm_num
    have hQuarter : (1/4:ℝ)^k=((4:ℝ)^k)⁻¹ := by rw [one_div_pow,one_div]
    have heq : (Q*R^2)/a^2=4*Q*(1/4:ℝ)^(k+1) := by
      dsimp only [a]
      rw [mul_pow,hPow,pow_succ (1/4:ℝ) k,hQuarter]
      field_simp [hR.ne',pow_ne_zero k (by norm_num : (4:ℝ) ≠ 0)] <;> ring
    exact hmono.trans (htail.trans (hM.trans_eq heq))

theorem diniAnnulus_modulus_le {n : ℕ} {psi : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hzero : psi 0=0) (hmono : MonotoneOn psi (Set.Ioi (0:ℝ)))
    (hpsi0 : ∀ s : ℝ, 0 < s → 0 ≤ psi s) {i : ℕ} {y : Space n} (hy : y ∈ diniAnnulus R i) :
    psi ‖y‖ ≤ psi ((2:ℝ)^i*R) := by
  have hRi : 0 < (2:ℝ)^i*R := mul_pos (pow_pos (by norm_num) _) hR
  by_cases hy0 : ‖y‖=0
  · rw [hy0,hzero]
    exact hpsi0 _ hRi
  · have hn : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
    exact hmono hn hRi (diniAnnulus_upper hy)

theorem two_moments_dini_integral {n : ℕ} {kappa : Space n → ℝ} {psi : ℝ → ℝ}
    {eta B Q R : ℝ} (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hR : 0 < R)
    (hm : Measurable psi) (hzero : psi 0=0) (hmono : MonotoneOn psi (Set.Ioi (0:ℝ)))
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta)
    (hk0 : ∀ y : Space n, 0 ≤ kappa y) (hk : Integrable kappa)
    (hk2 : Integrable (fun y : Space n => kappa y*‖y‖^2))
    (hm0 : (∫ y : Space n, kappa y) ≤ Q) (hm2 : (∫ y : Space n, kappa y*‖y‖^2) ≤ Q*R^2) :
    Integrable (fun y : Space n => kappa y*psi ‖y‖) ∧
      (∫ y : Space n, kappa y*psi ‖y‖) ≤ 4*Q*diniDyadicAverage psi R := by
  have hi := dini_weighted_kernel_integrable he he1 hB hm hzero hpsi hk0 hk hk2
  have hbound (i : ℕ) : (∫ y in diniAnnulus R i, kappa y*psi ‖y‖) ≤
      (4*Q)*((1/4:ℝ)^i*psi ((2:ℝ)^i*R)) := by
    have hMass := diniAnnulus_mass_le hQ hR hk0 hk hk2 hm0 hm2 i
    have hpoint (y : Space n) (hy : y ∈ diniAnnulus R i) :
        kappa y*psi ‖y‖ ≤ kappa y*psi ((2:ℝ)^i*R) :=
      mul_le_mul_of_nonneg_left (diniAnnulus_modulus_le hR hzero hmono (fun s hs => (hpsi s hs).1) hy) (hk0 y)
    have hInt := setIntegral_mono_on hi.integrableOn
      (hk.mul_const (psi ((2:ℝ)^i*R))).integrableOn (diniAnnulus_measurable R i) hpoint
    rw [integral_mul_const] at hInt
    have hh := mul_le_mul_of_nonneg_right hMass
      (hpsi ((2:ℝ)^i*R) (mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) i) hR)).1
    exact hInt.trans (hh.trans_eq (by ring))
  have hSum := hasSum_integral_iUnion (diniAnnulus_measurable (n := n) R)
    (diniAnnulus_pairwise_disjoint (n := n) hR.le) hi.integrableOn
  have hEq := hSum.tsum_eq
  rw [diniAnnulus_iUnion hR,Measure.restrict_univ] at hEq
  have hSeries := (diniDyadicAverage_summable he he1 hB hR hpsi).1
  have hComp := hSum.summable.tsum_le_tsum hbound (hSeries.mul_left (4*Q))
  rw [hEq,tsum_mul_left] at hComp
  exact ⟨hi,hComp⟩

end Yau.LeafProofs.L05Aux
