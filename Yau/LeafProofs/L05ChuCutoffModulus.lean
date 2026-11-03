import Yau.LeafProofs.L05ChuOscillation

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

set_option maxHeartbeats 1600000 in
theorem chu_cutoff_residual_pair {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    {P Q : Set (Point n)} {R : Point n → V} {J : Point n → W} {chi : Point n → ℝ}
    {gamma epsilon A M C : ℝ} (heps : 0 ≤ epsilon) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hchi : HolderBound gamma P chi C) (hunit : ∀ p ∈ P, |chi p| ≤ 1)
    (hzero : ∀ p ∈ P, p ∉ Q → chi p=0) (hR : ∀ p ∈ Q, ‖R p‖ ≤ M)
    (hpair : ∀ p ∈ Q, ∀ q ∈ Q, ‖R p-R q‖ ≤ epsilon*‖J p-J q‖+A*holderWeight gamma p q)
    {p q : Point n} (hp : p ∈ P) (hq : q ∈ P) :
    ‖chi p • R p-chi q • R q‖ ≤
      epsilon*‖J p-J q‖+(A+C*M)*holderWeight gamma p q := by
  have hW : 0 ≤ holderWeight gamma p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hvar : |chi p-chi q| ≤ C*holderWeight gamma p q := by
    simpa only [Real.norm_eq_abs] using hchi.2.2 p hp q hq
  have herror : 0 ≤ epsilon*‖J p-J q‖+A*holderWeight gamma p q := by positivity
  by_cases hpQ : p ∈ Q
  · by_cases hqQ : q ∈ Q
    · have he : chi p • R p-chi q • R q=chi p • (R p-R q)+(chi p-chi q) • R q := by
        rw [smul_sub,sub_smul]
        abel
      have hn := norm_add_le (chi p • (R p-R q)) ((chi p-chi q) • R q)
      rw [← he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs] at hn
      have hmain := mul_le_mul (hunit p hp) (hpair p hpQ q hqQ) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      have hcut := mul_le_mul hvar (hR q hqQ) (norm_nonneg _) (mul_nonneg hchi.1 hW)
      nlinarith only [hn,hmain,hcut]
    · have he : chi p • R p-chi q • R q=(chi p-chi q) • R p := by
        rw [hzero q hq hqQ]
        simp
      rw [he,norm_smul,Real.norm_eq_abs]
      have hh := mul_le_mul hvar (hR p hpQ) (norm_nonneg _) (mul_nonneg hchi.1 hW)
      nlinarith only [hh,herror]
  · by_cases hqQ : q ∈ Q
    · have he : chi p • R p-chi q • R q=(chi p-chi q) • R q := by
        rw [hzero p hp hpQ]
        simp
      rw [he,norm_smul,Real.norm_eq_abs]
      have hh := mul_le_mul hvar (hR q hqQ) (norm_nonneg _) (mul_nonneg hchi.1 hW)
      nlinarith only [hh,herror]
    · rw [hzero p hp hpQ,hzero q hq hqQ,zero_smul,zero_smul,sub_self,norm_zero]
      nlinarith only [herror,mul_nonneg (mul_nonneg hchi.1 hM) hW]

theorem chu_cutoff_residual_oscillation {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    {P Q : Set (Point n)} {R : Point n → V} {J : Point n → W} {chi : Point n → ℝ}
    {gamma epsilon A M C N r : ℝ} (heps : 0 ≤ epsilon) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hN : 0 ≤ N) (hr : 0 ≤ r) (hg : 0 ≤ gamma)
    (hchi : HolderBound gamma P chi C) (hunit : ∀ p ∈ P, |chi p| ≤ 1)
    (hzero : ∀ p ∈ P, p ∉ Q → chi p=0) (hR : ∀ p ∈ Q, ‖R p‖ ≤ M)
    (hJ : ∀ p ∈ P, ‖J p‖ ≤ N)
    (hpair : ∀ p ∈ Q, ∀ q ∈ Q, ‖R p-R q‖ ≤ epsilon*‖J p-J q‖+A*holderWeight gamma p q) :
    chuOscillation P (fun p => chi p • R p) r ≤
      epsilon*chuOscillation P J r+2*(A+C*M)*r^gamma := by
  apply chuOscillation_perturbation heps
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (add_nonneg hA (mul_nonneg hchi.1 hM))) hN hr hJ
  intro p hp q hq hpq
  have hh := chu_cutoff_residual_pair heps hA hM hchi hunit hzero hR hpair hp hq
  have hw := mul_le_mul_of_nonneg_left (holderWeight_le_twice_radius_power hg hpq)
    (add_nonneg hA (mul_nonneg hchi.1 hM))
  nlinarith only [hh,hw]

end Yau.LeafProofs.L05Aux
