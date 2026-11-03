import Yau.LeafProofs.L05ChuCutoffModulus

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

set_option maxHeartbeats 1600000 in
theorem chu_weighted_residual_pair {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b x y epsilon A C MR MH CB w : ℝ} {H J K L B D : V}
    (heps : 0 ≤ epsilon) (hA : 0 ≤ A) (hC : 0 ≤ C) (hMR : 0 ≤ MR) (hMH : 0 ≤ MH)
    (hw : 0 ≤ w) (ha : |a| ≤ 1) (hab : |a-b| ≤ C*w) (hy : |y| ≤ MR) (hJ : ‖J‖ ≤ MH)
    (hB : ‖B-D‖ ≤ CB*w) (hK : K=a • H+B) (hL : L=b • J+D)
    (hR : |x-y| ≤ epsilon*‖H-J‖+A*w) :
    |a*x-b*y| ≤ epsilon*‖K-L‖+(A+C*MR+epsilon*(CB+C*MH))*w := by
  have he : a*x-b*y=a*(x-y)+(a-b)*y := by ring
  have htri := abs_add_le (a*(x-y)) ((a-b)*y)
  rw [← he,abs_mul,abs_mul] at htri
  have hmain0 := mul_le_mul_of_nonneg_left hR (abs_nonneg a)
  have hAw := mul_le_mul_of_nonneg_right ha (mul_nonneg hA hw)
  have hmain : |a| * |x-y| ≤ epsilon*‖a • (H-J)‖+A*w := by
    rw [norm_smul,Real.norm_eq_abs]
    nlinarith only [hmain0,hAw]
  have hlow := mul_le_mul hab hy (abs_nonneg y) (mul_nonneg hC hw)
  have hi : a • (H-J)=(K-L)-(B-D)-(a-b) • J := by
    rw [hK,hL,smul_sub,sub_smul]
    abel
  have hn : ‖a • (H-J)‖ ≤ ‖K-L‖+‖B-D‖+|a-b| * ‖J‖ := by
    rw [hi]
    have hh := (norm_sub_le ((K-L)-(B-D)) ((a-b) • J)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    simpa only [norm_smul,Real.norm_eq_abs] using hh
  have hH := mul_le_mul hab hJ (norm_nonneg _) (mul_nonneg hC hw)
  have hLift : ‖a • (H-J)‖ ≤ ‖K-L‖+(CB+C*MH)*w := by
    nlinarith only [hn,hB,hH]
  have hLiftScaled := mul_le_mul_of_nonneg_left hLift heps
  nlinarith only [htri,hmain,hlow,hLiftScaled]

set_option maxHeartbeats 1800000 in
theorem chu_weighted_cutoff_pair {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P Q : Set (Point n)} {R chi : Point n → ℝ} {H J B : Point n → V}
    {gamma epsilon A C MR MH CB : ℝ}
    (heps : 0 ≤ epsilon) (hA : 0 ≤ A) (hMR : 0 ≤ MR) (hMH : 0 ≤ MH)
    (hchi : HolderBound gamma P chi C) (hunit : ∀ p ∈ P, |chi p| ≤ 1)
    (hzero : ∀ p ∈ P, p ∉ Q → chi p=0)
    (hR : ∀ p ∈ Q, |R p| ≤ MR) (hH : ∀ p ∈ Q, ‖H p‖ ≤ MH)
    (hB : HolderBound gamma P B CB) (hId : ∀ p ∈ P, J p=chi p • H p+B p)
    (hpair : ∀ p ∈ Q, ∀ q ∈ Q, |R p-R q| ≤ epsilon*‖H p-H q‖+A*holderWeight gamma p q)
    {p q : Point n} (hp : p ∈ P) (hq : q ∈ P) :
    |chi p*R p-chi q*R q| ≤ epsilon*‖J p-J q‖+
      (A+C*MR+epsilon*(CB+C*MH))*holderWeight gamma p q := by
  have hW : 0 ≤ holderWeight gamma p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hvar : |chi p-chi q| ≤ C*holderWeight gamma p q := by
    simpa only [Real.norm_eq_abs] using hchi.2.2 p hp q hq
  have hExtra : 0 ≤ epsilon*‖J p-J q‖+A*holderWeight gamma p q+
      epsilon*(CB+C*MH)*holderWeight gamma p q := by
    exact add_nonneg (add_nonneg (mul_nonneg heps (norm_nonneg _)) (mul_nonneg hA hW))
      (mul_nonneg (mul_nonneg heps (add_nonneg hB.1 (mul_nonneg hchi.1 hMH))) hW)
  by_cases hpQ : p ∈ Q
  · by_cases hqQ : q ∈ Q
    · exact chu_weighted_residual_pair heps hA hchi.1 hMR hMH hW (hunit p hp) hvar
        (hR q hqQ) (hH q hqQ) (hB.2.2 p hp q hq) (hId p hp) (hId q hq) (hpair p hpQ q hqQ)
    · have he : chi p*R p-chi q*R q=(chi p-chi q)*R p := by rw [hzero q hq hqQ]; ring
      rw [he,abs_mul]
      have hh := mul_le_mul hvar (hR p hpQ) (abs_nonneg _) (mul_nonneg hchi.1 hW)
      nlinarith only [hh,hExtra]
  · by_cases hqQ : q ∈ Q
    · have he : chi p*R p-chi q*R q=(chi p-chi q)*R q := by rw [hzero p hp hpQ]; ring
      rw [he,abs_mul]
      have hh := mul_le_mul hvar (hR q hqQ) (abs_nonneg _) (mul_nonneg hchi.1 hW)
      nlinarith only [hh,hExtra]
    · rw [hzero p hp hpQ,hzero q hq hqQ,zero_mul,zero_mul,sub_self,abs_zero]
      nlinarith only [hExtra,mul_nonneg (mul_nonneg hchi.1 hMR) hW]

theorem chu_weighted_cutoff_oscillation {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P Q : Set (Point n)} {R chi : Point n → ℝ} {H J B : Point n → V}
    {gamma epsilon A C MR MH CB N r : ℝ}
    (heps : 0 ≤ epsilon) (hA : 0 ≤ A) (hMR : 0 ≤ MR) (hMH : 0 ≤ MH)
    (hN : 0 ≤ N) (hr : 0 ≤ r) (hg : 0 ≤ gamma)
    (hchi : HolderBound gamma P chi C) (hunit : ∀ p ∈ P, |chi p| ≤ 1)
    (hzero : ∀ p ∈ P, p ∉ Q → chi p=0)
    (hR : ∀ p ∈ Q, |R p| ≤ MR) (hH : ∀ p ∈ Q, ‖H p‖ ≤ MH)
    (hB : HolderBound gamma P B CB) (hId : ∀ p ∈ P, J p=chi p • H p+B p)
    (hJ : ∀ p ∈ P, ‖J p‖ ≤ N)
    (hpair : ∀ p ∈ Q, ∀ q ∈ Q, |R p-R q| ≤ epsilon*‖H p-H q‖+A*holderWeight gamma p q) :
    chuOscillation P (fun p => chi p*R p) r ≤ epsilon*chuOscillation P J r+
      (2*(A+C*MR+epsilon*(CB+C*MH)))*r^gamma := by
  have hCoeff : 0 ≤ 2*(A+C*MR+epsilon*(CB+C*MH)) := by
    exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (add_nonneg (add_nonneg hA (mul_nonneg hchi.1 hMR))
      (mul_nonneg heps (add_nonneg hB.1 (mul_nonneg hchi.1 hMH))))
  apply chuOscillation_perturbation heps hCoeff hN hr hJ
  intro p hp q hq hpq
  have hh := chu_weighted_cutoff_pair heps hA hMR hMH hchi hunit hzero hR hH hB hId hpair hp hq
  have hw := mul_le_mul_of_nonneg_left (holderWeight_le_twice_radius_power hg hpq) (by linarith only [hCoeff] : 0 ≤ A+C*MR+epsilon*(CB+C*MH))
  rw [Real.norm_eq_abs]
  nlinarith only [hh,hw]

end Yau.LeafProofs.L05Aux
