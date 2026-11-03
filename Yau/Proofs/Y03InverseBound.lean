import Yau.Proofs.Y03Inverse

/-! A uniform polynomial bound for the actual inverse of every strict-weight triangular change. -/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem matOpNorm_one_le : matOpNorm (1 : Herm n) ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (1 : Herm n)‖ ≤ 1
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

theorem strict_weight_inverse_norm_le (L : Herm n) (w : Fin n → ℝ)
    (hdiag : ∀ i, L i i = 1) (hsupport : ∀ i j, i ≠ j → L i j ≠ 0 → w i < w j) :
    matOpNorm L⁻¹ ≤ ∑ r ∈ Finset.range n, (matOpNorm (L - 1)) ^ r := by
  change ‖L⁻¹‖ ≤ ∑ r ∈ Finset.range n, ‖L - 1‖ ^ r
  rw [strict_weight_inverse_polynomial L w hdiag hsupport]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  cases r with
  | zero =>
    simp only [pow_zero]
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    exact matOpNorm_one_le (n := n)
  | succ r => simpa only [norm_neg] using norm_pow_le' (-(L - 1)) (Nat.succ_pos r)

theorem strict_weight_change_polynomial_bound (L : Herm n) (w : Fin n → ℝ)
    (hdiag : ∀ i, L i i = 1) (hsupport : ∀ i j, i ≠ j → L i j ≠ 0 → w i < w j)
    {B : ℝ} (hB : 0 ≤ B) (hL : matOpNorm L ≤ B) :
    matOpNorm L + matOpNorm L⁻¹ ≤ (n + 1 : ℝ) * (B + 1) ^ (n + 1) := by
  have hinv := strict_weight_inverse_norm_le L w hdiag hsupport
  have hdiff : matOpNorm (L - 1) ≤ B + 1 := by
    exact (norm_sub_le L (1 : Herm n)).trans (add_le_add hL (matOpNorm_one_le (n := n)))
  have hbase : 1 ≤ B + 1 := by linarith
  have hpow (r : ℕ) (hr : r ∈ Finset.range n) : (matOpNorm (L - 1)) ^ r ≤ (B + 1) ^ (n + 1) := by
    exact (pow_le_pow_left₀ (norm_nonneg _) hdiff r).trans
      (pow_le_pow_right₀ hbase (by have := Finset.mem_range.1 hr; omega))
  have hsum : (∑ r ∈ Finset.range n, (matOpNorm (L - 1)) ^ r) ≤ (n : ℝ) * (B + 1) ^ (n + 1) := by
    calc
      _ ≤ ∑ _r ∈ Finset.range n, (B + 1) ^ (n + 1) := Finset.sum_le_sum hpow
      _ = _ := by simp
  have hLpow : B ≤ (B + 1) ^ (n + 1) := by
    have h := pow_le_pow_right₀ hbase (show 1 ≤ n + 1 by omega)
    have h' : B + 1 ≤ (B + 1) ^ (n + 1) := by simpa only [pow_one] using h
    exact (show B ≤ B + 1 by linarith).trans h'
  nlinarith

end Yau.Blueprint.Alignment.Y03Proof
