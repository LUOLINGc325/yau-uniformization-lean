import Yau.Proofs.Y03Weights
import Yau.Proofs.Y03Grid

/-! Passage estimates use the literal grid and the multiplier's shifted recurrence. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem weight_passage_same_macro {n : ℕ} (Q : ℕ → ℝ) (N : ℕ)
    (M hm scale K eps : ℝ) (j₀ : ℕ) (μ : ℕ → Fin n → ℝ)
    (k : ℕ) (i l : Fin n)
    (hmacro : macroAt Q N M hm j₀ (k + 1) = macroAt Q N M hm j₀ k)
    (hpass : μ k l - eps * theta Q (macroAt Q N M hm j₀ k) ≤ μ (k + 1) i) :
    weight Q N M hm scale K eps j₀ μ k l ≤ weight Q N M hm scale K eps j₀ μ (k + 1) i := by
  have hslot : slotAt Q N M hm j₀ (k + 1) = slotAt Q N M hm j₀ k + 1 := by
    unfold slotAt
    rw [hmacro]
    have := offset_macroAt_le Q N M hm j₀ k
    omega
  unfold weight
  simp only [hmacro]
  apply propagatedWeight_mono_of_passage
  · exact Finset.mem_product.2 ⟨Finset.mem_range.2 (slotAt_lt_pieces Q N M hm j₀ k),
      Finset.mem_univ _⟩
  · change (slotAt Q N M hm j₀ (k + 1), i) ∈
      (Finset.range (pieces Q N M hm (macroAt Q N M hm j₀ k))).product Finset.univ
    rw [← hmacro]
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (slotAt_lt_pieces Q N M hm j₀ (k + 1)),
      Finset.mem_univ _⟩
  · constructor
    · exact Or.inr hslot.symm
    · simp only [offset_add_slotAt]
      rw [← hmacro, offset_add_slotAt]
      simpa only [hmacro] using hpass

theorem next_multiplier_raw_dominates {lam K b q D mu : ℝ}
    (hlam : 0 ≤ lam) (hK : 0 ≤ K) (hq : 0 ≤ q) (hD : 0 < D)
    (hKb : 2 ≤ K * b) (hratio : K / D ≤ 1) (hmu : b * q ≤ mu) :
    lam * mu ≤ (lam * (1 + K / D)) * (mu - q / D) := by
  have hKm : 2 * q ≤ K * mu := by
    have h₁ := mul_le_mul_of_nonneg_left hmu hK
    have h₂ := mul_le_mul_of_nonneg_right hKb hq
    nlinarith
  have hqbound : (1 + K / D) * q ≤ 2 * q := by nlinarith
  have hbracket : 0 ≤ K * mu - (1 + K / D) * q := by linarith
  have hid : (1 + K / D) * (mu - q / D) - mu =
      (K * mu - (1 + K / D) * q) / D := by field_simp; ring
  have hscalar : mu ≤ (1 + K / D) * (mu - q / D) := by
    apply sub_nonneg.1
    rw [hid]
    exact div_nonneg hbracket hD.le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscalar hlam

theorem cross_macro_weight_passage {Q : ℕ → ℝ} {scale K eps b : ℝ}
    {j : ℕ} {muOld muNew wOld wNew : ℝ}
    (hlam : 0 ≤ multiplier scale K j) (hK : 0 ≤ K)
    (hq : 0 ≤ Q (j + 1)) (hθ : 0 ≤ theta Q j) (heps : eps ≤ 0.9)
    (hKb : 2 ≤ K * b) (hratio : K / ((j + 1 : ℕ) : ℝ) ^ 2 ≤ 1)
    (hmu : b * Q (j + 1) ≤ muNew)
    (hpass : muOld - eps * theta Q j ≤ muNew)
    (hOld : wOld ≤ multiplier scale K j * (muOld - 0.9 * theta Q j))
    (hNew : multiplier scale K (j + 1) * (muNew - theta Q (j + 1)) ≤ wNew) :
    wOld ≤ wNew := by
  have hraw := next_multiplier_raw_dominates hlam hK hq
    (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ 2) hKb hratio hmu
  have hmid : muOld - 0.9 * theta Q j ≤ muNew := by nlinarith
  apply hOld.trans
  apply (mul_le_mul_of_nonneg_left hmid hlam).trans
  apply hraw.trans
  simpa only [multiplier_succ, theta] using hNew

end Yau.Blueprint.Alignment.Y03Proof
