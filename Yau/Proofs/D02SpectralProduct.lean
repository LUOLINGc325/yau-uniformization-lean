import Yau.Proofs.D02Geometry

/-! The all-dimensional product/trace estimate behind the actual
inverse-Jacobian bound. The empty spectrum is included literally. -/

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem spectral_product_le_factor {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (B : ℝ) (htrace : ∑ i, lam i ≤ B) (i : Fin n) :
    (∏ j, lam j) ≤ lam i * max 1 B ^ (n - 1) := by
  classical
  have hle (j : Fin n) : lam j ≤ max 1 B :=
    (Finset.single_le_sum (fun k _ => hlam k) (Finset.mem_univ j)).trans
      (htrace.trans (le_max_right 1 B))
  have hprod : (∏ j ∈ Finset.univ.erase i, lam j) ≤
      ∏ _j ∈ Finset.univ.erase i, max 1 B :=
    Finset.prod_le_prod₀ (fun j _ => hlam j) (fun j _ => hle j)
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin] at hprod
  rw [← Finset.mul_prod_erase Finset.univ lam (Finset.mem_univ i)]
  exact mul_le_mul_of_nonneg_left hprod (hlam i)

/-- Multiplication by any genuine nonnegative spectral weights preserves
the estimate, including the zero-dimensional empty sum. -/
theorem spectral_weighted_product_bound {n : ℕ} (lam weight : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hweight : ∀ i, 0 ≤ weight i)
    (B : ℝ) (htrace : ∑ i, lam i ≤ B) :
    (∏ i, lam i) * (∑ i, weight i) ≤
      max 1 B ^ (n - 1) * (∑ i, lam i * weight i) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (spectral_product_le_factor lam hlam B htrace i) (hweight i)
  convert h using 1 <;> ring

theorem spectral_inverse_bound {n : ℕ} (lam weight : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hweight : ∀ i, 0 ≤ weight i)
    (B : ℝ) (htrace : ∑ i, lam i ≤ B) :
    (∑ i, weight i) ≤
      max 1 B ^ (n - 1) / (∏ i, lam i) * (∑ i, lam i * weight i) := by
  have hp : 0 < ∏ i, lam i := Finset.prod_pos (fun i _ => hlam i)
  have h := spectral_weighted_product_bound lam weight (fun i => (hlam i).le) hweight B htrace
  calc
    _ ≤ (max 1 B ^ (n - 1) * (∑ i, lam i * weight i)) / (∏ i, lam i) :=
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using h)
    _ = _ := by ring

end Yau.NodeProofs.D02Aux
