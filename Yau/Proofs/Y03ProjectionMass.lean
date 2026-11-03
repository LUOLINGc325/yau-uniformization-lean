import Yau.Blueprint.Alignment

/-! The quantitative coordinate-projection gain from a strict rate gap. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem projection_mass_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (μ a : ι → ℝ) {r g B : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (ha : ∀ i, 0 ≤ a i) (hr : 0 ≤ r) (hg : 0 < g)
    (hrB : r ≤ B) (hout : ∀ i, i ∉ s → r + g ≤ μ i)
    (hquad : (∑ i, μ i * a i) ≤ (r + g / 2) * ∑ i, a i) :
    g / (2 * (B + g)) * (∑ i, a i) ≤ ∑ i ∈ s, a i := by
  have hsplit : (∑ i ∈ sᶜ, a i) + (∑ i ∈ s, a i) = ∑ i, a i :=
    Finset.sum_compl_add_sum s a
  have hselected : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
  have hsum : (r + g) * (∑ i ∈ sᶜ, a i) ≤ ∑ i, μ i * a i := by
    calc
      _ = ∑ i ∈ sᶜ, (r + g) * a i := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ sᶜ, μ i * a i := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (hout i (Finset.mem_compl.1 hi)) (ha i)
      _ ≤ ∑ i, μ i * a i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => mul_nonneg (hμ i) (ha i))
  have hB : 0 < B + g := by linarith
  have hpay : g * (∑ i, a i) ≤ 2 * (B + g) * (∑ i ∈ s, a i) := by
    have hreplace := mul_le_mul_of_nonneg_right hrB hselected
    nlinarith
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) hB)).2
  simpa only [mul_comm] using hpay

end Yau.Blueprint.Alignment.Y03Proof
