import spec.CHAIN.CONTRACTS

/-! One large sublevel threshold makes the actual contact coefficient
strictly negative, uniformly in every properness penalty 0 ≤ δ ≤ 1. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem contact_coefficient_negative {B₀ G₀ c L δ : ℝ}
    (hB : 0 ≤ B₀) (hG : 0 ≤ G₀) (hL : 0 < L) (hδ : δ ≤ 1)
    (hlarge : 4 * B₀ + 13 * G₀ < c * L) :
    (3 * B₀ + 3 * G₀) / L ^ 2 - c * L⁻¹ + 8 * (G₀ / L ^ 2) +
      δ * (B₀ / L ^ 2 + 2 * (G₀ / L ^ 2)) < 0 := by
  have hnonneg : 0 ≤ B₀ / L ^ 2 + 2 * (G₀ / L ^ 2) := by positivity
  have hpenalty := mul_le_mul_of_nonneg_right hδ hnonneg
  have hsmall : (4 * B₀ + 13 * G₀) / L ^ 2 < c / L := by
    apply (div_lt_iff₀ (sq_pos_of_pos hL)).mpr
    have heq : c / L * L ^ 2 = c * L := by field_simp
    rwa [heq]
  calc
    _ ≤ (3 * B₀ + 3 * G₀) / L ^ 2 - c * L⁻¹ + 8 * (G₀ / L ^ 2) +
        (B₀ / L ^ 2 + 2 * (G₀ / L ^ 2)) := by linarith
    _ = (4 * B₀ + 13 * G₀) / L ^ 2 - c / L := by ring
    _ < 0 := sub_neg.mpr hsmall

theorem exists_uniform_contact_threshold {B₀ G₀ c : ℝ}
    (hB : 0 ≤ B₀) (hG : 0 ≤ G₀) (hc : 0 < c) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, ∀ δ ≤ 1,
      (3 * B₀ + 3 * G₀) / L ^ 2 - c * L⁻¹ + 8 * (G₀ / L ^ 2) +
        δ * (B₀ / L ^ 2 + 2 * (G₀ / L ^ 2)) < 0 := by
  let L₀ := max 1 ((4 * B₀ + 13 * G₀) / c + 1)
  have hL₀ : 0 < L₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL δ hδ
  have hdiv : (4 * B₀ + 13 * G₀) / c < L :=
    lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hL)
  have hlarge : 4 * B₀ + 13 * G₀ < c * L := by
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hdiv
  exact contact_coefficient_negative hB hG (hL₀.trans_le hL) hδ hlarge

end Yau.NodeProofs.F01Aux
