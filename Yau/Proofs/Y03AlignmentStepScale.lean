import Yau.Proofs.Y03AlignmentStep
import Yau.Proofs.Y03ProjectionScale

/-! The constructed alignment matrix has an explicit O(j) bound independent of the terminal horizon. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def alignmentCoefficient (n : ℕ) (B eps : ℝ) : ℝ :=
  max 1 ((n : ℝ) ^ 2 * (1 + (n : ℝ) * Real.sqrt (2 * (B + eps) / eps)))

theorem alignmentCoefficient_pos (n : ℕ) (B eps : ℝ) : 0 < alignmentCoefficient n B eps :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem exists_linear_bound_alignment_matrix (μ ν wold wnew : Fin n → ℝ) (U E : Herm n)
    (hU : Unitary U) {δ q B eps j : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (hq : 0 < q) (hB : 0 < B) (heps : 0 < eps) (hj : 1 ≤ j) (hE : matOpNorm E ≤ δ)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ B * q) (hν : ∀ i, 0 ≤ ν i ∧ ν i ≤ B * q)
    (horder : ∀ v : Fin n → ℂ, (∑ i, μ i * ‖(v ᵥ* U) i‖ ^ 2) ≤ ∑ i, ν i * ‖v i‖ ^ 2)
    (hpassage : ∀ i l, μ l - eps * q / j ^ 2 ≤ ν i → wold l ≤ wnew i)
    (hsmall : δ ≤ eps / (64 * B * j ^ 2)) :
    ∃ L : Herm n, (∀ i, L i i = 1) ∧
      (∀ i l, i ≠ l → L i l ≠ 0 → wold i < wold l) ∧ IsUnit L ∧
      matOpNorm L ≤ alignmentCoefficient n B eps * j ∧
      matOpNorm L + matOpNorm L⁻¹ ≤ (n + 1 : ℝ) *
        (alignmentCoefficient n B eps * j + 1) ^ (n + 1) ∧
      ∀ i l, wnew i < wold l → ((1 + E) * U * L⁻¹) i l = 0 := by
  have hjpos : 0 < j := zero_lt_one.trans_le hj
  have hg : 0 < eps * q / j ^ 2 := div_pos (mul_pos heps hq) (sq_pos_of_pos hjpos)
  obtain ⟨L, hdiag, hsupport, hunit, hnorm, _, hzero⟩ := exists_weight_alignment_matrix
    μ ν wold wnew U E hU hδ hδ' (mul_pos hB hq).le hg hE hμ hν horder hpassage
    (perturbation_threshold_scale hq heps hB hjpos hsmall)
  have hCP := projection_inverse_scale hq heps hB.le hj
  have hnorm' : matOpNorm L ≤ alignmentCoefficient n B eps * j := by
    have hmul := mul_le_mul_of_nonneg_left hCP (show 0 ≤ (n : ℝ) from Nat.cast_nonneg _)
    have hinner : 1 + (n : ℝ) * Real.sqrt (2 * (B * q + eps * q / j ^ 2) / (eps * q / j ^ 2)) ≤
        (1 + (n : ℝ) * Real.sqrt (2 * (B + eps) / eps)) * j := by nlinarith
    have hn := mul_le_mul_of_nonneg_left hinner (sq_nonneg (n : ℝ))
    have hA := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ)
      ((n : ℝ) ^ 2 * (1 + (n : ℝ) * Real.sqrt (2 * (B + eps) / eps)))) hjpos.le
    exact hnorm.trans (hn.trans (by simpa only [alignmentCoefficient, mul_assoc] using hA))
  refine ⟨L, hdiag, hsupport, hunit, hnorm', ?_, hzero⟩
  exact strict_weight_change_polynomial_bound L wold hdiag hsupport
    (mul_nonneg (alignmentCoefficient_pos n B eps).le hjpos.le) hnorm'

end Yau.Blueprint.Alignment.Y03Proof
