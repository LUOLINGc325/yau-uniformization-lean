import Yau.Proofs.Y03ThresholdGraphs
import Yau.Proofs.Y03SeparatedRows
import Yau.Proofs.Y03GraphBasis
import Yau.Proofs.Y03InverseBound

/-! Construct the actual one-step alignment matrix from the given unitary jump and propagated weights. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem exists_weight_alignment_matrix (μ ν wold wnew : Fin n → ℝ) (U E : Herm n)
    (hU : Unitary U) {δ B g : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (hB : 0 ≤ B) (hg : 0 < g) (hE : matOpNorm E ≤ δ)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ B) (hν : ∀ i, 0 ≤ ν i ∧ ν i ≤ B)
    (horder : ∀ v : Fin n → ℂ, (∑ i, μ i * ‖(v ᵥ* U) i‖ ^ 2) ≤ ∑ i, ν i * ‖v i‖ ^ 2)
    (hpassage : ∀ i l, μ l - g ≤ ν i → wold l ≤ wnew i)
    (hsmall : 32 * δ * B ≤ g / 2) :
    ∃ L : Herm n, (∀ i, L i i = 1) ∧
      (∀ i l, i ≠ l → L i l ≠ 0 → wold i < wold l) ∧ IsUnit L ∧
      matOpNorm L ≤ (n : ℝ) ^ 2 * (1 + (n : ℝ) * Real.sqrt (2 * (B + g) / g)) ∧
      matOpNorm L + matOpNorm L⁻¹ ≤ (n + 1 : ℝ) *
        ((n : ℝ) ^ 2 * (1 + (n : ℝ) * Real.sqrt (2 * (B + g) / g)) + 1) ^ (n + 1) ∧
      ∀ i l, wnew i < wold l → ((1 + E) * U * L⁻¹) i l = 0 := by
  let CP := Real.sqrt (2 * (B + g) / g)
  have hCP : 0 ≤ CP := Real.sqrt_nonneg _
  have hprojection (r : ℕ) (_hr : r < (weightValueSet wold).card)
      (a : selectedRowSpace ((1 + E) * U) (newWeightLevel wold wnew r)) :
      ‖a‖ ≤ CP * ‖coordinateProjectionOnto (oldWeightLevel wold r) a‖ := by
    exact separated_rows_projection_bound μ ν U E hU hδ hδ' hB hg hE hμ hν horder
      (oldWeightLevel wold r) (newWeightLevel wold wnew r)
      (rate_gap_of_separated_weights μ ν wold wnew g _ _ hpassage (weightLevel_separated wold wnew r))
      hsmall a
  obtain ⟨T, hpT, hnested, hrequired, hnormT⟩ := exists_threshold_graphs wold wnew ((1 + E) * U) hCP hprojection
  let L := graphMatrix wold T
  have hdiag : ∀ i, L i i = 1 := graphMatrix_diagonal wold T hpT
  have hsupport : ∀ i l, i ≠ l → L i l ≠ 0 → wold i < wold l := graphMatrix_strict_support wold T hpT
  have hnorm : matOpNorm L ≤ (n : ℝ) ^ 2 * (1 + (n : ℝ) * CP) :=
    graphMatrix_norm_le wold T (by positivity) hnormT
  refine ⟨L, hdiag, hsupport, strict_weight_isUnit L wold hdiag hsupport, hnorm, ?_, ?_⟩
  · exact strict_weight_change_polynomial_bound L wold hdiag hsupport (by positivity) hnorm
  · exact graphMatrix_zero_pattern wold wnew ((1 + E) * U) T hpT hnested hrequired

end Yau.Blueprint.Alignment.Y03Proof
