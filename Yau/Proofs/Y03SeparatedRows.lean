import Yau.Proofs.Y03RowSpace

/-! Projection bounds on separated old and new weight cuts, including the empty selected space. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem separated_rows_projection_bound (μ ν : Fin n → ℝ) (U E : Herm n)
    (hU : Unitary U) {δ B g : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (hB : 0 ≤ B) (hg : 0 < g) (hE : matOpNorm E ≤ δ)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ B) (hν : ∀ i, 0 ≤ ν i ∧ ν i ≤ B)
    (horder : ∀ v : Fin n → ℂ, (∑ i, μ i * ‖(v ᵥ* U) i‖ ^ 2) ≤ ∑ i, ν i * ‖v i‖ ^ 2)
    (sold snew : Finset (Fin n))
    (hgap : ∀ i ∈ snew, ∀ l, l ∉ sold → ν i + g ≤ μ l)
    (hsmall : 32 * δ * B ≤ g / 2)
    (a : selectedRowSpace ((1 + E) * U) snew) :
    ‖a‖ ≤ Real.sqrt (2 * (B + g) / g) * ‖coordinateProjectionOnto sold a‖ := by
  obtain ⟨c, hc⟩ := a.property
  have hca : rowApply ((1 + E) * U) (c : ComplexVector n) = (a : ComplexVector n) :=
    (rowLinearMap_apply _ _).symm.trans hc
  by_cases hne : snew.Nonempty
  · obtain ⟨imax, himax, hmax⟩ := Finset.exists_max_image snew ν hne
    have hcoef (i : Fin n) (hi : (c : ComplexVector n) i ≠ 0) : ν i ≤ ν imax := by
      apply hmax i
      by_contra hn
      exact hi (c.property i hn)
    have hp := perturbed_row_projection_mass μ ν U E hU hδ hδ' hB (hν imax).1 (hν imax).2 hg
      hE hμ horder sold (hgap imax himax) hsmall (c : ComplexVector n) hcoef
    rw [hca] at hp
    exact norm_le_of_projection_mass (a : ComplexVector n) (coordinateProjection sold a) hg hB hp
  · have hempty : snew = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    have hc0 : (c : ComplexVector n) = 0 := by
      ext i
      exact c.property i (by rw [hempty]; simp)
    have ha0 : (a : ComplexVector n) = 0 := by rw [← hca, hc0]; simp [rowApply]
    change ‖(a : ComplexVector n)‖ ≤ Real.sqrt (2 * (B + g) / g) * ‖coordinateProjection sold (a : ComplexVector n)‖
    simp only [ha0, norm_zero, map_zero, mul_zero, le_refl]

theorem rate_gap_of_separated_weights (μ ν wold wnew : Fin n → ℝ) (g : ℝ)
    (sold snew : Finset (Fin n))
    (hpassage : ∀ i l, μ l - g ≤ ν i → wold l ≤ wnew i)
    (hseparated : ∀ i ∈ snew, ∀ l, l ∉ sold → wnew i < wold l) :
    ∀ i ∈ snew, ∀ l, l ∉ sold → ν i + g ≤ μ l := by
  intro i hi l hl
  by_contra hn
  have hp := hpassage i l (by linarith)
  exact (not_le_of_gt (hseparated i hi l hl)) hp

end Yau.Blueprint.Alignment.Y03Proof
