import Yau.Proofs.P03AffineSchurCharts

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- Dimension of the actual free row-solving variables, with the pivot
column omitted, leaves precisely twice the row count available. -/
theorem affineRowParameter_finrank_lt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {m L : ℕ} (pivot : Fin L) (hd : Module.finrank ℝ E < m * 2) :
    Module.finrank ℝ (E × (Fin m → {l : Fin L // l ≠ pivot} → ℂ)) <
      Module.finrank ℝ (Fin m → Fin L → ℂ) := by
  have ht : Module.finrank ℝ (Fin m → Fin L → ℂ) = m * L * 2 := by
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  rw [Module.finrank_prod, affineSchurFreeRows_finrank, Fintype.card_fin, ht]
  calc
    Module.finrank ℝ E + m * (L - 1) * 2 < m * 2 + m * (L - 1) * 2 :=
      Nat.add_lt_add_right hd _
    _ = m * ((L - 1) + 1) * 2 := by ring
    _ = m * L * 2 := by rw [Nat.sub_add_cancel (show 1 ≤ L from Nat.zero_lt_of_lt pivot.isLt)]

end Yau.NodeProofs.P03Aux
