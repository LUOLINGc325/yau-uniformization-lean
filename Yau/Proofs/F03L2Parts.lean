import Yau.Proofs.F03ResolventPositivity

/-! Actual positive and negative L2 parts have the original source norm bound. -/
noncomputable section
open MeasureTheory Filter
namespace Yau.Proofs.F03Aux
variable {α : Type*} [MeasurableSpace α]

theorem l2_posPart_norm_le (μ : Measure α) (f : Lp ℝ 2 μ) : ‖Lp.posPart f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_posPart f] with x hx
  rw [hx,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem l2_negPart_norm_le (μ : Measure α) (f : Lp ℝ 2 μ) : ‖Lp.negPart f‖ ≤ ‖f‖ := by
  change ‖Lp.posPart (-f)‖ ≤ ‖f‖
  exact (l2_posPart_norm_le μ (-f)).trans_eq (norm_neg f)

theorem l2_posPart_nonneg (μ : Measure α) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, 0 ≤ Lp.posPart f x := by
  filter_upwards [Lp.coeFn_posPart f] with x hx
  rw [hx]
  exact le_max_right _ _

theorem l2_negPart_nonneg (μ : Measure α) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, 0 ≤ Lp.negPart f x := l2_posPart_nonneg μ (-f)

end Yau.Proofs.F03Aux
