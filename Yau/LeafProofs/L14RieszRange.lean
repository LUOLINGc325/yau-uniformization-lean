import Yau.Analysis.RangeRiesz

namespace Yau.LeafProofs.L14Aux

variable {V H : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complex specialization of the shared real/complex range-Riesz theorem. -/
theorem exists_norm_le_inner_eq_of_range_bound
    (J : V →ₗ[ℂ] H) (f : V →ₗ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ v, ‖f v‖ ≤ C * ‖J v‖) :
    ∃ u : H, ‖u‖ ≤ C ∧ ∀ v, inner ℂ u (J v) = f v :=
  Yau.Analysis.exists_norm_le_inner_eq_of_range_bound J f C hC hbound

/-- Squared estimate with the same constant, using the shared theorem. -/
theorem exists_sq_norm_le_inner_eq_of_range_bound
    (J : V →ₗ[ℂ] H) (f : V →ₗ[ℂ] ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ v, ‖f v‖ ^ 2 ≤ A * ‖J v‖ ^ 2) :
    ∃ u : H, ‖u‖ ^ 2 ≤ A ∧ ∀ v, inner ℂ u (J v) = f v :=
  Yau.Analysis.exists_sq_norm_le_inner_eq_of_range_bound J f A hA hbound

end Yau.LeafProofs.L14Aux
