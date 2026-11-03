import Yau.Proofs.F03L2Order

/-! Actual order comparison passes to contraction Euler powers. -/
noncomputable section
open MeasureTheory
namespace Yau.Proofs.F03Aux
set_option maxHeartbeats 1000000

theorem l2_powers_le_of_step {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : Monotone A)
    (hB : ∀ f, 0 ≤ f → 0 ≤ B f)
    (hAB : ∀ f, 0 ≤ f → A f ≤ B f) (m : ℕ) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    (A^m) f ≤ (B^m) f := by
  have hBp : ∀ k : ℕ, 0 ≤ (B^k) f := by
    intro k
    induction k with
    | zero => simpa only [pow_zero,one_apply_eq_self] using hf
    | succ k hk => simpa only [pow_succ',mul_apply_eq_comp] using hB _ hk
  induction m with
  | zero => simp only [pow_zero,one_apply_eq_self,le_refl]
  | succ m hm =>
    simp only [pow_succ',mul_apply_eq_comp]
    exact (hA hm).trans (hAB _ (hBp m))

end Yau.Proofs.F03Aux
