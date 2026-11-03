import Yau.Proofs.V03BoundaryCurrentEstimate

/-! Actual interval integrals of finite continuous signed currents obey
the sum of their separate native integral bounds, including empty families. -/

open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem abs_intervalIntegral_fintype_sum_le {ι : Type*} [Fintype ι]
    {f : ι → ℝ → ℝ} {a b Z : ℝ} (hf : ∀ i, IntervalIntegrable (f i) volume a b)
    (hbound : ∀ i, |∫ θ in a..b, f i θ| ≤ Z) :
    |∫ θ in a..b, ∑ i, f i θ| ≤ (Fintype.card ι : ℝ) * Z := by
  rw [intervalIntegral.integral_finset_sum (fun i _ => hf i)]
  calc
    _ ≤ ∑ i, |∫ θ in a..b, f i θ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, Z := Finset.sum_le_sum (fun i _ => hbound i)
    _ = _ := by simp

end Yau.Blueprint.V03Proof
