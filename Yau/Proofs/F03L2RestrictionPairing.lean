import Yau.Proofs.F03DirichletAmbientEnergy

/-! The actual restriction/zero-extension adjoint pairing, for any measurable domain. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem l2ZeroExtension_inner_left {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (O : Set α) (hO : MeasurableSet O)
    (f : Lp ℝ 2 (μ.restrict O)) (k : Lp ℝ 2 μ) :
    inner ℝ (l2ZeroExtension μ O hO f) k = inner ℝ f (l2Restriction μ O k) := by
  classical
  rw [L2.inner_def,L2.inner_def]
  calc
    (∫ x, inner ℝ (l2ZeroExtension μ O hO f x) (k x) ∂μ) =
        ∫ x, O.indicator (fun y => inner ℝ (f y) (k y)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [extendL2_coe μ O hO f] with x hx
      change inner ℝ (extendL2 μ O hO f x) (k x) = _
      rw [hx]
      by_cases hxo : x ∈ O
      · simp only [indicator_of_mem hxo]
      · simp only [indicator_of_notMem hxo,inner_zero_left]
    _ = ∫ x in O, inner ℝ (f x) (k x) ∂μ := integral_indicator hO
    _ = ∫ x in O, inner ℝ (f x) (l2Restriction μ O k x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [restrictL2_coe μ O k] with x hx
      change inner ℝ (f x) (k x) = inner ℝ (f x) (restrictL2 μ O k x)
      rw [hx]

end Yau.Proofs.F03Aux
