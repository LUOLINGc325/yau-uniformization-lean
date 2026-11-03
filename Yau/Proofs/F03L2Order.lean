import Yau.Proofs.F03L2Restriction

/-! Order is preserved by the actual scalar restriction and zero-extension maps. -/
noncomputable section
open MeasureTheory Filter Set
namespace Yau.Proofs.F03Aux
variable {α : Type*} [MeasurableSpace α]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem l2Restriction_nonneg (μ : Measure α) (Ω : Set α)
    (f : Lp ℝ 2 μ) (hf : 0 ≤ f) : 0 ≤ l2Restriction μ Ω f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [restrictL2_coe μ Ω f,ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr hf)] with x hr hx
  change 0 ≤ restrictL2 μ Ω f x
  rw [hr]
  exact hx

theorem l2ZeroExtension_nonneg (μ : Measure α) (Ω : Set α) (hΩ : MeasurableSet Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) (hf : 0 ≤ f) : 0 ≤ l2ZeroExtension μ Ω hΩ f := by
  have hfΩ := (ae_restrict_iff' hΩ).mp ((Lp.coeFn_nonneg _).mpr hf)
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [extendL2_coe μ Ω hΩ f,hfΩ] with x he hx
  change 0 ≤ extendL2 μ Ω hΩ f x
  rw [he]
  by_cases hm : x ∈ Ω
  · rw [indicator_of_mem hm]
    exact hx hm
  · rw [indicator_of_notMem hm]

theorem l2_linear_monotone {β : Type*} [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f, 0 ≤ f → 0 ≤ T f) : Monotone T := by
  intro f k hfk
  have h := hT (k-f) (sub_nonneg.mpr hfk)
  rw [map_sub] at h
  exact sub_nonneg.mp h

theorem l2Restriction_monotone (μ : Measure α) (Ω : Set α) : Monotone (l2Restriction μ Ω) :=
  l2_linear_monotone μ (μ.restrict Ω) _ (l2Restriction_nonneg μ Ω)

theorem l2ZeroExtension_monotone (μ : Measure α) (Ω : Set α) (hΩ : MeasurableSet Ω) :
    Monotone (l2ZeroExtension μ Ω hΩ) :=
  l2_linear_monotone (μ.restrict Ω) μ _ (l2ZeroExtension_nonneg μ Ω hΩ)

end Yau.Proofs.F03Aux
