import Mathlib.Analysis.SpecialFunctions.Exp

/-! The actual exponential rate beats every fixed integer inverse time power. -/
noncomputable section
open Filter Set
open scoped Topology

namespace Yau.NodeProofs.P06Aux.InitialTrace

theorem remoteRate_tendsto (C a : ℝ) (p : ℕ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => (C / t ^ p) * Real.exp (-a / t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => a / t) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] (0 : ℝ)) atTop).const_mul_atTop ha
  have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp hi).const_mul (C / a ^ p)
  rw [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  simp only [Function.comp_def, div_pow, neg_div]
  field_simp [ha.ne', ne_of_gt ht]

theorem remoteRate_small (C a : ℝ) (p : ℕ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → (C / t ^ p) * Real.exp (-a / t) < ε := by
  have hh := (remoteRate_tendsto C a p ha).eventually (Iio_mem_nhds hε)
  obtain ⟨τ, hτ, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hh
  exact ⟨τ, hτ, fun t ht htτ => hb ⟨ht, htτ⟩⟩

end Yau.NodeProofs.P06Aux.InitialTrace
