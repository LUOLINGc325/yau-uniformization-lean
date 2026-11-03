import spec.CHAIN.CONTRACTS

/-! The clock multiplier is controlled before any localization parameters
are selected. No sign assumption is made on the physical test derivative. -/

noncomputable section
open Set Metric
namespace Yau.Blueprint.V01Proof

theorem exists_clock_factor_tolerance (τ β : ℝ) (hβ : 0 < β) :
    ∃ d : ℝ, 0 < d ∧ ∀ r L : ℝ, |r| ≤ d → |L| ≤ d →
      0 ≤ (1 + r) ^ 2 * Real.exp (-L) ∧
      (1 + r) ^ 2 * Real.exp (-L) ≤ 2 ∧
      |(1 + r) ^ 2 * Real.exp (-L) - 1| * (1 + |τ|) ≤ β / 4 := by
  let η := min 1 (β / (4 * (1 + |τ|)))
  have hden : 0 < 4 * (1 + |τ|) := by positivity
  have hη : 0 < η := lt_min zero_lt_one (div_pos hβ hden)
  have hf : Continuous (fun p : ℝ × ℝ => (1 + p.1) ^ 2 * Real.exp (-p.2)) := by
    fun_prop
  obtain ⟨δ, hδ, hLocal⟩ := Metric.continuousAt_iff.mp hf.continuousAt η hη
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro r L hr hL
  have hd : dist (r, L) (0, 0) < δ := by
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using
      (max_le hr hL).trans_lt (half_lt_self hδ)
  have he : |(1 + r) ^ 2 * Real.exp (-L) - 1| ≤ η := by
    simpa only [Real.dist_eq, neg_zero, Real.exp_zero, add_zero, one_pow, one_mul] using
      (hLocal hd).le
  have he₁ : |(1 + r) ^ 2 * Real.exp (-L) - 1| ≤ 1 := he.trans (min_le_left _ _)
  have he₂ : |(1 + r) ^ 2 * Real.exp (-L) - 1| * (4 * (1 + |τ|)) ≤ β :=
    (le_div_iff₀ hden).mp (he.trans (min_le_right _ _))
  exact ⟨mul_nonneg (sq_nonneg _) (Real.exp_pos _).le,
    by linarith [(abs_le.mp he₁).2], by nlinarith⟩

end Yau.Blueprint.V01Proof
