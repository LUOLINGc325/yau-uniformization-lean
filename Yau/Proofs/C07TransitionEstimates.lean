import Yau.Proofs.C07JetFamily
import Yau.Proofs.C07SmallBallFamily

/-! The actual inner estimate supplies both complete frozen transition estimates. -/

open Filter

namespace Yau.Proofs.C07Aux

variable {n : ℕ}

theorem transition_full_decay_estimates
    {F : ℝ → ℝ → Yau.ComplexVector n → Yau.ComplexVector n} {s : ℝ → ℝ}
    {R β σ B T₀ : ℝ} (hR : 0 < R) (hβ : 0 < β) (hσ : 0 < σ)
    (hclock : Tendsto s atTop atTop) (hmono : MonotoneOn s (Set.Ici T₀))
    (hhol : ∀ t u, T₀ ≤ t → t ≤ u → DifferentiableOn ℂ (F t u) (Metric.ball 0 R))
    (hfixed : ∀ t u, T₀ ≤ t → t ≤ u → ∀ z ∈ Metric.ball (0 : Yau.ComplexVector n) R,
      ‖F t u z‖ ≤ B)
    (hinner : ∀ t u, T₀ ≤ t → t ≤ u → ∀ z : Yau.ComplexVector n,
      ‖z‖ ≤ Real.exp (-β * s t) → ‖F t u z‖ ≤ Real.exp (-σ * s u)) :
    (∀ d : ℕ, ∃ Cd Td : ℝ, ∀ t u, Td ≤ t → t ≤ u →
      Yau.jetNorm (F t u) d ≤ Cd * min 1 (Real.exp (Cd * s t - σ * s u))) ∧
    (∃ c γ₀ : ℝ, 0 < c ∧ 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      ∃ Tγ : ℝ, ∀ t u, Tγ ≤ t → t ≤ u → ∀ z : Yau.ComplexVector n,
        ‖z‖ ≤ Real.exp (-γ * s t) → ‖F t u z‖ ≤ Real.exp (-c * γ * s u)) := by
  constructor
  · apply transition_jet_bounds hR hβ hclock hhol hfixed
    intro t u ht htu z hz
    exact hinner t u ht htu z (le_of_lt (by
      simpa only [Metric.mem_ball, dist_zero_right] using hz))
  · let δ := min (R / 2) (1 / 2 : ℝ)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδR : δ < R := (min_le_left _ _).trans_lt (by linarith)
    have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have hBpos : 0 < max 1 B := zero_lt_one.trans_le (le_max_left _ _)
    have houter : ∀ t u, T₀ ≤ t → t ≤ u → ∀ z : Yau.ComplexVector n,
        ‖z‖ ≤ Real.exp (Real.log δ) → ‖F t u z‖ ≤ Real.exp (Real.log (max 1 B)) := by
      intro t u ht htu z hz
      rw [Real.exp_log hδ] at hz
      rw [Real.exp_log hBpos]
      apply (hfixed t u ht htu z ?_).trans (le_max_right _ _)
      simpa only [Metric.mem_ball, dist_zero_right] using hz.trans_lt hδR
    exact small_ball_decay_family hβ hσ (Real.log_nonpos hδ.le hδ1)
      (Real.log_nonneg (le_max_left 1 B)) (by rwa [Real.exp_log hδ])
      hclock hmono hhol hinner houter

end Yau.Proofs.C07Aux
