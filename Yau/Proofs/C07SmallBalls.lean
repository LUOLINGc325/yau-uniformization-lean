import Yau.Proofs.C07Exponential
import Yau.Proofs.C07ThreeCircleBall

namespace Yau.Proofs.C07Aux

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The inner exponential bound implies the small-ball estimate with the
paper's constant `c = σ / (4 C₀)`, uniformly in every later clock `u ≥ s`. -/
theorem small_ball_decay_at_clocks {f : E → G} {R C₀ γ σ L B s u : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hC : 0 < C₀) (hγ : 0 < γ) (hγC : γ ≤ C₀) (hσ : 0 < σ)
    (hL : L ≤ 0) (hB : 0 ≤ B) (hR : Real.exp L < R)
    (hs : 0 < s) (hsu : s ≤ u) (hlarge : -2 * L ≤ γ * s)
    (habsorb : B ≤ σ * γ * s / (4 * C₀))
    (hinner : ∀ z : E, ‖z‖ ≤ Real.exp (-C₀ * s) → ‖f z‖ ≤ Real.exp (-σ * u))
    (houter : ∀ z : E, ‖z‖ ≤ Real.exp L → ‖f z‖ ≤ Real.exp B)
    {z : E} (hz : ‖z‖ ≤ Real.exp (-γ * s)) :
    ‖f z‖ ≤ Real.exp (-(σ / (4 * C₀)) * γ * u) := by
  have hu : 0 ≤ u := hs.le.trans hsu
  have hγs : 0 < γ * s := mul_pos hγ hs
  have hγCs : γ * s ≤ C₀ * s := mul_le_mul_of_nonneg_right hγC hs.le
  have hden : 0 < L + C₀ * s := by nlinarith
  have hbounds : -γ * s ∈ Set.Icc (-C₀ * s) L := by constructor <;> nlinarith
  have h := three_circle_exp_bound hf (by nlinarith : -C₀ * s < L) hR hbounds
    (show -σ * u ≤ B by nlinarith) hinner houter hz
  let θ := (L + γ * s) / (L + C₀ * s)
  have hθ : γ / (2 * C₀) ≤ θ :=
    interpolation_weight_lower hC hγ hγC hL hs hlarge
  have hθ₀ : 0 ≤ θ := (div_nonneg hγ.le (by positivity)).trans hθ
  have hθid : 1 - ((-γ * s - -C₀ * s) / (L - -C₀ * s)) = θ := by
    dsimp [θ]
    rw [show L - -C₀ * s = L + C₀ * s by ring]
    apply (eq_div_iff hden.ne').2
    have hcancel := div_mul_cancel₀ (-γ * s - -C₀ * s) hden.ne'
    nlinarith
  have hexp : -σ * u * (1 - (-γ * s - -C₀ * s) / (L - -C₀ * s)) +
      B * ((-γ * s - -C₀ * s) / (L - -C₀ * s)) =
      -θ * σ * u + (1 - θ) * B := by
    rw [← hθid]
    ring
  rw [hexp] at h
  exact h.trans (Real.exp_le_exp.mpr
    (absorb_interpolation_error hC hγ hσ hθ₀ hθ hB hs.le hsu habsorb))

end Yau.Proofs.C07Aux
