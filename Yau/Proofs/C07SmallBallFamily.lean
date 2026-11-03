import Yau.Proofs.C07SmallBalls

open Filter

namespace Yau.Proofs.C07Aux

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The two analytic bounds give the complete physical-time quantifiers of
the last shrinking-chart estimate.  Only the starting threshold depends on
`γ`; its constant is independent of both physical-time endpoints. -/
theorem small_ball_decay_family {F : ℝ → ℝ → E → G} {s : ℝ → ℝ}
    {R C₀ σ L B T₀ : ℝ}
    (hC : 0 < C₀) (hσ : 0 < σ) (hL : L ≤ 0) (hB : 0 ≤ B)
    (hR : Real.exp L < R) (hclock : Tendsto s atTop atTop)
    (hmono : MonotoneOn s (Set.Ici T₀))
    (hhol : ∀ t u, T₀ ≤ t → t ≤ u → DifferentiableOn ℂ (F t u) (Metric.ball 0 R))
    (hinner : ∀ t u, T₀ ≤ t → t ≤ u → ∀ z : E,
      ‖z‖ ≤ Real.exp (-C₀ * s t) → ‖F t u z‖ ≤ Real.exp (-σ * s u))
    (houter : ∀ t u, T₀ ≤ t → t ≤ u → ∀ z : E,
      ‖z‖ ≤ Real.exp L → ‖F t u z‖ ≤ Real.exp B) :
    ∃ c γ₀ : ℝ, 0 < c ∧ 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      ∃ Tγ : ℝ, ∀ t u, Tγ ≤ t → t ≤ u → ∀ z : E,
        ‖z‖ ≤ Real.exp (-γ * s t) → ‖F t u z‖ ≤ Real.exp (-c * γ * s u) := by
  refine ⟨σ / (4 * C₀), C₀, by positivity, hC, ?_⟩
  intro γ hγ hγC
  let K := max 1 (max (-2 * L / γ) (4 * C₀ * B / (σ * γ)))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    (hclock.eventually (Filter.eventually_ge_atTop K))
  refine ⟨max T₀ T, ?_⟩
  intro t u ht htu z hz
  have ht₀ : T₀ ≤ t := (le_max_left _ _).trans ht
  have htT : T ≤ t := (le_max_right _ _).trans ht
  have hKt : K ≤ s t := hT t htT
  have hs : 0 < s t := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hKt)
  have hlarge : -2 * L ≤ γ * s t := by
    have h := (le_max_left (-2 * L / γ) _).trans ((le_max_right _ _).trans hKt)
    have hh := (div_le_iff₀ hγ).1 h
    nlinarith
  have habsorb : B ≤ σ * γ * s t / (4 * C₀) := by
    have h := (le_max_right (-2 * L / γ) _).trans ((le_max_right _ _).trans hKt)
    have hh := (div_le_iff₀ (mul_pos hσ hγ)).1 h
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  exact small_ball_decay_at_clocks (hhol t u ht₀ htu) hC hγ hγC hσ hL hB hR
    hs (hmono ht₀ (ht₀.trans htu) htu) hlarge habsorb
    (hinner t u ht₀ htu) (houter t u ht₀ htu) hz

end Yau.Proofs.C07Aux
