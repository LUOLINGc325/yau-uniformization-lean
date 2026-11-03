import Yau.Proofs.C07PshScaling

open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

/-- Extended logarithmic norm inequalities retain their usual exponential
meaning at a zero of the vector as well. -/
theorem log_norm_le_real_iff {G : Type*} [NormedAddCommGroup G] (w : G) (b : ℝ) :
    ENNReal.log (ENNReal.ofReal ‖w‖) ≤ (b : EReal) ↔ ‖w‖ ≤ Real.exp b := by
  have he : ENNReal.log (ENNReal.ofReal (Real.exp b)) = (b : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos b), Real.log_exp]
  rw [← he, ENNReal.log_le_log_iff, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos b).le]

theorem normalized_logNorm_le_real_iff {G : Type*} [NormedAddCommGroup G]
    (w : G) {s : ℝ} (hs : 0 < s) (b : ℝ) :
    ((s⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖w‖) ≤ (b : EReal) ↔
      ‖w‖ ≤ Real.exp (b * s) := by
  rw [positive_scale_le_real_iff (inv_pos.mpr hs), div_inv_eq_mul, log_norm_le_real_iff]

/-- The compact-dependent prefactor in a local decay estimate is absorbed
by halving its exponent, along the same volume clock. -/
theorem eventual_pure_exponential {A G : Type*} [NormedAddCommGroup G]
    (f : ℝ → A → G) (K : Set A) {s : ℝ → ℝ} (hclock : Tendsto s atTop atTop)
    {a C T : ℝ} (ha : 0 < a)
    (hdecay : ∀ t, T ≤ t → ∀ x ∈ K, ‖f t x‖ ≤ C * Real.exp (-a * s t)) :
    ∃ T' : ℝ, ∀ t, T' ≤ t → ∀ x ∈ K,
      ‖f t x‖ ≤ Real.exp (-(a / 2) * s t) := by
  let B := max 1 C
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (hclock.eventually (eventually_ge_atTop (2 * Real.log B / a)))
  refine ⟨max T T₁, ?_⟩
  intro t ht x hx
  have hst := (div_le_iff₀ ha).mp (hT₁ t ((le_max_right _ _).trans ht))
  have hBexp : B ≤ Real.exp ((a / 2) * s t) := by
    rw [← Real.exp_log hB]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    ‖f t x‖ ≤ C * Real.exp (-a * s t) := hdecay t ((le_max_left _ _).trans ht) x hx
    _ ≤ B * Real.exp (-a * s t) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    _ ≤ Real.exp ((a / 2) * s t) * Real.exp (-a * s t) :=
      mul_le_mul_of_nonneg_right hBexp (Real.exp_pos _).le
    _ = Real.exp (-(a / 2) * s t) := by rw [← Real.exp_add]; congr 1; ring

end Yau.Proofs.C07Aux
