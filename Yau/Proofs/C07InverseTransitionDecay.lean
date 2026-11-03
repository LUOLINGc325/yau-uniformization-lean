import Yau.Proofs.C07ChartInverseIdentity

/-! The actual inverse estimate controls the same transition map on a tiny ball. -/

open scoped Manifold Topology
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem transition_inner_decay_of_inverse
    (Φ : ℝ → ComplexVector n → M.Carrier)
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (Ω : ℝ → Set M.Carrier) (f : ℝ → M.Carrier → ComplexVector n)
    (s : ℝ → ℝ) {r R σ T₀ : ℝ} (hr : 0 < r) (hRr : R ≤ r)
    (hclock : Tendsto s atTop atTop)
    (hΦ : ∀ t, T₀ ≤ t → IsLocalBiholomorphism (Φ t) r)
    (hf : ∀ t, ContinuousOn (f t) (Ω t))
    (hp : ∀ t, ∀ x ∈ Ω t, f t x ∈ Metric.ball 0 R ∧ Φ t (f t x) = x)
    (hzero : ∀ t, T₀ ≤ t → f t (Φ t 0) = 0)
    (hcoherence : ∀ t u, T₀ ≤ t → t ≤ u → EqOn (f u) (F t u ∘ f t) (Ω t))
    (K : Set M.Carrier)
    (hexhaust : ∃ T : ℝ, ∀ t, T ≤ t → K ⊆ Ω t)
    (hdecay : ∃ T : ℝ, ∀ t, T ≤ t → ∀ x ∈ K, ‖f t x‖ ≤ Real.exp (-σ * s t))
    {β : ℝ} (hβ : 0 < β)
    (htiny : ∃ T : ℝ, ∀ t, T ≤ t → ∀ z : ComplexVector n,
      ‖z‖ ≤ Real.exp (-β * s t) → Φ t z ∈ K) :
    ∃ T : ℝ, T₀ ≤ T ∧ ∀ t u, T ≤ t → t ≤ u → ∀ z : ComplexVector n,
      ‖z‖ ≤ Real.exp (-β * s t) → ‖F t u z‖ ≤ Real.exp (-σ * s u) := by
  obtain ⟨TΩ, hTΩ⟩ := hexhaust
  obtain ⟨Tdecay, hTdecay⟩ := hdecay
  obtain ⟨Ttiny, hTtiny⟩ := htiny
  have hlim : Tendsto (fun t => Real.exp (-β * s t)) atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hβ hclock)
  obtain ⟨Tsmall, hTsmall⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hr))
  let T := max T₀ (max TΩ (max Tdecay (max Ttiny Tsmall)))
  have hT₀ : T₀ ≤ T := le_max_left _ _
  have hTΩ' : TΩ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTd : Tdecay ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hTt : Ttiny ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hTs : Tsmall ≤ T := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨T, hT₀, ?_⟩
  intro t u ht htu z hz
  have hmaps : MapsTo (Φ t) (Metric.closedBall 0 (Real.exp (-β * s t))) (Ω t) := by
    intro w hw
    apply hTΩ t (hTΩ'.trans ht)
    apply hTtiny t (hTt.trans ht)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have hid := inverse_comp_chart_eq_on_closedBall (hΦ t (hT₀.trans ht))
    (Real.exp_pos _).le (hTsmall t (hTs.trans ht)) (hf t)
    (fun x hx => ⟨Metric.ball_subset_ball hRr (hp t x hx).1, (hp t x hx).2⟩)
    (hzero t (hT₀.trans ht)) hmaps
  have hzball : z ∈ Metric.closedBall (0 : ComplexVector n) (Real.exp (-β * s t)) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hzt : Φ t z ∈ K := hTtiny t (hTt.trans ht) z hz
  have heq := hcoherence t u (hT₀.trans ht) htu (hTΩ t (hTΩ'.trans ht) hzt)
  have hfz : f t (Φ t z) = z := hid hzball
  change f u (Φ t z) = F t u (f t (Φ t z)) at heq
  rw [hfz] at heq
  rw [← heq]
  exact hTdecay u ((hTd.trans ht).trans htu) _ hzt

end Yau.Proofs.C07Aux
