import Yau.Proofs.C07ChartBallLifts

/-! Fix actual local curve lifts at every physical time without changing their curves. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set Yau.Proofs.D04AtlasGlueAux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

theorem exists_chartBall_lift_family
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    (B : ChartBall X.manifold) :
    ∃ (γ : ∀ x : B.outer, IntegrableCurve X.metric.form o x)
      (a A T : ℝ) (E : ℝ → unitInterval × B.outer → ComplexVector n),
      0 < a ∧ 0 ≤ A ∧ t₀ ≤ T ∧
      ∀ t, T ≤ t → Continuous (E t) ∧ (∀ x, E t (0, x) = 0) ∧
        (∀ p, E t p ∈ Metric.ball 0 r ∧ Φ t (E t p) = (γ p.2).1 p.1) ∧
        ∀ p, ‖E t p‖ ≤ A * Real.exp (-a * ρ o t) := by
  classical
  obtain ⟨γ, a, A, T, ha, hA, hT, hlift⟩ :=
    eventually_chartBall_lifts hflow hwindow hr hc Φ hcharts B
  let E : ℝ → unitInterval × B.outer → ComplexVector n := fun t =>
    if ht : T ≤ t then Classical.choose (hlift t ht) else fun _ => 0
  refine ⟨γ, a, A, T, E, ha, hA, hT, ?_⟩
  intro t ht
  dsimp only [E]
  rw [dif_pos ht]
  exact Classical.choose_spec (hlift t ht)

end Yau.Proofs.C07Aux
