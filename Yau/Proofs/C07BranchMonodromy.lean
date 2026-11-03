import Yau.Proofs.C07EventualMonodromy
import Yau.Proofs.C07ChartBallLifts

/-! The actual local branches agree pointwise eventually, including zero at the base point. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set Yau.Proofs.D04AtlasGlueAux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

theorem eventually_chartBall_endpoint_agreement
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    (hsimply : SimplyConnectedSpace (Pt X))
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    (B D : ChartBall X.manifold)
    (γ : ∀ x : B.outer, IntegrableCurve X.metric.form o x)
    (η : ∀ x : D.outer, IntegrableCurve X.metric.form o x)
    (E : ℝ → unitInterval × B.outer → ComplexVector n)
    (F : ℝ → unitInterval × D.outer → ComplexVector n) (T₁ T₂ : ℝ)
    (hE : ∀ t, T₁ ≤ t → Continuous (E t) ∧ (∀ x, E t (0, x) = 0) ∧
      ∀ p, E t p ∈ Metric.ball 0 r ∧ Φ t (E t p) = (γ p.2).1 p.1)
    (hF : ∀ t, T₂ ≤ t → Continuous (F t) ∧ (∀ x, F t (0, x) = 0) ∧
      ∀ p, F t p ∈ Metric.ball 0 r ∧ Φ t (F t p) = (η p.2).1 p.1)
    {x : Pt X} (hxB : x ∈ B.outer) (hxD : x ∈ D.outer) :
    ∃ T : ℝ, ∀ t, T ≤ t → chartBallLiftEnd B (E t) x = chartBallLiftEnd D (F t) x := by
  obtain ⟨S, _, hS⟩ := eventually_curve_lifts_endpoint_eq hflow hwindow hsimply hr hc
    Φ hcharts (γ ⟨x, hxB⟩).1 (η ⟨x, hxD⟩).1
  refine ⟨max S (max T₁ T₂), ?_⟩
  intro t ht
  have htS : S ≤ t := (le_max_left _ _).trans ht
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht₂ : T₂ ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  obtain ⟨hEc, hE₀, hEp⟩ := hE t ht₁
  obtain ⟨hFc, hF₀, hFp⟩ := hF t ht₂
  rw [chartBallLiftEnd_eq B (E t) hxB, chartBallLiftEnd_eq D (F t) hxD]
  exact hS t htS (fun u => E t (u, ⟨x, hxB⟩)) (fun u => F t (u, ⟨x, hxD⟩))
    (hEc.comp (continuous_id.prodMk continuous_const))
    (hFc.comp (continuous_id.prodMk continuous_const))
    (fun u => (hEp (u, ⟨x, hxB⟩)).1) (fun u => (hFp (u, ⟨x, hxD⟩)).1)
    (fun u => (hEp (u, ⟨x, hxB⟩)).2) (fun u => (hFp (u, ⟨x, hxD⟩)).2)
    (hE₀ _) (hF₀ _)

theorem eventually_based_loop_lift_zero
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    (hsimply : SimplyConnectedSpace (Pt X))
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    (γ : PiecewiseC1Curve o o) :
    ∃ T : ℝ, t₀ ≤ T ∧ ∀ t, T ≤ t →
      ∀ Γ : unitInterval → ComplexVector n, Continuous Γ →
      (∀ u, Γ u ∈ Metric.ball 0 r) → (∀ u, Φ t (Γ u) = γ u) →
      Γ 0 = 0 → Γ 1 = 0 := by
  obtain ⟨T, hT, hlate⟩ := eventually_curve_lifts_endpoint_eq hflow hwindow hsimply hr hc
    Φ hcharts γ (C07PolygonalPrefixAux.constantPiecewise o)
  refine ⟨T, hT, ?_⟩
  intro t ht Γ hΓ hΓball hΓproj hΓ₀
  exact hlate t ht Γ (fun _ => 0) hΓ continuous_const hΓball
    (fun _ => Metric.mem_ball_self hr) hΓproj
    (fun _ => (hcharts t (hT.trans ht)).2.1) hΓ₀ rfl

end Yau.Proofs.C07Aux
