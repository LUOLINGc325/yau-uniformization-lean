import Yau.Proofs.C07ControlledHomotopyLift
import Yau.Proofs.C07CurveHomotopy
import Yau.Proofs.C07PathMonodromy

/-! Original simple connectivity makes the endpoints of the same late chart lifts agree. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

theorem eventually_curve_lifts_endpoint_eq
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    (hsimply : SimplyConnectedSpace (Pt X))
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    {x : Pt X} (γ η : PiecewiseC1Curve o x) :
    ∃ T : ℝ, t₀ ≤ T ∧ ∀ t, T ≤ t →
      ∀ Γ₀ Γ₁ : unitInterval → ComplexVector n,
      Continuous Γ₀ → Continuous Γ₁ →
      (∀ u, Γ₀ u ∈ Metric.ball 0 r) → (∀ u, Γ₁ u ∈ Metric.ball 0 r) →
      (∀ u, Φ t (Γ₀ u) = γ u) → (∀ u, Φ t (Γ₁ u) = η u) →
      Γ₀ 0 = 0 → Γ₁ 0 = 0 → Γ₀ 1 = Γ₁ 1 := by
  obtain ⟨H, hH₀, hH₁, hHγ, hHη⟩ := curve_homotopy_square hsimply γ η
  obtain ⟨T, hT, hlift⟩ :=
    eventually_continuous_homotopy_lift hflow hwindow hr hc Φ hcharts H hH₀
  refine ⟨T, hT, ?_⟩
  intro t ht Γ₀ Γ₁ hΓ₀ hΓ₁ hΓ₀ball hΓ₁ball hΓ₀proj hΓ₁proj hΓ₀zero hΓ₁zero
  obtain ⟨E, hE, hE₀, hEp⟩ := hlift t ht
  exact homotopy_boundary_lifts_endpoint_eq (hcharts t (hT.trans ht)).1 H E hE hE₀
    (fun p => (hEp p).1) (fun p => (hEp p).2)
    (fun s => (hH₁ s).trans (hH₁ 0).symm)
    Γ₀ Γ₁ hΓ₀ hΓ₁ hΓ₀ball hΓ₁ball
    (fun u => (hΓ₀proj u).trans (hHγ u).symm)
    (fun u => (hΓ₁proj u).trans (hHη u).symm) hΓ₀zero hΓ₁zero

end Yau.Proofs.C07Aux
