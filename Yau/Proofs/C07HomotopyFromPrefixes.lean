import Yau.Proofs.C07ParametricDecayLift
import Yau.Proofs.C07LiftUniqueness

/-! Uniformly controlled polygonal prefixes lift the original continuous homotopy. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

theorem eventually_homotopy_lift_from_prefixes
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    (H : C(unitInterval × unitInterval, Pt X)) (N : Set unitInterval)
    (γ : ∀ a : unitInterval × N, IntegrableCurve X.metric.form o (H (a.1, a.2.1)))
    (Q : C(unitInterval × (unitInterval × N), Pt X))
    (hQ : ∀ p, Q p = (γ p.2).1 p.1)
    {K : Set (Pt X)} (hK : IsCompact K)
    (htrace : ∀ a, ∀ u ∈ Icc (0 : ℝ) 1, (γ a).1 u ∈ K)
    (L : ℝ) (hlength : ∀ a, curveLength X.metric.form (γ a).1 ≤ L)
    (hzero : ∀ s : N, ∀ u ∈ Icc (0 : ℝ) 1, (γ ((0 : unitInterval), s)).1 u = o) :
    ∃ a B T : ℝ, 0 < a ∧ 0 ≤ B ∧ t₀ ≤ T ∧
      ∀ t, T ≤ t → ∃ E : unitInterval × N → ComplexVector n,
        Continuous E ∧ (∀ s, E (0, s) = 0) ∧
        (∀ p, E p ∈ Metric.ball 0 r ∧ Φ t (E p) = H (p.1, p.2.1)) ∧
        ∀ p, ‖E p‖ ≤ B * Real.exp (-a * ρ o t) := by
  obtain ⟨a, B, T, ha, hB, hT, hlift⟩ := eventually_joint_lift_of_compact_decay
    hflow hwindow hr hc Φ hcharts γ Q hQ hK htrace L hlength
  refine ⟨a, B, T, ha, hB, hT, ?_⟩
  intro t ht
  obtain ⟨Ξ, hΞ, hΞ₀, hΞp, hΞnorm⟩ := hlift t ht
  let E : unitInterval × N → ComplexVector n := fun p => Ξ (1, p)
  have hmap : Continuous (fun p : unitInterval × N => ((1 : unitInterval), p)) :=
    continuous_const.prodMk continuous_id
  have hEc : Continuous E := hΞ.comp hmap
  have hE₀ (s : N) : E (0, s) = 0 := by
    let z : unitInterval × N := (0, s)
    have hc' : Continuous (fun u : unitInterval => Ξ (u, z)) :=
      hΞ.comp (continuous_id.prodMk continuous_const)
    have hcomp : Φ t ∘ (fun u : unitInterval => Ξ (u, z)) = Φ t ∘ (fun _ => 0) := by
      funext u
      exact (hΞp (u, z)).2.trans ((hQ (u, z)).trans
        ((hzero s u u.2).trans (hcharts t (hT.trans ht)).2.1.symm))
    have heq := chart_lifts_unique (hcharts t (hT.trans ht)).1 hc' continuous_const
      (fun u => (hΞp (u, z)).1) (fun _ => Metric.mem_ball_self hr) hcomp
      (0 : unitInterval) (hΞ₀ z)
    exact congrFun heq 1
  refine ⟨E, hEc, hE₀, ?_, fun p => hΞnorm (1, p)⟩
  intro p
  have hQ₁ : Q (1, p) = (γ p).1 1 := by simpa using hQ (1, p)
  exact ⟨(hΞp (1, p)).1, (hΞp (1, p)).2.trans (hQ₁.trans (γ p).1.finish_eq)⟩

end Yau.Proofs.C07Aux
