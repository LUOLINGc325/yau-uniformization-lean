import Yau.Proofs.C07ChartBallCurveFamily
import Yau.Proofs.C07ParametricDecayLift
import Yau.Proofs.C07InverseCompatibility

/-! Local branches are the endpoints of lifts of the same actual chart-curve family. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set Yau.Proofs.D04AtlasGlueAux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

theorem eventually_chartBall_lifts
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    (B : ChartBall X.manifold) :
    ∃ γ : ∀ x : B.outer, IntegrableCurve X.metric.form o x,
      ∃ a A T : ℝ, 0 < a ∧ 0 ≤ A ∧ t₀ ≤ T ∧
      ∀ t, T ≤ t → ∃ E : unitInterval × B.outer → ComplexVector n,
        Continuous E ∧ (∀ x, E (0, x) = 0) ∧
        (∀ p, E p ∈ Metric.ball 0 r ∧ Φ t (E p) = (γ p.2).1 p.1) ∧
        ∀ p, ‖E p‖ ≤ A * Real.exp (-a * ρ o t) := by
  obtain ⟨K, L, γ, H, hK, _, hH, hlength, htrace⟩ :=
    exists_chartBall_curve_family X.metric o B
  obtain ⟨a, A, T, ha, hA, hT, hlift⟩ :=
    eventually_joint_lift_of_compact_decay hflow hwindow hr hc Φ hcharts
      γ H hH hK htrace L hlength
  refine ⟨γ, a, A, T, ha, hA, hT, ?_⟩
  intro t ht
  obtain ⟨E, hE, hE₀, hEp, hEnorm⟩ := hlift t ht
  exact ⟨E, hE, hE₀, fun p => ⟨(hEp p).1, (hEp p).2.trans (hH p)⟩, hEnorm⟩

variable {M : ComplexManifold n}

def chartBallLiftEnd (B : ChartBall M) (E : unitInterval × B.outer → ComplexVector n)
    (x : M.Carrier) : ComplexVector n := by
  classical
  exact if hx : x ∈ B.outer then E (1, ⟨x, hx⟩) else 0

theorem chartBallLiftEnd_eq (B : ChartBall M)
    (E : unitInterval × B.outer → ComplexVector n) {x : M.Carrier} (hx : x ∈ B.outer) :
    chartBallLiftEnd B E x = E (1, ⟨x, hx⟩) := by
  classical
  exact dif_pos hx

theorem chartBallLiftEnd_continuousOn (B : ChartBall M)
    (E : unitInterval × B.outer → ComplexVector n) (hE : Continuous E) :
    ContinuousOn (chartBallLiftEnd B E) B.outer := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (hE.comp (continuous_const.prodMk continuous_id)).congr
    fun x => (chartBallLiftEnd_eq B E x.2).symm

theorem chartBallLiftEnd_point (B : ChartBall M)
    {k : HermitianField M} {o : M.Carrier}
    (γ : ∀ x : B.outer, IntegrableCurve k o x)
    (E : unitInterval × B.outer → ComplexVector n)
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hp : ∀ p, E p ∈ Metric.ball 0 r ∧ Φ (E p) = (γ p.2).1 p.1)
    {x : M.Carrier} (hx : x ∈ B.outer) :
    chartBallLiftEnd B E x ∈ Metric.ball 0 r ∧ Φ (chartBallLiftEnd B E x) = x := by
  rw [chartBallLiftEnd_eq B E hx]
  exact ⟨(hp (1, ⟨x, hx⟩)).1, (hp (1, ⟨x, hx⟩)).2.trans (γ ⟨x, hx⟩).1.finish_eq⟩

theorem chartBallLiftEnd_mdifferentiable (B : ChartBall M)
    {k : HermitianField M} {o : M.Carrier}
    (γ : ∀ x : B.outer, IntegrableCurve k o x)
    (E : unitInterval × B.outer → ComplexVector n) (hE : Continuous E)
    {Φ : ComplexVector n → M.Carrier} {r : ℝ} (hΦ : IsLocalBiholomorphism Φ r)
    (hp : ∀ p, E p ∈ Metric.ball 0 r ∧ Φ (E p) = (γ p.2).1 p.1) :
    MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) (chartBallLiftEnd B E) B.outer :=
  continuous_manifold_inverse_mdifferentiable hΦ B.isOpen_outer
    (chartBallLiftEnd_continuousOn B E hE)
    (fun _ hx => (chartBallLiftEnd_point B γ E hp hx).1)
    (fun _ hx => (chartBallLiftEnd_point B γ E hp hx).2)

end Yau.Proofs.C07Aux
