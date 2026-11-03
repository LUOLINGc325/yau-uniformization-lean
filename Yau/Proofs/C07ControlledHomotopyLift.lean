import Yau.Proofs.C07PolygonalPrefix
import Yau.Proofs.C07HomotopyFromPrefixes
import Yau.Proofs.C07CompactHomotopyLift
import Yau.LeafProofs.L12

/-! Every original continuous based square has one actual late-time joint lift. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

theorem eventually_continuous_homotopy_lift
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    (H : C(unitInterval × unitInterval, Pt X)) (hzero : ∀ s, H (0, s) = o) :
    ∃ T : ℝ, t₀ ≤ T ∧ ∀ t, T ≤ t →
      ∃ E : unitInterval × unitInterval → ComplexVector n,
        Continuous E ∧ (∀ s, E (0, s) = 0) ∧
        ∀ p, E p ∈ Metric.ball 0 r ∧ Φ t (E p) = H p := by
  have hg : MetricSmooth X.metric.form :=
    Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  apply eventually_joint_lift_of_local_parameter Φ H
    (fun t ht => (hcharts t ht).1)
  intro s
  obtain ⟨N, hN, hsN, K, L, hK, _, γ, Q, hQ, hlength, htrace, hbase⟩ :=
    C07PolygonalPrefixAux.exists_local_polygonal_prefix hg o H hzero s
  obtain ⟨a, B, T, _, _, _, hlift⟩ :=
    eventually_homotopy_lift_from_prefixes hflow hwindow hr hc Φ hcharts H N
      γ Q (fun p => hQ p.1 p.2) hK htrace L hlength hbase
  refine ⟨N, hN, hsN, T, ?_⟩
  intro t ht
  obtain ⟨E, hE, hE₀, hEp, _⟩ := hlift t ht
  exact ⟨E, hE, hE₀, hEp⟩

end Yau.Proofs.C07Aux
