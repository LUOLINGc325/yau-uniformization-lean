import Yau.Proofs.C07Charts
import Yau.Proofs.C07TransitionFamily
import Yau.Proofs.C07ExhaustingInverse
import Yau.Proofs.C07CommonExponent
import Yau.Proofs.C07InverseTransitionDecay
import Yau.Proofs.C07TransitionEstimates
import Yau.Proofs.C07TinyImage
import Yau.Proofs.G02GluedVolume

/-! Original C07, using only the original predecessor contracts actually needed. -/

open scoped Manifold Topology
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

set_option maxHeartbeats 1600000 in
theorem C07_of_original_predecessors
    (hC02 : C02) (hC04 : C04) (hC05 : C05) (hC06 : C06) (hE03 : E03) : C07 := by
  intro n X o h U P ρ hflow
  have hwindow : RicciWindows X o h ρ := hC04 n X o h U P ρ hflow.1
  have hjoint : JointPositivity X h := hE03 n X o h U P ρ hflow.1
  have hsimply : SimplyConnectedSpace (Pt X) := hC05 n X
  obtain ⟨r, C, tc, Φ, hr, hC, hcharts₀⟩ :=
    centered_chart_family o h (hC02 n X o h U P ρ hflow.1)
  let t₀ := max 0 tc
  have ht₀ : 0 ≤ t₀ := le_max_left _ _
  have hcharts (t : ℝ) (ht : t₀ ≤ t) : UnitaryChart (h t) o (Φ t) r C⁻¹ C :=
    hcharts₀ t ((le_max_right _ _).trans ht)
  obtain ⟨R, Cb, F, hR, hRr, hF, hFproj, hFcomp⟩ :=
    transition_family_of_unitaryCharts hflow hjoint hr hC ht₀ Φ hcharts
  have hFsimple (t u : ℝ) (ht : t₀ ≤ t) (htu : t ≤ u) :
      ContinuousOn (F t u) (Metric.ball 0 R) ∧
      (∀ z ∈ Metric.ball 0 R, F t u z ∈ Metric.ball 0 r ∧ Φ u (F t u z) = Φ t z) ∧
      F t u 0 = 0 :=
    ⟨(hF t u ht htu).1.continuousOn, hFproj t u ht htu, (hF t u ht htu).2.2.1⟩
  obtain ⟨Ω, f, S, hS, hopen, hmono, hexhaust, hf, hp, hzero, hcoherence, hlocal⟩ :=
    exists_exhausting_inverse hflow hwindow hsimply hr hR hRr.le (inv_pos.mpr hC)
      Φ hcharts F hFsimple
  have hg : MetricSmooth X.metric.form :=
    Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form hg
  have hexhaust' (K : Set (Pt X)) (hK : IsCompact K) :
      ∃ T : ℝ, ∀ t, T ≤ t → K ⊆ Ω t := by
    obtain ⟨T, _, hT⟩ := hexhaust K hK
    exact ⟨T, hT⟩
  obtain ⟨σ, hσ, hdecay⟩ := common_exponent_of_local_decay X X.metric.form hg μ hμ
    (hC06 n X) Ω f (ρ o) hwindow.2.2.1 S R hR
    (fun t _ => hopen t) (fun _ _ _ _ htu => hmono htu) hexhaust'
    (fun t _ => hf t)
    (fun t _ x hx => le_of_lt (by
      simpa only [Metric.mem_ball, dist_zero_right] using (hp t x hx).1)) hlocal
  obtain ⟨K₀, hK₀, β, Ttiny, hβ, _, htiny⟩ :=
    C07TinyImageAux.exists_eventual_tiny_image hflow hwindow hr hC Φ hcharts
  obtain ⟨Tinner, hTS, hinner⟩ := transition_inner_decay_of_inverse Φ F Ω f (ρ o) hr hRr.le
    hwindow.2.2.1 (fun t ht => (hcharts t (hS.trans ht)).1)
    (fun t => (hf t).continuousOn) hp
    (fun t ht => by rw [(hcharts t (hS.trans ht)).2.1]; exact hzero t)
    hcoherence K₀ (hexhaust' K₀ hK₀) (hdecay K₀ hK₀) hβ ⟨Ttiny, htiny⟩
  obtain ⟨t₁, _, hstrict, _, _⟩ := hwindow.1
  let Tfinal := max Tinner t₁
  have hfinalS : S ≤ Tfinal := hTS.trans (le_max_left _ _)
  have hfinalchart : t₀ ≤ Tfinal := hS.trans hfinalS
  have hclockmono : MonotoneOn (ρ o) (Ici Tfinal) := by
    intro t ht u hu htu
    have htt : t₁ ≤ t := (show t₁ ≤ Tfinal from le_max_right _ _).trans ht
    have hut : t₁ ≤ u := (show t₁ ≤ Tfinal from le_max_right _ _).trans hu
    exact hstrict.monotoneOn htt hut htu
  obtain ⟨hjets, hsmall⟩ := transition_full_decay_estimates hR hβ hσ hwindow.2.2.1 hclockmono
    (fun t u ht htu => (hF t u (hfinalchart.trans ht) htu).1)
    (fun t u ht htu z hz => ((hF t u (hfinalchart.trans ht) htu).2.1 z hz).2)
    (fun t u ht htu => hinner t u ((le_max_left _ _).trans ht) htu)
  refine ⟨r, R, σ, C, Cb, Tfinal, Φ, F, f, hR, hRr, hσ, hC,
    (fun t ht => hcharts t (hfinalchart.trans ht)),
    (fun t u ht htu => hF t u (hfinalchart.trans ht) htu),
    (fun t u v ht htu huv => hFcomp t u v (hfinalchart.trans ht) htu huv),
    (fun t _ => hzero t), ?_, hdecay, hjets, hsmall⟩
  intro K hK
  obtain ⟨T, _, hT⟩ := hexhaust K hK
  refine ⟨max Tfinal T, le_max_left _ _, ?_⟩
  intro t ht
  have htfinal : Tfinal ≤ t := (le_max_left _ _).trans ht
  refine ⟨Ω t, hopen t, hT t ((le_max_right _ _).trans ht), hf t, ?_⟩
  intro x hx
  refine ⟨Metric.ball_subset_ball hRr.le (hp t x hx).1, (hp t x hx).2, ?_⟩
  intro u htu _
  exact hcoherence t u (hfinalS.trans htfinal) htu hx

end Yau.Proofs.C07Aux
