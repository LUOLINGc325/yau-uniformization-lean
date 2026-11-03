import Yau.Proofs.C07ConnectedExhaustion
import Yau.Proofs.C07CompactInverse
import Yau.Proofs.C07SelectedInverseCoherence

/-! Select one actual inverse at each physical time on a connected exhaustion. -/

open scoped Manifold Topology
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

set_option maxHeartbeats 1200000 in
theorem exists_exhausting_inverse
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    (hsimply : SimplyConnectedSpace (Pt X))
    {r R c C t₀ : ℝ} (hr : 0 < r) (hR : 0 < R) (hRr : R ≤ r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (hF : ∀ t u, t₀ ≤ t → t ≤ u →
      ContinuousOn (F t u) (Metric.ball 0 R) ∧
      (∀ z ∈ Metric.ball 0 R, F t u z ∈ Metric.ball 0 r ∧ Φ u (F t u z) = Φ t z) ∧
      F t u 0 = 0) :
    ∃ (Ω : ℝ → Set (Pt X)) (f : ℝ → Pt X → ComplexVector n) (S : ℝ),
      t₀ ≤ S ∧ (∀ t, IsOpen (Ω t)) ∧ Monotone Ω ∧
      (∀ K : Set (Pt X), IsCompact K → ∃ T : ℝ, S ≤ T ∧ ∀ t, T ≤ t → K ⊆ Ω t) ∧
      (∀ t, MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) (f t) (Ω t)) ∧
      (∀ t, ∀ x ∈ Ω t, f t x ∈ Metric.ball 0 R ∧ Φ t (f t x) = x) ∧
      (∀ t, f t o = 0) ∧
      (∀ t u, S ≤ t → t ≤ u → EqOn (f u) (F t u ∘ f t) (Ω t)) ∧
      ∀ K : Set (Pt X), IsCompact K → ∃ a A T : ℝ, 0 < a ∧
        ∀ t, T ≤ t → ∀ x ∈ K, ‖f t x‖ ≤ A * Real.exp (-a * ρ o t) := by
  classical
  obtain ⟨V, hV, hstep, hcover⟩ :=
    C07ConnectedExhaustionAux.exists_connected_exhaustion (M := X.manifold) o
  have hVmono : Monotone V := monotone_nat_of_le_succ (fun j => subset_closure.trans (hstep j))
  choose W b a A S hWo hVW hoW ha hA hS hdata using
    (fun j => eventually_inverse_near_compact hflow hwindow hsimply hr hc Φ hcharts (hV j).2.2.1)
  have hsmall : ∀ j : ℕ, ∃ T : ℝ, ∀ t, T ≤ t → A j * Real.exp (-a j * ρ o t) < R := by
    intro j
    have hz : Tendsto (fun t => A j * Real.exp (-a j * ρ o t)) atTop (nhds 0) := by
      have hz := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.const_mul_atTop (ha j) hwindow.2.2.1)).const_mul (A j)
      simpa only [Function.comp_def, mul_zero, neg_mul] using hz
    exact eventually_atTop.mp (hz.eventually (Iio_mem_nhds hR))
  choose Q hQ using hsmall
  let T : ℕ → ℝ := fun j => max (j : ℝ) (max (S j) (Q j))
  have hmajor (j : ℕ) : (j : ℝ) ≤ T j := le_max_left _ _
  have hST (j : ℕ) : S j ≤ T j := (le_max_left _ _).trans (le_max_right _ _)
  have hQT (j : ℕ) : Q j ≤ T j := (le_max_right _ _).trans (le_max_right _ _)
  have hTchart (j : ℕ) : t₀ ≤ T j := (hS j).trans (hST j)
  have hVU (j : ℕ) : V j ⊆ W j := subset_closure.trans (hVW j)
  have hbc (j : ℕ) (t : ℝ) (ht : T j ≤ t) : ContinuousOn (b j t) (V j) :=
    ((hdata j t ((hST j).trans ht)).1).mono (hVU j)
  have hbp (j : ℕ) (t : ℝ) (ht : T j ≤ t) (x : Pt X) (hx : x ∈ V j) :
      b j t x ∈ Metric.ball 0 R ∧ Φ t (b j t x) = x := by
    have hp := (hdata j t ((hST j).trans ht)).2.2.2 x (hVU j hx)
    refine ⟨?_, hp.2.1⟩
    simpa only [Metric.mem_ball, dist_zero_right] using
      (hp.2.2.trans_lt (hQ j t ((hQT j).trans ht)))
  have hbzero (j : ℕ) (t : ℝ) (ht : T j ≤ t) : b j t o = 0 :=
    (hdata j t ((hST j).trans ht)).2.2.1
  let Ω := selectedInverseDomain V T
  let f := selectedInverse V T b
  refine ⟨Ω, f, T 0, hTchart 0, selectedInverseDomain_open V T (fun j => (hV j).1),
    selectedInverseDomain_monotone V T hVmono,
    selectedInverseDomain_exhausts V T hVmono hmajor hcover,
    selectedInverse_mdifferentiable V T b Φ hRr (fun j => (hV j).1) hTchart
      (fun t ht => (hcharts t ht).1) hbc hbp,
    (fun t x hx => selectedInverse_point V T b Φ R hbp t hx),
    selectedInverse_zero V T b o (fun j => (hV j).2.2.2) hbzero, ?_, ?_⟩
  · intro t u ht htu
    have htchart : t₀ ≤ t := (hTchart 0).trans ht
    have hFu := hF t u htchart htu
    exact selectedInverse_transition_coherence V T b Φ hRr hVmono
      (fun j => (hV j).2.1) (fun j => (hV j).2.2.2) hbc hbp hbzero ht htu
      (hcharts u (htchart.trans htu)).1 (F t u) hFu.1
      (fun z hz => (hFu.2.1 z hz).1) (fun z hz => (hFu.2.1 z hz).2) hFu.2.2
  · intro K hK
    obtain ⟨j, hj⟩ := hcover K hK
    refine ⟨a j, A j, max (T 0) (T j), ha j, ?_⟩
    intro t ht x hx
    have ht₀ : T 0 ≤ t := (le_max_left _ _).trans ht
    have htj : T j ≤ t := (le_max_right _ _).trans ht
    have heq := selectedInverse_branch_agreement V T b Φ hRr hVmono
      (fun j => (hV j).2.1) (fun j => (hV j).2.2.2) hmajor hbc hbp hbzero ht₀ htj
      (hcharts t ((hTchart 0).trans ht₀)).1
    change ‖selectedInverse V T b t x‖ ≤ _
    rw [heq (hj hx)]
    exact ((hdata j t ((hST j).trans htj)).2.2.2 x (hVU j (hj hx))).2.2

end Yau.Proofs.C07Aux
