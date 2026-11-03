import Yau.Proofs.C07TransitionLift
import Yau.Proofs.C07TransitionHolomorphic
import Yau.Proofs.C07TransitionRadius
import Yau.Proofs.C07CompositionGerm
import Yau.Proofs.C07FlowSmooth
import Yau.Proofs.C07CenterEstimates

/-! Whole-ball transition maps for the same physical-time unitary chart family. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem transition_family_of_unitaryCharts {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X} (hflow : FlowStage X o h U P ρ)
    (hjoint : JointPositivity X h) {r C t₀ : ℝ}
    (hr : 0 < r) (hC : 0 < C) (ht₀ : 0 ≤ t₀)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r C⁻¹ C) :
    ∃ R Cb : ℝ, ∃ F : ℝ → ℝ → ComplexVector n → ComplexVector n,
      0 < R ∧ R < r ∧
      (∀ t u, t₀ ≤ t → t ≤ u →
        DifferentiableOn ℂ (F t u) (Metric.ball 0 R) ∧
        (∀ z ∈ Metric.ball (0 : ComplexVector n) R,
          Function.Bijective (fderiv ℂ (F t u) z) ∧ ‖F t u z‖ ≤ Cb) ∧
        F t u 0 = 0 ∧ (∀ᶠ z in 𝓝 0, Φ u (F t u z) = Φ t z) ∧
        ‖fderiv ℂ (F t u) 0‖ ≤ 1 ∧
        ‖LinearMap.det (fderiv ℂ (F t u) 0).toLinearMap‖ =
          Real.exp (-(ρ o u - ρ o t) / 2) ∧
        ‖(fderiv ℂ (F t u) 0).inverse‖ ≤ Real.exp ((ρ o u - ρ o t) / 2)) ∧
      (∀ t u, t₀ ≤ t → t ≤ u → ∀ z ∈ Metric.ball (0 : ComplexVector n) R,
        F t u z ∈ Metric.ball 0 r ∧ Φ u (F t u z) = Φ t z) ∧
      (∀ t u v, t₀ ≤ t → t ≤ u → u ≤ v →
        ∀ᶠ z in 𝓝 0, F u v (F t u z) = F t v z) := by
  classical
  obtain ⟨R, hR, hRr, hshort⟩ := exists_transition_radius hr (inv_pos.mpr hC) hC
  let α : ℝ := (Real.sqrt (2 * C⁻¹))⁻¹ * Real.sqrt (2 * C)
  have hα : 0 ≤ α := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hex (t u : ℝ) : ∃ f : ComplexVector n → ComplexVector n,
      t₀ ≤ t → t ≤ u →
      ContinuousOn f (Metric.ball 0 R) ∧ f 0 = 0 ∧
      ∀ z ∈ Metric.ball 0 R, f z ∈ Metric.ball 0 r ∧ Φ u (f z) = Φ t z ∧
        ‖f z‖ ≤ α * ‖z‖ := by
    by_cases ht : t₀ ≤ t ∧ t ≤ u
    · obtain ⟨f, hf⟩ := exists_continuous_transition
        (flow_metricSmooth hflow (ht₀.trans (ht.1.trans ht.2)))
        (fun x => joint_metric_antitone hflow hjoint x (ht₀.trans ht.1) ht.2)
        hr hR hRr.le (inv_pos.mpr hC) hC (hcharts t ht.1)
        (hcharts u (ht.1.trans ht.2)) hshort
      exact ⟨f, fun _ _ => hf⟩
    · exact ⟨fun _ => 0, fun ht' htu => False.elim (ht ⟨ht', htu⟩)⟩
  choose F hF using hex
  have hproj (t u : ℝ) (ht : t₀ ≤ t) (htu : t ≤ u) :
      ∀ᶠ z in 𝓝 0, Φ u (F t u z) = Φ t z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ComplexVector n) hR] with z hz
    exact ((hF t u ht htu).2.2 z hz).2.1
  refine ⟨R, α * R, F, hR, hRr, ?_, ?_, ?_⟩
  · intro t u ht htu
    have hf := hF t u ht htu
    obtain ⟨hd, hbij⟩ := continuous_transition_holomorphic
      (hcharts t ht).1 (hcharts u (ht.trans htu)).1 hRr.le hf.1
      (fun z hz => (hf.2.2 z hz).1) (fun z hz => (hf.2.2 z hz).2.1)
    have hcenter := transition_center_estimates hflow hjoint (ht₀.trans ht) htu
      hR hr (hcharts t ht) (hcharts u (ht.trans htu)) hd hf.2.1 (hproj t u ht htu)
    refine ⟨hd, ?_, hf.2.1, hproj t u ht htu, hcenter⟩
    intro z hz
    refine ⟨hbij z hz, (hf.2.2 z hz).2.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hα
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  · intro t u ht htu z hz
    exact ⟨((hF t u ht htu).2.2 z hz).1, ((hF t u ht htu).2.2 z hz).2.1⟩
  · intro t u v ht htu huv
    exact transition_composition_germ hr (hcharts v (ht.trans (htu.trans huv))).1
      ((hF t u ht htu).1.continuousAt (Metric.ball_mem_nhds _ hR))
      ((hF u v (ht.trans htu) huv).1.continuousAt (Metric.ball_mem_nhds _ hR))
      ((hF t v ht (htu.trans huv)).1.continuousAt (Metric.ball_mem_nhds _ hR))
      (hF t u ht htu).2.1 (hF u v (ht.trans htu) huv).2.1
      (hF t v ht (htu.trans huv)).2.1 (hproj t u ht htu)
      (hproj u v (ht.trans htu) huv) (hproj t v ht (htu.trans huv))

end Yau.Proofs.C07Aux
