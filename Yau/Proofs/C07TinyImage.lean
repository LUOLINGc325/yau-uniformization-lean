import Yau.Proofs.C07TinyImageMetric
import Yau.Proofs.C07FlowSmooth
import Yau.Proofs.C07ChartBallMaps

open scoped Manifold Topology ContDiff unitInterval

noncomputable section

namespace Yau.Proofs.C07TinyImageAux

open Yau Yau.Blueprint Set Filter
open C07Aux D04AtlasGlueAux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

/-- For the same flow charts and the same volume clock, exponentially tiny
coordinate balls eventually have image in one fixed compact chart core. -/
theorem exists_eventual_tiny_image (hflow : FlowStage X o h U P ρ)
    (hwindow : RicciWindows X o h ρ) {r c C t₀ : ℝ} (hr : 0 < r) (hC : 0 < C)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C) :
    ∃ K : Set (Pt X), IsCompact K ∧ ∃ β T : ℝ, 0 < β ∧ t₀ ≤ T ∧
      ∀ t, T ≤ t → ∀ z : ComplexVector n,
        ‖z‖ ≤ Real.exp (-β * ρ o t) → Φ t z ∈ K := by
  obtain ⟨B, hBo⟩ := exists_chartBall o
  have hoB : o ∈ B.inner := by simpa only [hBo] using B.center_mem_inner
  obtain ⟨δ, hδ, hδB⟩ := (X.metric.induced_distance_topology o B.inner).mp
    (B.isOpen_inner.mem_nhds hoB)
  let q := δ / 2
  have hq : 0 < q := half_pos hδ
  have hqδ : q < δ := by dsimp only [q]; linarith
  have hnear : ∀ y, inducedDistance X.metric.form o y ≤ q → y ∈ B.core :=
    fun y hy => B.inner_subset_core (hδB (lt_of_le_of_lt hy hqδ))
  obtain ⟨a, ha, T₁, hmetric⟩ := hwindow.2.2.2.2.2.2.1 B.core B.isCompact_core
  let s : ℝ → ℝ := fun t => ρ o t
  have hs : Tendsto s atTop atTop := hwindow.2.2.1
  have hball : Tendsto (fun t => Real.exp (-2 * s t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.const_mul_atTop (show (0 : ℝ) < 2 by norm_num) hs)
  have hdecay : Tendsto (fun t => Real.sqrt (2 * C) * Real.exp (-s t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hs).const_mul (Real.sqrt (2 * C))
  obtain ⟨T₂, hsmallBall⟩ := eventually_atTop.mp (hball.eventually (Iio_mem_nhds hr))
  obtain ⟨T₃, hsmallLength⟩ := eventually_atTop.mp (hdecay.eventually (Iio_mem_nhds hq))
  let T := max (max 0 t₀) (max T₁ (max T₂ T₃))
  have hT0 : 0 ≤ T := (le_max_left 0 t₀).trans (le_max_left _ _)
  have hTchart : t₀ ≤ T := (le_max_right 0 t₀).trans (le_max_left _ _)
  have hT₁ : T₁ ≤ T := (le_max_left T₁ (max T₂ T₃)).trans (le_max_right _ _)
  have hT₂ : T₂ ≤ T := (le_max_left T₂ T₃).trans
    ((le_max_right T₁ (max T₂ T₃)).trans (le_max_right _ _))
  have hT₃ : T₃ ≤ T := (le_max_right T₂ T₃).trans
    ((le_max_right T₁ (max T₂ T₃)).trans (le_max_right _ _))
  refine ⟨B.core, B.isCompact_core, 2, T, by norm_num, hTchart, ?_⟩
  intro t ht z hz
  change ‖z‖ ≤ Real.exp (-2 * s t) at hz
  have hzr : ‖z‖ < r := hz.trans_lt (hsmallBall t (hT₂.trans ht))
  have hshort : Real.exp (s t) * (Real.sqrt (2 * C) * ‖z‖) < q := by
    calc
      _ ≤ Real.exp (s t) * (Real.sqrt (2 * C) * Real.exp (-2 * s t)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)) (Real.exp_pos _).le
      _ = Real.sqrt (2 * C) * (Real.exp (s t) * Real.exp (-2 * s t)) := by ring
      _ = Real.sqrt (2 * C) * Real.exp (s t + -2 * s t) := by rw [Real.exp_add]
      _ = Real.sqrt (2 * C) * Real.exp (-s t) := by congr 1; congr 1; ring
      _ < q := hsmallLength t (hT₃.trans ht)
  exact image_mem_of_metric_lower X.metric (flow_metricSmooth hflow (hT0.trans ht))
    hC (hcharts t (hTchart.trans ht)) hq B.core hnear
    (fun y hy => (hmetric t (hT₁.trans ht) y hy).1) hzr hshort

end Yau.Proofs.C07TinyImageAux
