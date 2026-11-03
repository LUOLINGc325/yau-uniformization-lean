import Yau.Proofs.C05GradientFlowContraction
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Compactness supplies chart neighborhoods of uniform metric size; contraction carries the whole trap into one. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem exists_uniform_convex_chart_cover (g : SmoothMetric M)
    (K : Set M.Carrier) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∃ c : M.Carrier, ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (chartPt c c) ε ⊆ chartTarget c ∧
      ∀ y, inducedDistance g.form x y < δ →
        y ∈ (chartAt (ComplexVector n) c).source ∧
          chartPt c y ∈ Metric.ball (chartPt c c) ε := by
  classical
  letI := inducedMetricSpace g
  have hchart : ∀ c : M.Carrier, ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (chartPt c c) ε ⊆ chartTarget c := by
    intro c
    exact Metric.mem_nhds_iff.mp
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds (mem_extChartAt_target c))
  choose ε hε hball using hchart
  let U := fun c : M.Carrier => (chartAt (ComplexVector n) c).source ∩
    chartPt c ⁻¹' Metric.ball (chartPt c c) (ε c)
  have hU : ∀ c, IsOpen (U c) := fun c =>
    isOpen_extChartAt_preimage (I := ComplexModel n) c Metric.isOpen_ball
  have hcover : K ⊆ ⋃ c, U c := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source _ _, by simpa using hε x⟩
  obtain ⟨δ, hδ, hδU⟩ := lebesgue_number_lemma_of_metric hK hU hcover
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  obtain ⟨c, hc⟩ := hδU x hx
  refine ⟨c, ε c, hε c, hball c, ?_⟩
  intro y hy
  apply hc
  change dist y x < δ
  rw [dist_comm]
  exact hy

theorem exists_time_carries_trap_into_convex_chart (g : SmoothMetric M)
    (o : M.Carrier) (a r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (F : ℝ → M.Carrier → M.Carrier)
    (hFK : ∀ t, 0 ≤ t → ∀ x ∈ gradientTrap g o r, F t x ∈ gradientTrap g o r)
    (hcontract : ∀ t, 0 ≤ t → ∀ x ∈ gradientTrap g o r, ∀ y ∈ gradientTrap g o r,
      inducedDistance g.form (F t x) (F t y) ≤ Real.exp (-a * t) * inducedDistance g.form x y) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ c : M.Carrier, ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (chartPt c c) ε ⊆ chartTarget c ∧
      ∀ x ∈ gradientTrap g o r, F T x ∈ (chartAt (ComplexVector n) c).source ∧
        chartPt c (F T x) ∈ Metric.ball (chartPt c c) ε := by
  obtain ⟨δ, hδ, hcharts⟩ := exists_uniform_convex_chart_cover g
    (gradientTrap g o r) (gradientTrap_isCompact g o r)
  have hlim : Tendsto (fun t : ℝ => Real.exp (-a * t) * (r / 2)) atTop (𝓝 0) := by
    simpa only [zero_mul, Function.comp_apply, id_eq] using (Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos ha)).mpr tendsto_id)).mul_const (r / 2)
  obtain ⟨T, hsmall, hT⟩ := ((hlim.eventually (gt_mem_nhds hδ)).and (eventually_ge_atTop 0)).exists
  have ho : o ∈ gradientTrap g o r := by
    change inducedDistance g.form o o ≤ r / 2
    rw [g.induced_distance_eq_zero.mpr rfl]
    positivity
  obtain ⟨c, ε, hε, hεball, hc⟩ := hcharts (F T o) (hFK T hT o ho)
  refine ⟨T, hT, c, ε, hε, hεball, ?_⟩
  intro x hx
  apply hc
  have H := hcontract T hT o ho x hx
  have hDx : inducedDistance g.form o x ≤ r / 2 := hx
  exact H.trans_lt ((mul_le_mul_of_nonneg_left hDx (Real.exp_pos _).le).trans_lt hsmall)

end Yau.Proofs.C05GradientFlowAux
