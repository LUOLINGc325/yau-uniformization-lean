import Yau.LeafProofs.L23FieldMetricNormalDistance

/-! A uniform metric neighborhood inside a joint endpoint chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem exists_uniform_normal_metric_ball
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (B₀ : Set (ComplexVector n)) (hB₀ : IsOpen B₀) (hcB₀ : chartPt c c ∈ B₀)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (he : (chartPt c c,chartPt c c) ∈ e.target) :
    ∃ (B : Set (ComplexVector n)) (δ : ℝ), IsOpen B ∧ chartPt c c ∈ B ∧
      B ⊆ B₀ ∧ B ⊆ chartTarget c ∧ 0 < δ ∧
      ∀ z ∈ B, ∀ y : M.Carrier, inducedDistance h (chartInv c z) y < δ →
        y ∈ (chartAt (ComplexVector n) c).source ∧ (z,chartPt c y) ∈ e.target := by
  letI := manifold_realSmooth M
  letI := metricSpaceOfField h hh
  have hchart : ContinuousAt (chartPt c) c :=
    (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := ∞) (x := c) (x' := c)
      (mem_chart_source _ _)).continuousAt
  have hF : ContinuousAt (fun p : M.Carrier × M.Carrier => (chartPt c p.1,chartPt c p.2)) (c,c) :=
    (hchart.comp continuousAt_fst).prodMk (hchart.comp continuousAt_snd)
  have hn : {p : M.Carrier × M.Carrier | p.2 ∈ (chartAt (ComplexVector n) c).source ∧
      (chartPt c p.1,chartPt c p.2) ∈ e.target} ∈ 𝓝 (c,c) :=
    inter_mem (continuousAt_snd.preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _)))
      (hF.preimage_mem_nhds (e.open_target.mem_nhds he))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hn
  let δ := r/4
  have hδ : 0 < δ := div_pos hr (by norm_num)
  let B := B₀ ∩ (chartTarget c ∩ (chartInv c) ⁻¹' Metric.ball c δ)
  have hInvC : ContinuousOn (chartInv c) (chartTarget c) :=
    continuousOn_extChartAt_symm (I := ComplexModel n) c
  have hB : IsOpen B := hB₀.inter (hInvC.isOpen_inter_preimage
    (isOpen_extChartAt_target (I := ComplexModel n) c) Metric.isOpen_ball)
  have hcInv : chartInv c (chartPt c c) = c :=
    (extChartAt (ComplexModel n) c).left_inv (mem_extChartAt_source c)
  have hcB : chartPt c c ∈ B := by
    refine ⟨hcB₀,mem_extChartAt_target c,?_⟩
    change chartInv c (chartPt c c) ∈ Metric.ball c δ
    rw [hcInv]
    exact Metric.mem_ball_self hδ
  refine ⟨B,δ,hB,hcB,(fun z hz => hz.1),(fun z hz => hz.2.1),hδ,?_⟩
  intro z hz y hy
  have hx : dist (chartInv c z) c < δ := hz.2.2
  have hyx : dist (chartInv c z) y < δ := hy
  have hyc : dist y c < r := by
    have H := dist_triangle y (chartInv c z) c
    rw [dist_comm y (chartInv c z)] at H
    dsimp only [δ] at hx hyx
    linarith
  have hp : (chartInv c z,y) ∈ Metric.ball (c,c) r := by
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt_iff.mpr ⟨hx.trans (by dsimp [δ]; linarith),hyc⟩
  have H := hrsub hp
  have hinv : chartPt c (chartInv c z) = z := (extChartAt (ComplexModel n) c).right_inv hz.2.1
  change y ∈ (chartAt (ComplexVector n) c).source ∧
    (chartPt c (chartInv c z),chartPt c y) ∈ e.target at H
  rwa [hinv] at H

theorem chartVectorNorm_le_opNorm_add_one (h : HermitianField M) (c : M.Carrier)
    (z v : ComplexVector n) : chartVectorNorm h c z v ≤ (‖realMetricInChart h c z‖+1)*‖v‖ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (by positivity) (norm_nonneg _),?_⟩
  have H : realMetricInChart h c z v v ≤ ‖realMetricInChart h c z‖*‖v‖^2 := by
    calc
      _ ≤ |realMetricInChart h c z v v| := le_abs_self _
      _ ≤ ‖realMetricInChart h c z v‖*‖v‖ := (realMetricInChart h c z v).le_opNorm v
      _ ≤ (‖realMetricInChart h c z‖*‖v‖)*‖v‖ :=
        mul_le_mul_of_nonneg_right ((realMetricInChart h c z).le_opNorm v) (norm_nonneg _)
      _ = _ := by ring
  have Hcoef : ‖realMetricInChart h c z‖ ≤ (‖realMetricInChart h c z‖+1)^2 := by
    nlinarith [norm_nonneg (realMetricInChart h c z),sq_nonneg ‖realMetricInChart h c z‖]
  have Hmul := mul_le_mul_of_nonneg_right Hcoef (sq_nonneg ‖v‖)
  nlinarith only [H,Hmul]

end Yau.LeafProofs.L23Aux
