import Yau.LeafProofs.L23FieldMetricNormalDistanceSmooth

/-! A genuine joint endpoint chart contains a product of open manifold neighborhoods. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem exists_open_chart_pair_neighborhood
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (O : Set M.Carrier) (hO : IsOpen O) (hcO : c ∈ O)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (he : (chartPt c c,chartPt c c) ∈ e.target) :
    ∃ U : Set M.Carrier, IsOpen U ∧ c ∈ U ∧ U ⊆ O ∧
      U ⊆ (chartAt (ComplexVector n) c).source ∧
      ∀ x ∈ U, ∀ y ∈ U, (chartPt c x,chartPt c y) ∈ e.target := by
  letI := manifold_realSmooth M
  letI := metricSpaceOfField h hh
  have hchart : ContinuousAt (chartPt c) c :=
    (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (x := c) (x' := c) (mem_chart_source _ _)).continuousAt
  have hF : ContinuousAt (fun p : M.Carrier × M.Carrier => (chartPt c p.1,chartPt c p.2)) (c,c) :=
    (hchart.comp continuousAt_fst).prodMk (hchart.comp continuousAt_snd)
  have hsource : (chartAt (ComplexVector n) c).source ∈ 𝓝 c :=
    (chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _)
  have hn : {p : M.Carrier × M.Carrier | p.1 ∈ O ∧ p.2 ∈ O ∧
      p.1 ∈ (chartAt (ComplexVector n) c).source ∧ p.2 ∈ (chartAt (ComplexVector n) c).source ∧
      (chartPt c p.1,chartPt c p.2) ∈ e.target} ∈ 𝓝 (c,c) := by
    exact inter_mem (continuousAt_fst.preimage_mem_nhds (hO.mem_nhds hcO))
      (inter_mem (continuousAt_snd.preimage_mem_nhds (hO.mem_nhds hcO))
        (inter_mem (continuousAt_fst.preimage_mem_nhds hsource)
          (inter_mem (continuousAt_snd.preimage_mem_nhds hsource)
            (hF.preimage_mem_nhds (e.open_target.mem_nhds he)))))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hn
  let U := Metric.ball c (r/2)
  have hsub (x y : M.Carrier) (hx : x ∈ U) (hy : y ∈ U) :
      x ∈ O ∧ y ∈ O ∧ x ∈ (chartAt (ComplexVector n) c).source ∧
        y ∈ (chartAt (ComplexVector n) c).source ∧ (chartPt c x,chartPt c y) ∈ e.target := by
    have hp : (x,y) ∈ Metric.ball (c,c) r := by
      rw [Metric.mem_ball,Prod.dist_eq]
      exact max_lt_iff.mpr ⟨hx.trans (half_lt_self hr),hy.trans (half_lt_self hr)⟩
    exact hrsub hp
  exact ⟨U,Metric.isOpen_ball,Metric.mem_ball_self (half_pos hr),
    (fun x hx => (hsub x x hx hx).1),(fun x hx => (hsub x x hx hx).2.2.1),
    (fun x hx y hy => (hsub x y hx hy).2.2.2.2)⟩

end Yau.LeafProofs.L23Aux
