import Yau.Proofs.P02ChartSupport

noncomputable section
open Filter Metric
open scoped Topology ContDiff

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_chart_metric_lower_ball (g : SmoothMetric M) (p : M.Carrier) :
    ∃ r m : ℝ, 0 < r ∧ 0 < m ∧
      closedBall (chartPt p p) r ⊆ chartTarget p ∧
      ∀ z ∈ closedBall (chartPt p p) r, ∀ v : ComplexVector n,
        m*‖v‖^2 ≤ realMetricInChart g.form p z v v := by
  let zp := chartPt p p
  let G := realMetricInChart g.form p
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) p).mem_nhds (mem_extChartAt_target p))
  let r := ρ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrtarget : closedBall zp r ⊆ chartTarget p := by
    intro z hz
    apply hball
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by dsimp [r]; linarith)
  let S : Set (ComplexVector n × ComplexVector n) := closedBall zp r ×ˢ sphere 0 1
  have hS : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hFc : ContinuousOn (fun q : ComplexVector n × ComplexVector n => G q.1 q.2 q.2) S := by
    have HG : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ComplexVector n => G q.1)
        (chartTarget p ×ˢ Set.univ) :=
      (realMetricInChart_smooth g p).comp contDiffOn_fst (fun q hq => hq.1)
    have HF := (HG.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd
    exact HF.continuousOn.mono (fun q hq => ⟨hrtarget hq.1,Set.mem_univ _⟩)
  have hpos (q : ComplexVector n × ComplexVector n) (hq : q ∈ S) : 0 < G q.1 q.2 q.2 := by
    have hn : ‖q.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hq.2
    have hv : q.2 ≠ 0 := by intro he; rw [he,norm_zero] at hn; norm_num at hn
    have hz := hrtarget hq.1
    have hy : chartInv p q.1 ∈ (chartAt (ComplexVector n) p).source := by
      simpa only [extChartAt_source,chartInv] using (extChartAt (ComplexModel n) p).map_target hz
    have hpt : chartPt p (chartInv p q.1) = q.1 := (extChartAt (ComplexModel n) p).right_inv hz
    have hne : G q.1 q.2 q.2 ≠ 0 := by
      intro he
      apply hv
      apply (realMetricInChart_quadratic_eq_zero_iff g.form p (chartInv p q.1) hy q.2).mp
      rw [hpt]
      exact he
    exact lt_of_le_of_ne (realMetricInChart_quadratic_nonneg g.form p q.1 q.2) hne.symm
  obtain ⟨m,hm,hmin⟩ := hS.exists_forall_le' hFc hpos
  refine ⟨r,m,hr,hm,hrtarget,?_⟩
  intro z hz v
  by_cases hv : v=0
  · subst v
    simp
  have hnorm : (‖v‖⁻¹ : ℝ) • v ∈ sphere (0 : ComplexVector n) 1 := by
    rw [mem_sphere,dist_zero_right]
    exact norm_smul_inv_norm (𝕜 := ℝ) hv
  have H := hmin (z,(‖v‖⁻¹ : ℝ) • v) ⟨hz,hnorm⟩
  change m ≤ G z ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at H
  simp only [map_smul,smul_apply,smul_eq_mul] at H
  calc
    _ ≤ (‖v‖⁻¹*(‖v‖⁻¹*G z v v))*‖v‖^2 :=
      mul_le_mul_of_nonneg_right H (sq_nonneg _)
    _ = _ := by
      change (‖v‖⁻¹*(‖v‖⁻¹*G z v v))*‖v‖^2 = G z v v
      field_simp

end Yau.NodeProofs.P02Aux
