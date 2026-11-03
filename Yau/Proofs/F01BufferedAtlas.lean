import Yau.Proofs.F01OpenCharts

/-! Finite buffered ordinary holomorphic charts on a compact set. Radius
choices are actual coordinate balls, made before choosing a chart for a point. -/
open Set
open scoped Manifold Topology
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n)

theorem exists_chart_buffer (p : M.Carrier) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (chartPt p p) (4 * r) ⊆ chartTarget p := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) p).mem_nhds (mem_extChartAt_target p))
  refine ⟨ε / 8, by positivity, ?_⟩
  intro z hz
  apply hball
  exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))

theorem finite_buffered_chart_cover {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ (r : M.Carrier → ℝ) (c : Finset M.Carrier),
      (∀ p, 0 < r p ∧ Metric.closedBall (chartPt p p) (4 * r p) ⊆ chartTarget p) ∧
      K ⊆ ⋃ p ∈ c, (chartAt (ComplexVector n) p).symm '' Metric.ball (chartPt p p) (r p) := by
  classical
  choose r hr hbuffer using exists_chart_buffer M
  let U : M.Carrier → Set M.Carrier := fun p =>
    (chartAt (ComplexVector n) p).symm '' Metric.ball (chartPt p p) (r p)
  have hball (p : M.Carrier) : Metric.ball (chartPt p p) (r p) ⊆
      (chartAt (ComplexVector n) p).target := by
    have hsub : Metric.ball (chartPt p p) (r p) ⊆ chartTarget p := by
      intro z hz
      apply hbuffer p
      exact Metric.mem_closedBall.mpr
        (le_trans (Metric.mem_ball.mp hz).le (by linarith [hr p]))
    simpa only [chartTarget, extChartAt, complex_extend_eq] using hsub
  have hopen (p : M.Carrier) : IsOpen (U p) :=
    (chartAt (ComplexVector n) p).isOpen_image_symm_of_subset_target Metric.isOpen_ball (hball p)
  have hmem (p : M.Carrier) : p ∈ U p :=
    ⟨chartPt p p, Metric.mem_ball_self (hr p),
      (chartAt (ComplexVector n) p).left_inv (mem_chart_source (ComplexVector n) p)⟩
  obtain ⟨c, hc⟩ := hK.elim_finite_subcover U hopen
    (fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩)
  exact ⟨r, c, fun p => ⟨hr p, hbuffer p⟩, hc⟩

end Yau.NodeProofs.F01Aux
