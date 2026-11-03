import Yau.Proofs.F01CountableChartCover
import Yau.Proofs.F01ClosedSlabSmoothness
import Yau.Proofs.F01SpaceTimeSmoothCover

/-! A countable compact coordinate atlas is constructed from the actual
manifold before the function. Joint smoothness on its closed cylinders
then implies the original SmoothSpaceTime on all nonnegative times. -/
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n)

theorem exists_countable_smoothness_atlas :
    ∃ (a : ℕ → M.Carrier) (r : ℕ → ℝ),
      (∀ j, 0 < r j ∧ Metric.closedBall (chartPt (a j) (a j)) (r j) ⊆ chartTarget (a j)) ∧
      (∀ j, IsCompact (chartInv (a j) '' Metric.closedBall (chartPt (a j) (a j)) (r j))) ∧
      (∀ x : M.Carrier, ∃ j, x ∈ chartInv (a j) '' Metric.ball (chartPt (a j) (a j)) (r j)) ∧
      ∀ F : M.Carrier → ℝ → ℝ,
        (∀ j k : ℕ, ContDiffOn ℝ ∞
          (fun p : ComplexVector n × ℝ => F (chartInv (a j) p.1) p.2)
          (Metric.closedBall (chartPt (a j) (a j)) (r j) ×ˢ Icc 0 ((k : ℝ) + 1))) →
        SmoothSpaceTime F (Ici 0) := by
  obtain ⟨a, r, hclosed, hcompact, hcover⟩ := exists_countable_compact_chart_cover M
  refine ⟨a, r, hclosed, hcompact, hcover, ?_⟩
  intro F hF
  apply smoothSpaceTime_of_holomorphic_cover F (Ici 0)
    (fun j => ordinaryChart (a j))
    (fun j => (ordinaryChart_inverse_contMDiffOn (a j)).mdifferentiableOn (by simp))
    (fun j => Metric.ball (chartPt (a j) (a j)) (r j))
    (fun j => Metric.isOpen_ball)
  · intro j
    rw [ordinaryChart_source]
    exact Metric.ball_subset_closedBall.trans (hclosed j).2
  · intro y
    obtain ⟨j, w, hw, hwy⟩ := hcover y
    exact ⟨j, w, hw, (ordinaryChart_apply (a j) w).trans hwy⟩
  · intro j
    apply contDiffOn_nonnegative_time_of_closed_slabs
    intro k
    simpa only [ordinaryChart_apply] using
      (hF j k).mono (prod_mono Metric.ball_subset_closedBall Subset.rfl)

end Yau.NodeProofs.F01Aux
