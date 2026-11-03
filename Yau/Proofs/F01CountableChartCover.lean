import Yau.Proofs.F01SpaceTimeChart
import Yau.Proofs.F01OrdinaryCharts

/-! Actual chart inverse images of compact coordinate balls admit a
countable open-ball subcover of the original manifold. No atlas is supplied
as an extra geometric hypothesis. -/
noncomputable section
open Set TopologicalSpace
open scoped Topology Manifold
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n)

theorem exists_countable_compact_chart_cover :
    ∃ (a : ℕ → M.Carrier) (r : ℕ → ℝ),
      (∀ j, 0 < r j ∧ Metric.closedBall (chartPt (a j) (a j)) (r j) ⊆ chartTarget (a j)) ∧
      (∀ j, IsCompact (chartInv (a j) '' Metric.closedBall (chartPt (a j) (a j)) (r j))) ∧
      ∀ x : M.Carrier, ∃ j, x ∈ chartInv (a j) '' Metric.ball (chartPt (a j) (a j)) (r j) := by
  classical
  have hlocal (x : M.Carrier) : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (chartPt x x) r ⊆ chartTarget x :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))
  choose r hr hclosed using hlocal
  let U : M.Carrier → Set M.Carrier := fun x => ordinaryChart x '' Metric.ball (chartPt x x) (r x)
  have hU (x : M.Carrier) : IsOpen (U x) :=
    (ordinaryChart x).isOpen_image_of_subset_source Metric.isOpen_ball
      (by rw [ordinaryChart_source]; exact Metric.ball_subset_closedBall.trans (hclosed x))
  have hxU (x : M.Carrier) : x ∈ U x := by
    refine ⟨chartPt x x, Metric.mem_ball_self (hr x), ?_⟩
    rw [ordinaryChart_apply]
    exact (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨a, (fun j => r (a j)), (fun j => ⟨hr (a j), hclosed (a j)⟩), ?_, ?_⟩
  · intro j
    have heq : chartInv (a j) = (ordinaryChart (a j) : ComplexVector n → M.Carrier) :=
      funext (fun z => (ordinaryChart_apply (a j) z).symm)
    rw [heq]
    exact (isCompact_closedBall (chartPt (a j) (a j)) (r (a j))).image_of_continuousOn
      ((ordinaryChart (a j)).continuousOn.mono
        (by rw [ordinaryChart_source]; exact hclosed (a j)))
  · intro x
    obtain ⟨j, hj⟩ := mem_iUnion.mp (ha (mem_univ x))
    obtain ⟨z, hz, hzx⟩ := hj
    exact ⟨j, z, hz, (ordinaryChart_apply (a j) z) ▸ hzx⟩

end Yau.NodeProofs.F01Aux
