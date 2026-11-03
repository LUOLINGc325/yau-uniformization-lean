import Yau.Proofs.F01CountableChartCover

/-! The actual countable original atlas is chosen with a fixed spatial
buffer before the approximants. The small balls still cover the manifold;
their sixty-fourfold closed balls remain in the original chart. -/
noncomputable section
open Set TopologicalSpace
open scoped Topology Manifold
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n)

theorem exists_buffered_countable_original_atlas :
    ∃ (a : ℕ → M.Carrier) (r : ℕ → ℝ),
      (∀ j, 0 < r j ∧ 64 * r j ≤ 1 ∧
        Metric.closedBall (chartPt (a j) (a j)) (64 * r j) ⊆ chartTarget (a j)) ∧
      (∀ j, IsCompact (chartInv (a j) ''
        Metric.closedBall (chartPt (a j) (a j)) (64 * r j))) ∧
      ∀ x : M.Carrier, ∃ j,
        x ∈ chartInv (a j) '' Metric.ball (chartPt (a j) (a j)) (r j) := by
  classical
  have hlocal (x : M.Carrier) : ∃ r : ℝ, 0 < r ∧ 64 * r ≤ 1 ∧
      Metric.closedBall (chartPt x x) (64 * r) ⊆ chartTarget x := by
    obtain ⟨ε, hε, hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))
    let r : ℝ := min (ε / 64) (1 / 64)
    have hr : 0 < r := lt_min (by positivity) (by norm_num)
    have hsmall : r ≤ 1 / 64 := min_le_right _ _
    have hlarge : r ≤ ε / 64 := min_le_left _ _
    exact ⟨r, hr, by linarith, (Metric.closedBall_subset_closedBall (by linarith)).trans hclosed⟩
  choose r hr hsmall hclosed using hlocal
  let U : M.Carrier → Set M.Carrier :=
    fun x => ordinaryChart x '' Metric.ball (chartPt x x) (r x)
  have hsub (x : M.Carrier) : Metric.closedBall (chartPt x x) (r x) ⊆ chartTarget x :=
    (Metric.closedBall_subset_closedBall (by linarith [hr x])).trans (hclosed x)
  have hU (x : M.Carrier) : IsOpen (U x) :=
    (ordinaryChart x).isOpen_image_of_subset_source Metric.isOpen_ball
      (by rw [ordinaryChart_source]; exact Metric.ball_subset_closedBall.trans (hsub x))
  have hxU (x : M.Carrier) : x ∈ U x := by
    refine ⟨chartPt x x, Metric.mem_ball_self (hr x), ?_⟩
    rw [ordinaryChart_apply]
    exact (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨a, (fun j => r (a j)), (fun j => ⟨hr (a j), hsmall (a j), hclosed (a j)⟩), ?_, ?_⟩
  · intro j
    have heq : chartInv (a j) = (ordinaryChart (a j) : ComplexVector n → M.Carrier) :=
      funext (fun z => (ordinaryChart_apply (a j) z).symm)
    rw [heq]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      ((ordinaryChart (a j)).continuousOn.mono
        (by rw [ordinaryChart_source]; exact hclosed (a j)))
  · intro x
    obtain ⟨j, hj⟩ := mem_iUnion.mp (ha (mem_univ x))
    obtain ⟨z, hz, hzx⟩ := hj
    exact ⟨j, z, hz, (ordinaryChart_apply (a j) z) ▸ hzx⟩

end Yau.NodeProofs.F01Aux
