import Yau.LeafProofs.L17UniformPartitionBudget

/-! The actual locally finite normalizing sum has the fixed overlap bound. -/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem UniformChartPartition.chartWeightSum_le_overlapBudget
    (P : UniformChartPartition g) (x : M.Carrier) :
    chartWeightSum P.charts P.centers P.radius P.radius_pos x ≤ (P.overlapBudget : ℝ) := by
  classical
  obtain ⟨V, hV, hI, hcard⟩ := P.overlap x
  let I : Set P.centers :=
    {p | ((P.charts.chart p '' closedBall 0 P.radius) ∩ V).Nonempty}
  have hIF : I.Finite := by convert! hI using 1
  have hIcard : Nat.card I ≤ P.overlapBudget := by convert! hcard using 1
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hsupp : Function.support (fun p : P.centers =>
      chartWeight (P.charts.chart p) P.radius P.radius_pos x) ⊆ I := by
    intro p hp
    have hts : x ∈ tsupport (chartWeight (P.charts.chart p) P.radius P.radius_pos) :=
      subset_closure hp
    have himage := (P.charts.chartWeight_properties p P.radius_pos P.radius_lt).2.2 hts
    refine ⟨x, ?_, hxV⟩
    apply image_mono _ himage
    intro z hz
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (by have := P.radius_pos; linarith))
  have hsuppfin : Function.support (fun p : P.centers =>
      chartWeight (P.charts.chart p) P.radius P.radius_pos x) ⊆ (hIF.toFinset : Set P.centers) := by
    intro p hp
    exact hIF.mem_toFinset.mpr (hsupp hp)
  rw [chartWeightSum, finsum_eq_sum_of_support_subset _ hsuppfin]
  calc
    _ ≤ ∑ _p ∈ hIF.toFinset, (1 : ℝ) := Finset.sum_le_sum fun p hp =>
      (chartWeight_mem_Icc (P.charts.chart p) P.radius_pos x).2
    _ = (hIF.toFinset.card : ℝ) := by simp
    _ = (Nat.card I : ℝ) := by rw [← Nat.card_eq_card_finite_toFinset hIF]
    _ ≤ (P.overlapBudget : ℝ) := by exact_mod_cast hIcard

end Yau.LeafProofs.L17Aux
