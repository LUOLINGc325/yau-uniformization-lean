import Yau.LeafProofs.L17PartitionSumJets

/-! The normalizing sum and its inverse have uniform jets before the scale is selected. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def PartitionBudgetFamily (A : BoundedChartFamily g) (N : ℕ) : Type _ :=
  {P : UniformChartPartition g // P.charts = A ∧ P.radius ≤ 1 ∧
    2 * P.radius < A.radius ∧ P.overlapBudget ≤ N}

abbrev PartitionBudgetIndex (A : BoundedChartFamily g) (N : ℕ) :=
  PartitionBudgetFamily A N × M.Carrier

def partitionScaledSum (A : BoundedChartFamily g) (N : ℕ) (i : PartitionBudgetIndex A N)
    (z : ComplexVector n) : ℝ :=
  chartWeightSum i.1.val.charts i.1.val.centers i.1.val.radius i.1.val.radius_pos
    (i.1.val.charts.chart i.2 (i.1.val.radius • z))

theorem partitionScaledSum_smooth (A : BoundedChartFamily g) (N : ℕ)
    (i : PartitionBudgetIndex A N) :
    ContDiffOn ℝ ∞ (partitionScaledSum A N i) (ball (0 : ComplexVector n) 2) :=
  smoothFn_comp_scaledChart_contDiffOn i.1.val.charts i.1.val.chartWeightSum_smoothFn
    i.1.val.radius_pos (by simpa only [i.1.property.1] using i.1.property.2.2.1) i.2

theorem partitionScaledSum_mem_Icc (A : BoundedChartFamily g) (N : ℕ)
    (i : PartitionBudgetIndex A N) (z : ComplexVector n) :
    partitionScaledSum A N i z ∈ Icc (1 : ℝ) N := by
  let P := i.1.val
  constructor
  · exact P.charts.one_le_chartWeightSum P.centers P.radius_pos P.radius_lt P.covers
      P.locallyFinite _
  · exact (P.chartWeightSum_le_overlapBudget _).trans (by exact_mod_cast i.1.property.2.2.2)

theorem partitionScaledSum_uniformJetBounds (A : BoundedChartFamily g) (N k : ℕ) :
    UniformJetBounds k (partitionScaledSum A N) (fun _ => ball (0 : ComplexVector n) 2) := by
  apply UniformJetBounds.of_orderBounds
  intro j hj
  obtain ⟨C, hC, hc⟩ := A.scaled_chartWeightSum_jet_bound j
  refine ⟨(N : ℝ) * C, ?_⟩
  intro i z hz
  have hsum := hc i.1.val i.1.property.1 i.1.property.2.1 i.1.property.2.2.1 i.2 z hz
  exact hsum.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast i.1.property.2.2.2) hC.le)

theorem partitionScaledSum_inverse_smooth (A : BoundedChartFamily g) (N : ℕ)
    (i : PartitionBudgetIndex A N) :
    ContDiffOn ℝ ∞ (fun z => (partitionScaledSum A N i z)⁻¹)
      (ball (0 : ComplexVector n) 2) :=
  (partitionScaledSum_smooth A N i).inv (fun z _ =>
    (zero_lt_one.trans_le (partitionScaledSum_mem_Icc A N i z).1).ne')

theorem partitionScaledSum_inverse_uniformJetBounds (A : BoundedChartFamily g) (N k : ℕ) :
    UniformJetBounds k (fun i z => (partitionScaledSum A N i z)⁻¹)
      (fun _ => ball (0 : ComplexVector n) 2) := by
  have hi : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) (Ioi 0) :=
    contDiffOn_id.inv (fun _ hx => (ne_of_gt hx))
  have hKU : Icc (1 : ℝ) N ⊆ Ioi (0 : ℝ) := fun _ hx => zero_lt_one.trans_le hx.1
  obtain ⟨V, hVo, hKV, hVU, hVjets⟩ :=
    compact_buffer_uniformJetBounds (ι := PartitionBudgetIndex A N)
      isCompact_Icc isOpen_Ioi hKU hi
  have hmap (i : PartitionBudgetIndex A N) : MapsTo (partitionScaledSum A N i)
      (ball (0 : ComplexVector n) 2) V := fun z _ => hKV (partitionScaledSum_mem_Icc A N i z)
  exact (partitionScaledSum_uniformJetBounds A N k).comp (hVjets k) (fun _ => isOpen_ball)
    (fun _ => hVo) (partitionScaledSum_smooth A N)
    (fun _ => hi.mono (subset_closure.trans hVU)) hmap

end Yau.LeafProofs.L17Aux
